"""
月絶天葬数 第5節の補題用：純粋な {∈,=} 一階式 Big_j(x) を生成し、
整形性・自由変数・記号数を機械的に確認する。

Big_j(x) は「x は自然数であり、V_j と等濃である」を表す。
M = V_{κ+1} において x = |V_j| を一意に定める。

記号：x  '  ¬  ∧  ∀  ∈  =  (  )
変数 k 番は "x" + "′" * k（′ は本文第 2 節のプライム記号 U+2032）。
原子式は (u∈v), (u=v)。¬φ, (φ∧ψ), ∀u φ。
"""

import sys

# ---------- 基本構文（AST） ----------

class F:
    pass

class Atom(F):
    def __init__(s, op, a, b): s.op, s.a, s.b = op, a, b
class Not(F):
    def __init__(s, p): s.p = p
class And(F):
    def __init__(s, p, q): s.p, s.q = p, q
class All(F):
    def __init__(s, v, p): s.v, s.p = v, p

def In(a, b): return Atom('∈', a, b)
def Eq(a, b): return Atom('=', a, b)

# 略記（すべて原始記号へ展開される）
def Or(p, q):  return Not(And(Not(p), Not(q)))
def Imp(p, q): return Not(And(p, Not(q)))
def Iff(p, q): return And(Imp(p, q), Imp(q, p))
def Ex(v, p):  return Not(All(v, Not(p)))
def AllIn(v, a, p): return All(v, Imp(In(v, a), p))      # ∀v∈a p
def ExIn(v, a, p):  return Ex(v, And(In(v, a), p))        # ∃v∈a p

def conj(*ps):
    r = ps[0]
    for p in ps[1:]:
        r = And(r, p)
    return r

# ---------- 描画・計数・検査 ----------

def var(k): return "x" + "′" * k

def render(f):
    if isinstance(f, Atom): return "(" + var(f.a) + f.op + var(f.b) + ")"
    if isinstance(f, Not):  return "¬" + render(f.p)
    if isinstance(f, And):  return "(" + render(f.p) + "∧" + render(f.q) + ")"
    if isinstance(f, All):  return "∀" + var(f.v) + render(f.p)
    raise TypeError

def length(f):
    """記号数を再帰で直接数える（文字列を作らずに済むよう別実装）。"""
    if isinstance(f, Atom): return 3 + (1 + f.a) + (1 + f.b)   # ( u op v ) : '(' op ')' の3 + 変数2つ
    if isinstance(f, Not):  return 1 + length(f.p)
    if isinstance(f, And):  return 3 + length(f.p) + length(f.q)
    if isinstance(f, All):  return 1 + (1 + f.v) + length(f.p)
    raise TypeError

def free(f):
    if isinstance(f, Atom): return {f.a, f.b}
    if isinstance(f, Not):  return free(f.p)
    if isinstance(f, And):  return free(f.p) | free(f.q)
    if isinstance(f, All):  return free(f.p) - {f.v}
    raise TypeError

ALPHABET = set("x′¬∧∀∈=()")

# ---------- 部品 ----------
# 変数番号の割当て（衝突しないよう用途ごとに固定）
X  = 0          # 定義される自然数（唯一の自由変数）
V1, V2 = 1, 2   # V_j の鎖で交互に使う
Z, U = 3, 4     # 部分集合・推移性などの内部変数
W = 5           # 後者判定の内部変数
G = 6           # 全単射
P, Q = 7, 8     # 順序対
A1, B1, B2 = 9, 10, 11   # 対の成分
S, T = 12, 13   # 対の内部（{a},{a,b} の判定）
E = 14          # 空集合判定の内部変数

def hygienic(args, bound):
    """部品の引数が、その部品の内部で束縛する変数と重ならないことを確認する（変数捕獲の防止）。"""
    clash = set(args) & set(bound)
    assert not clash, f"変数捕獲: 引数 {args} と束縛変数 {bound} が {clash} で重なる"

def Empty(a):            # a = ∅
    hygienic([a], [E])
    return All(E, Not(In(E, a)))

def Trans(a):            # a は推移的
    hygienic([a], [Z, U])
    return AllIn(Z, a, AllIn(U, Z, In(U, a)))

def Succ(z):             # z は後者：∃w∈z ∀u (u∈z ↔ (u∈w ∨ u=w))
    hygienic([z], [W, U])
    return ExIn(W, z, All(U, Iff(In(U, z), Or(In(U, W), Eq(U, W)))))

def Nat(a):
    # a は推移的、a の元はすべて推移的（基礎の公理の下で a は順序数）、
    # a 以下の順序数はすべて 0 か後者（よって a は自然数）
    hygienic([a], [Z, U, W])
    return conj(
        Trans(a),
        AllIn(Z, a, AllIn(U, Z, AllIn(W, U, In(W, Z)))),   # ∀z∈a, z は推移的
        All(Z, Imp(Or(In(Z, a), Eq(Z, a)), Or(Empty(Z), Succ(Z)))),
    )

def PowerOf(a, b):       # a = P(b)：∀z (z∈a ↔ ∀u (u∈z → u∈b))
    hygienic([a, b], [Z, U])
    return All(Z, Iff(In(Z, a), All(U, Imp(In(U, Z), In(U, b)))))

def Chain(v, j, other):
    """v = V_j。v と other を交互に使う。"""
    if j == 0:
        return Empty(v)
    hygienic([v], [other])
    return Ex(other, And(PowerOf(v, other), Chain(other, j - 1, v)))

def Pair(p, a, b):
    # p = {{a},{a,b}}：∀s (s∈p ↔ (∀t(t∈s↔t=a) ∨ ∀t(t∈s↔(t=a ∨ t=b))))
    hygienic([p, a, b], [S, T])
    sing = All(T, Iff(In(T, S), Eq(T, a)))
    dbl  = All(T, Iff(In(T, S), Or(Eq(T, a), Eq(T, b))))
    return All(S, Iff(In(S, p), Or(sing, dbl)))

def Equi(a, b):
    """a と b の間に全単射 g が存在する（g は順序対の集合）。"""
    hygienic([a, b], [G, P, Q, A1, B1, B2])
    elems  = AllIn(P, G, ExIn(A1, a, ExIn(B1, b, Pair(P, A1, B1))))
    total  = AllIn(A1, a, ExIn(B1, b, ExIn(P, G, Pair(P, A1, B1))))
    onto   = AllIn(B1, b, ExIn(A1, a, ExIn(P, G, Pair(P, A1, B1))))
    # 関数性：(a1,b1),(a1,b2) ∈ g ならば b1 = b2（成分は a, b に属するものに限ってよい）
    func   = AllIn(P, G, AllIn(Q, G, AllIn(A1, a, AllIn(B1, b, AllIn(B2, b,
                 Imp(And(Pair(P, A1, B1), Pair(Q, A1, B2)), Eq(B1, B2)))))))
    # 単射性：(a1,b1),(a2,b1) ∈ g ならば a1 = a2（a2 として B2 番の変数を流用）
    inj    = AllIn(P, G, AllIn(Q, G, AllIn(A1, a, AllIn(B1, b, AllIn(B2, a,
                 Imp(And(Pair(P, A1, B1), Pair(Q, B2, B1)), Eq(A1, B2)))))))
    return Ex(G, conj(elems, total, onto, func, inj))

def Big(j):
    """Big_j(x) ≡ Nat(x) ∧ ∃v (v = V_j ∧ Equi(x, v))"""
    return And(Nat(X), Ex(V1, And(Chain(V1, j, V2), Equi(X, V1))))

# ---------- 実行 ----------

if __name__ == "__main__":
    rows = []
    for j in range(0, 13):
        f = Big(j)
        s = render(f)
        n = length(f)
        assert len(s) == n, (j, len(s), n)            # 2通りの数え方が一致
        assert set(s) <= ALPHABET, set(s) - ALPHABET  # アルファベット外の記号なし
        assert free(f) == {X}, free(f)                # 自由変数は x のみ
        rows.append((j, n))
    # V_j の鎖は変数 x' と x'' を交互に使うので、1段あたりの増分は偶奇で2通り。
    # 増分の最大値 B を取れば |Big_j| ≤ A + B j が全 j で成り立つことを確認する。
    A = rows[0][1]
    steps = sorted({rows[k + 1][1] - rows[k][1] for k in range(len(rows) - 1)})
    B = max(steps)
    for j, n in rows:
        assert n <= A + B * j, (j, n, A, B)
    print("A =", A, " 1段あたりの増分 =", steps, " → B =", B)
    for j, n in rows:
        print(f"j={j:2d}  |Big_j| = {n}   (上限 A+Bj = {A + B * j})")
    if len(sys.argv) > 1:
        print()
        print(render(Big(int(sys.argv[1]))))
