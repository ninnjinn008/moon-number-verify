"""
算術の層：M = V_{κ+1} の中で自然数の演算・素数・Encode を表す式。

各関数は (ctx, 変数番号…) を受け取り、構文木を返す。束縛変数はすべて ctx.fresh() で新しく取る。
ctx.use_oracle(名前) が真なら、その関係を Oracle（テスト用の代用）に差し替える。

再帰的に定まる値は「有限な計算表の存在」で表す。計算表は遺伝的有限集合なので M に属し、
表の各行が正しい値をもつことは再帰の順序に関する帰納法で保証される。
"""
from fol import (Atom, Not, And, All, Oracle, In, Eq, Or, Imp, Iff, Ex,
                 AllIn, ExIn, conj, disj)

# ---------- 基本 ----------

def empty(ctx, a):
    if ctx.use_oracle("empty"):
        return Oracle("empty", [a])
    e = ctx.fresh()
    return All(e, Not(In(e, a)))

def succ_of(ctx, b, c):               # c = b ∪ {b}
    if ctx.use_oracle("succ"):
        return Oracle("succ", [b, c])
    u = ctx.fresh()
    return All(u, Iff(In(u, c), Or(In(u, b), Eq(u, b))))

def numeral(ctx, v, k):               # v = k
    if ctx.use_oracle("numeral"):
        return Oracle(f"numeral:{k}", [v])
    if k == 0:
        return empty(ctx, v)
    w = ctx.fresh()
    return ExIn(w, v, And(succ_of(ctx, w, v), numeral(ctx, w, k - 1)))

def trans(ctx, a):
    z, u = ctx.fresh(2)
    return AllIn(z, a, AllIn(u, z, In(u, a)))

def nat(ctx, a):                      # a は自然数
    if ctx.use_oracle("nat"):
        return Oracle("nat", [a])
    z, u, w, w2 = ctx.fresh(4)
    is_succ = ExIn(w2, z, succ_of(ctx, w2, z))
    return conj(
        trans(ctx, a),
        AllIn(z, a, AllIn(u, z, AllIn(w, u, In(w, z)))),
        All(z, Imp(Or(In(z, a), Eq(z, a)), Or(empty(ctx, z), is_succ))),
    )

def pair(ctx, p, a, b):               # p = {{a},{a,b}}
    """Δ0 式（量化子はすべて有界）。推移的な M のどの元 p, a, b についても絶対的。
    改訂28 までは ∀s (s ∈ p ↔ s = {a} ∨ s = {a,b}) という有界でない形で、M が {a} や {a,b} を
    含まないとき（a, b の階数が κ のとき）に偽の陽性が生じた（別の AI による審査で指摘された）。"""
    if ctx.use_oracle("pair"):
        return Oracle("pair", [p, a, b])
    s, t = ctx.fresh(2)
    sing = And(In(a, s), AllIn(t, s, Eq(t, a)))                              # s = {a}
    dbl = conj(In(a, s), In(b, s), AllIn(t, s, Or(Eq(t, a), Eq(t, b))))      # s = {a, b}
    return conj(AllIn(s, p, Or(sing, dbl)), ExIn(s, p, sing), ExIn(s, p, dbl))

def pair_old(ctx, p, a, b):           # 改訂28 までの形（回帰テスト用）
    s, t = ctx.fresh(2)
    sing = All(t, Iff(In(t, s), Eq(t, a)))
    dbl = All(t, Iff(In(t, s), Or(Eq(t, a), Eq(t, b))))
    return All(s, Iff(In(s, p), Or(sing, dbl)))

def pair_parts(ctx, q, body):
    """q が順序対 (i, a) のとき、その成分 i, a を有界量化で取り出して body(i, a) を述べる：
       ∃r∈q ∃i∈r ∃a∈r (pair(q,i,a) ∧ body(i,a))"""
    r, i, a = ctx.fresh(3)
    return ExIn(r, q, ExIn(i, r, ExIn(a, r, And(pair(ctx, q, i, a), body(i, a)))))

def all_pairs(ctx, t, body):
    """t の元で順序対 (i, a) であるものすべてについて body(q, i, a)：
       ∀q∈t ∀r∈q ∀i∈r ∀a∈r (pair(q,i,a) → body(q,i,a))"""
    q, r, i, a = ctx.fresh(4)
    return AllIn(q, t, AllIn(r, q, AllIn(i, r, AllIn(a, r,
           Imp(pair(ctx, q, i, a), body(q, i, a))))))

def lookup(ctx, t, i, body):
    """t に順序対 (i, a) があり body(a) が成り立つ：∃q∈t (… pair(q,i,a) ∧ body(a))"""
    q, r, a = ctx.fresh(3)
    return ExIn(q, t, ExIn(r, q, ExIn(a, r, And(pair(ctx, q, i, a), body(a)))))

def triple(ctx, p, n, b, v):          # p = ((n, b), v)
    if ctx.use_oracle("triple"):
        return Oracle("triple", [p, n, b, v])
    s, q = ctx.fresh(2)
    return ExIn(s, p, ExIn(q, s, And(pair(ctx, p, q, v), pair(ctx, q, n, b))))

# ---------- ハイパー演算 H(n, a, b) ----------
#   H(0,a,b)=b+1, H(1,a,0)=a, H(2,a,0)=0, H(n,a,0)=1 (n≥3), H(n+1,a,b+1)=H(n,a,H(n+1,a,b))

def hyper_table(ctx, t, a):
    p, s1, q, v, s2, n, b = ctx.fresh(7)
    def case():
        n1, b1, p2, sa, w, p3, e1 = ctx.fresh(7)
        is_one = lambda z: ExIn(e1, z, And(empty(ctx, e1), succ_of(ctx, e1, z)))
        base = disj(And(empty(ctx, n1), Eq(v, a)),
                    And(is_one(n1), empty(ctx, v)),
                    conj(Not(empty(ctx, n1)), Not(is_one(n1)), is_one(v)))
        zero_n = And(empty(ctx, n), succ_of(ctx, b, v))
        zero_b = ExIn(n1, n, conj(succ_of(ctx, n1, n), empty(ctx, b), base))
        rec = ExIn(n1, n, ExIn(b1, b, conj(
                succ_of(ctx, n1, n), succ_of(ctx, b1, b),
                ExIn(p2, t, ExIn(sa, p2, ExIn(w, sa, And(
                    triple(ctx, p2, n, b1, w),
                    ExIn(p3, t, triple(ctx, p3, n1, w, v)))))))))
        return disj(zero_n, zero_b, rec)
    return AllIn(p, t, AllIn(s1, p, AllIn(q, s1, AllIn(v, s1,
           AllIn(s2, q, AllIn(n, s2, AllIn(b, s2,
           Imp(triple(ctx, p, n, b, v), case()))))))))

def hyper(ctx, n, a, b, c):           # c = H(n, a, b)
    if ctx.use_oracle("hyper"):
        return Oracle("hyper", [n, a, b, c])
    t, p = ctx.fresh(2)
    return Ex(t, And(hyper_table(ctx, t, a), ExIn(p, t, triple(ctx, p, n, b, c))))

def _op(ctx, name, k, a, b, c):
    if ctx.use_oracle(name):
        return Oracle(name, [a, b, c])
    o = ctx.fresh()
    return Ex(o, And(numeral(ctx, o, k), hyper(ctx, o, a, b, c)))

def add(ctx, a, b, c): return _op(ctx, "add", 1, a, b, c)   # c = a + b
def mul(ctx, a, b, c): return _op(ctx, "mul", 2, a, b, c)   # c = a · b
def exp(ctx, a, b, c): return _op(ctx, "exp", 3, a, b, c)   # c = a ^ b

# ---------- 素数 ----------

def divides(ctx, d, m):               # ∃k (m = d · k)
    k = ctx.fresh()
    return Ex(k, mul(ctx, d, k, m))

def prime(ctx, p):
    if ctx.use_oracle("prime"):
        return Oracle("prime", [p])
    d = ctx.fresh()
    small = lambda z: Or(empty(ctx, z), _is_one(ctx, z))
    return conj(nat(ctx, p), Not(small(p)),
                AllIn(d, p, Imp(Not(small(d)), Not(divides(ctx, d, p)))))

def _is_one(ctx, z):
    e = ctx.fresh()
    return ExIn(e, z, And(empty(ctx, e), succ_of(ctx, e, z)))

def prime_table(ctx, t):
    """t の各行 (i, p) は p = p_i（0 番目の素数は 2）。"""
    def row(q, i, p):
        i1, m = ctx.fresh(2)
        first = And(empty(ctx, i), numeral(ctx, p, 2))
        nxt = ExIn(i1, i, And(succ_of(ctx, i1, i),
              lookup(ctx, t, i1, lambda p2: conj(
                  In(p2, p), prime(ctx, p),
                  AllIn(m, p, Imp(In(p2, m), Not(prime(ctx, m))))))))
        return Or(first, nxt)
    return all_pairs(ctx, t, row)

def nth_prime(ctx, i, p):             # p = p_i（原文の表記で (1+i) 番目の素数）
    if ctx.use_oracle("nth_prime"):
        return Oracle("nth_prime", [i, p])
    t = ctx.fresh()
    return Ex(t, And(prime_table(ctx, t), lookup(ctx, t, i, lambda p2: Eq(p2, p))))

# ---------- 有限列と Encode ----------

def seqfun(ctx, s, h):
    """s は定義域 h（自然数）の関数で、値は自然数。s の元は順序対 (i, a_i)。"""
    i, q0 = ctx.fresh(2)
    # すべての元が順序対 (i, a) で、i < h、a は自然数（順序対でない元を拒否する）
    elems = AllIn(q0, s, pair_parts(ctx, q0, lambda i_, a_: And(In(i_, h), nat(ctx, a_))))
    total = AllIn(i, h, lookup(ctx, s, i, lambda a_: Eq(a_, a_)))   # 各 i < h に値がある
    func = all_pairs(ctx, s, lambda q1, i1, a1:
             all_pairs(ctx, s, lambda q2, i2, a2: Imp(Eq(i1, i2), Eq(a1, a2))))
    return conj(nat(ctx, h), elems, total, func)

def prod_table(ctx, t, s):
    """t の各行 (k, P) は P = ∏_{i<k} p_{i+1}^{s(i)}。"""
    def row(q, k, P):
        k1, pr, pw = ctx.fresh(3)
        first = And(empty(ctx, k), _is_one(ctx, P))
        nxt = ExIn(k1, k, And(succ_of(ctx, k1, k),
              lookup(ctx, t, k1, lambda P1:
                lookup(ctx, s, k1, lambda a:
                  Ex(pr, And(nth_prime(ctx, k, pr),
                  Ex(pw, And(exp(ctx, pr, a, pw), mul(ctx, P1, pw, P)))))))))
        return Or(first, nxt)
    return all_pairs(ctx, t, row)

def encode(ctx, s, c):
    """c = Encode(s) = -1 + 2^h ∏_{i<h} p_{i+1}^{s(i)}（h は s の長さ）。"""
    if ctx.use_oracle("encode"):
        return Oracle("encode", [s, c])
    h, t, two, e, c1 = ctx.fresh(5)
    return Ex(h, And(seqfun(ctx, s, h),
           Ex(t, And(prod_table(ctx, t, s),
           lookup(ctx, t, h, lambda P:
             Ex(two, And(numeral(ctx, two, 2),
             Ex(e, And(exp(ctx, two, h, e),
             Ex(c1, And(mul(ctx, e, P, c1), succ_of(ctx, c, c1))))))))))))
