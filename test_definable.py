"""
definable.py（IsDefinition と Definable の意味による表現）の検証。

答え合わせ役は、原文どおりに IsDefinition(P) ≡ ∃x0 (P ∧ ∀x1 (P[x1/x0] → x1 = x0)) を
**構文的に**組み立て、原文の代入規則（∃y(Q) で代入する項に y が現れるなら y を新しい変数に付け替える）で
P[x1/x0] を計算し、全称閉包で評価する。判定式は代入補題で意味に書き換えているので、
両者の一致は書き換えの正しさの確認にもなる。

回帰例（別の AI による審査の提案）：
  P が x1 を自由にもつ・x0, x1 以外の自由変数をもつ・x1 を束縛変数として使う、の三種を固定で含める。
下位の充足関係 sat は代用関係に差し替える（test_sat.py で検証済み）。
"""
import itertools, random, sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair
import definable as DF
import test_sat as TS
T = TS.T

X2 = (7, 1, 2, 0)
def V(k): return (7, 1, k, 0)

# ---------- 原文どおりの代入と IsDefinition（答え合わせ役） ----------
def vars_in(f):
    out = set()
    def term(a):
        if a[0] == "var": out.add(a[1])
        elif a[0] == "app": [term(x) for x in a[2]]
    def form(g):
        k = g[0]
        if k in ("neg",): form(g[1])
        elif k in ("imp", "and"): form(g[1]); form(g[2])
        elif k == "exists": out.add(g[1]); form(g[2])
        elif k in ("elem", "eq"): term(g[1]); term(g[2])
        elif k == "rel": [term(x) for x in g[2]]
    form(f); return out

def subst_term(a, x, y):            # 項の中の変数 x を変数 y に
    if a[0] == "var": return ("var", y) if a[1] == x else a
    if a[0] == "app": return ("app", a[1], [subst_term(b, x, y) for b in a[2]])
    return a

def subst(f, x, y):
    """f[x_y / x_x]：原文の規則。∃z(Q) で z == y（代入する項に z が現れる）なら z を新しい変数に付け替える。"""
    k = f[0]
    if k == "bot": return f
    if k == "neg": return ("neg", subst(f[1], x, y))
    if k in ("imp", "and"): return (k, subst(f[1], x, y), subst(f[2], x, y))
    if k in ("elem", "eq"): return (k, subst_term(f[1], x, y), subst_term(f[2], x, y))
    if k == "rel": return ("rel", f[1], [subst_term(a, x, y) for a in f[2]])
    if k == "exists":
        z, body = f[1], f[2]
        if z == x: return f                         # x は束縛されている
        if z == y:                                  # 捕獲を避けるため付け替える
            new = max(vars_in(f) | {x, y}) + 1
            body = subst(body, z, new)
            z = new
        return ("exists", z, subst(body, x, y))
    raise ValueError(k)

def is_definition_ast(P):
    forall = lambda v, g: ("neg", ("exists", v, ("neg", g)))
    return ("exists", 0, ("and", P, forall(1, ("imp", subst(P, 0, 1), ("eq", ("var", 1), ("var", 0))))))

def ev(f, M, sg):
    k = f[0]
    if k == "and": return ev(f[1], M, sg) and ev(f[2], M, sg)
    if k == "eq": return TS.ev_term(f[1], M, sg) == TS.ev_term(f[2], M, sg)
    if k == "neg": return not ev(f[1], M, sg)
    if k == "imp": return (not ev(f[1], M, sg)) or ev(f[2], M, sg)
    if k == "exists": return any(ev(f[2], M, {**sg, f[1]: a}) for a in M.dom)
    return TS.ev_form(f, M, sg)

def free_vars(f, bound=frozenset()):
    k = f[0]
    if k == "exists": return free_vars(f[2], bound | {f[1]})
    if k in ("neg",): return free_vars(f[1], bound)
    if k in ("imp", "and"): return free_vars(f[1], bound) | free_vars(f[2], bound)
    out = set()
    def term(a):
        if a[0] == "var" and a[1] not in bound: out.add(a[1])
        elif a[0] == "app": [term(x) for x in a[2]]
    if k in ("elem", "eq"): term(f[1]); term(f[2])
    elif k == "rel": [term(x) for x in f[2]]
    return out

def closed_true(f, M, fixed=None):
    fixed = fixed or {}
    fv = sorted(free_vars(f) - set(fixed))
    return all(ev(f, M, {**dict(zip(fv, vals)), **fixed}) for vals in itertools.product(M.dom, repeat=len(fv)))

def ref_definable(P, M, m):
    return closed_true(is_definition_ast(P), M) and closed_true(P, M, {0: m})

# ---------- 代用関係 ----------
_STR = {}
def raw(f): f.raw = True; return f
_M = {}
def sat_oracle(s, dom, E, Cn, Fn, Rel, sg):
    P = _STR[s]; M = _M["cur"]
    d = {}
    for q in sg:
        for k in range(6):
            for a in M.dom:
                if q == pair(nat(k), a): d[k] = a
    return TS.ev_form(TS.parse_whole(P, "F"), M, d)
ORC = dict(TS.ORC)
ORC["sat_ext"] = raw(sat_oracle)
LOW = TS.LOW | {"sat"}

def run(P, M, mutate=False, light=True):
    s = T.sset(P); _STR[s] = P; _M["cur"] = M
    Ns = sorted({t[2] for t in P if TS.is_var(t)})
    W = sorted(set(Ns) | {0, 1})
    assigns = [frozenset(pair(nat(k), a) for k, a in zip(W, vals)) for vals in itertools.product(M.dom, repeat=len(W))]
    dom, E, Cn, Fn, Rel = TS.struct_sets(M)
    witnesses = {s, dom, E, Cn, Fn, Rel, frozenset(nat(k) for k in Ns), frozenset(nat(k) for k in W)} | set(assigns) | {nat(k) for k in range(len(P) + 3)}
    D = transitive_closure(witnesses)
    udom = ({nat(k) for k in range(max(len(P) + 3, 13))} | set(assigns) |
            {frozenset(nat(k) for k in Ns), frozenset(nat(k) for k in W)}) if light else None
    ctx = Ctx(oracles=LOW, start=1)
    vs, vd, vE, vC, vF, vR, vm = ctx.fresh(7)
    f = DF.definable_in(ctx, vs, vd, vE, vC, vF, vR, vm, mutate=mutate)
    bad = 0
    for m in M.dom:
        got = Evaluator(D, ORC, udom).ev(f, {vs: s, vd: dom, vE: E, vC: Cn, vF: Fn, vR: Rel, vm: m})
        want = ref_definable(TS.parse_whole(P, "F"), M, m)
        if got != want: bad += 1
    return bad, len(M.dom)

X0, X1 = T.X[0], T.X[1]
FIXED = {
    "x1 を自由にもつ (x0 ∈ x1)": [T.LP, X0, T.ELEM, X1, T.RP],
    "x1 を自由にもつ (x1 ∈ x0)": [T.LP, X1, T.ELEM, X0, T.RP],
    "x2 を自由にもつ (x0 ∈ x2)": [T.LP, X0, T.ELEM, X2, T.RP],
    "x1 を束縛 ∃x1((x0 ∈ x1))": [T.EXI, X1, T.LP, T.LP, X0, T.ELEM, X1, T.RP, T.RP],
    "x0 は空 ¬∃x1((x1 ∈ x0))": [T.NEG, T.EXI, X1, T.LP, T.LP, X1, T.ELEM, X0, T.RP, T.RP],
    "x1 を束縛し x0 も束縛 ∃x0((x0 ∈ x1))": [T.EXI, X0, T.LP, T.LP, X0, T.ELEM, X1, T.RP, T.RP],
    "x0 = c0 の代わり (x0 ∈ c0)": [T.LP, X0, T.ELEM, T.C0, T.RP],
}

def structures(r):
    out = []
    for bits in range(16):                          # 2 元の領域で ∈ の解釈を全通り
        M = TS.random_struct(r, 2)
        pairs = [(a, b) for a in M.dom for b in M.dom]
        M.E = {pairs[k] for k in range(4) if bits >> k & 1}
        out.append(M)
    for _ in range(4):
        out.append(TS.random_struct(r, 3))
    return out

def main(n_rand=6, seed=5):
    r = random.Random(seed)
    Ms = structures(r)
    total = bad = 0
    cases = list(FIXED.items())
    while len(cases) < len(FIXED) + n_rand:
        P = T.gen_formula(r, 2)
        if len(P) <= 10 and all(P != c for _, c in cases):
            cases.append((f"ランダム {len(cases) - len(FIXED) + 1}", P))
    for name, P in cases:
        b = n = 0
        for M in Ms:
            bb, nn = run(P, M); b += bb; n += nn
        bad += b; total += n
        print(f"  {name}: 判定 {n} 回、不一致 {b}", flush=True)
    print(f"Definable: 式 {len(cases)} 個 × 構造 {len(Ms)} 個、判定 {total} 回 → {'すべて一致' if bad == 0 else str(bad) + ' 件の不一致'}")
    return bad

def mutation():
    """変異版（外側の ∀x1 が x1 を取り替えない＝「意図した意味」の読み）が、x1 を自由にもつ式で食い違うことを確かめる。"""
    r = random.Random(9)
    n = 0
    for M in structures(r):
        n += run(FIXED["x1 を自由にもつ (x0 ∈ x1)"], M, mutate=True)[0]
        n += run(FIXED["x1 を自由にもつ (x1 ∈ x0)"], M, mutate=True)[0]
    print(f"変異テスト（外側の ∀x1 による取り替えを外した版）: {n} 件の不一致を検出" + ("" if n else "　※検出できていない"))
    return 0 if n else 1

if __name__ == "__main__":
    b = main()
    if "--mutation" in sys.argv:
        b += mutation()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)
