"""
fsub.py の検証（下の層 pair・triple・empty・succ・numeral・nat・add は代用関係に差し替える）。

- 層 1（証明書）：記号列ごとに、Python の参照実装で求めた完全な証明書（すべての変数区間と式区間）を与え、
  cert_ok が真で、根の項目 ((0, h), 1) があることと「式である」ことが一致するか。
  さらに、式でない区間に式の項目を足した偽の証明書を cert_ok が拒否するか。
- 層 2（IX・Ns・FV と、自由変数が x だけ）：正しい表を受理し、一項目を変えた表を拒否するか。
  only_x が参照実装の「自由変数がちょうど x」と一致するか。
- 層 3（充足の表 S）：W = {0, 1}（= V_2）と W = V_3 で、正しい S を受理し、一項目を反転した S を拒否するか。
  holds(a) と「W ⊨ φ[x := a]」、一意性が参照実装と一致するか。
- 層 4（f_sub）：defines_in を代用にして、x = 1 + max のときだけ真か。
- 層 5（Num_y）：y = 1〜40 で、Num_y(u) を満たす u が y だけか（add は代用）。
--mutation：参照実装の否定の規則を壊した版で、層 3 が不一致を出すことを確かめる。
"""
import itertools, sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair, to_nat
import fsub as FS
import arith as A

def raw(f): f.raw = True; return f
ORC = {
    "pair": raw(lambda p, a, b: p == pair(a, b)),
    "triple": raw(lambda p, n, b, v: p == pair(pair(n, b), v)),
    "empty": raw(lambda a: a == frozenset()),
    "succ": raw(lambda b, c: c == (b | {b})),
    "numeral": raw(lambda k, v: v == nat(int(k))),
    "nat": raw(lambda a: to_nat(a) is not None),
    "add": lambda a, b, c: a + b == c,
}
LOW = {"pair", "triple", "empty", "succ", "numeral", "nat", "add"}
MUT = "--mutation" in sys.argv

# ---------------- 参照実装 ----------------
X, P, NEG, AND, ALL, ELEM, EQ, LP, RP = range(9)
def lex(st):
    m = {"x": X, "′": P, "¬": NEG, "∧": AND, "∀": ALL, "∈": ELEM, "=": EQ, "(": LP, ")": RP}
    return [m[c] for c in st]

def is_var(t, i, j):
    return 0 <= i < j <= len(t) and t[i] == X and all(t[p] == P for p in range(i + 1, j))

def parse_all(t):
    """完全な証明書：変数区間と式区間の全体。式区間は区間の長さの順に決める。"""
    h = len(t)
    V = {(i, j) for i in range(h) for j in range(i + 1, h + 1) if is_var(t, i, j)}
    F, how = set(), {}
    for L in range(1, h + 1):
        for i in range(0, h - L + 1):
            j = i + L
            r = None
            if t[i] == LP:
                for a in range(i + 2, j):
                    for b in range(a + 2, j):
                        if (i + 1, a) in V and t[a] in (ELEM, EQ) and (a + 1, b) in V and t[b] == RP and b + 1 == j:
                            r = ("atom", i + 1, a, a + 1, b)
                for a in range(i + 2, j):
                    if (i + 1, a) in F and t[a] == AND and (a + 1, j - 1) in F and t[j - 1] == RP:
                        r = ("and", i + 1, a, a + 1, j - 1)
            elif t[i] == NEG and (i + 1, j) in F:
                r = ("not", i + 1, j)
            elif t[i] == ALL:
                for a in range(i + 2, j):
                    if (i + 1, a) in V and (a, j) in F:
                        r = ("all", i + 1, a)
            if r:
                F.add((i, j)); how[(i, j)] = r
    return V, F, how

def idx(i, j): return j - i - 1

def fv_ref(how, i, j):
    r = how[(i, j)]
    if r[0] == "atom": return {idx(r[1], r[2]), idx(r[3], r[4])}
    if r[0] == "not": return fv_ref(how, r[1], r[2])
    if r[0] == "and": return fv_ref(how, r[1], r[2]) | fv_ref(how, r[3], r[4])
    return fv_ref(how, r[2], j) - {idx(r[1], r[2])}

def sat_ref(t, how, i, j, sg, W):
    r = how[(i, j)]
    if r[0] == "atom":
        u, v = sg[idx(r[1], r[2])], sg[idx(r[3], r[4])]
        return (u in v) if t[r[2]] == ELEM else (u == v)
    if r[0] == "not":
        b = sat_ref(t, how, r[1], r[2], sg, W)
        return b if MUT else not b
    if r[0] == "and": return sat_ref(t, how, r[1], r[2], sg, W) and sat_ref(t, how, r[3], r[4], sg, W)
    m = idx(r[1], r[2])
    return all(sat_ref(t, how, r[2], j, {**sg, m: e}, W) for e in W)

# ---------------- 集合の組み立て ----------------
def fun(d): return frozenset(pair(nat(k), v) for k, v in d.items())
def trip(i, j, v): return pair(pair(nat(i), nat(j)), v)

def tables(t, W):
    V, F, how = parse_all(t)
    C = frozenset({trip(i, j, nat(0)) for (i, j) in V} | {trip(i, j, nat(1)) for (i, j) in F})
    IX = frozenset(trip(i, j, nat(idx(i, j))) for (i, j) in V)
    Ns = sorted({idx(i, j) for (i, j) in V})
    FVt = frozenset(trip(i, j, nat(m)) for (i, j) in F for m in fv_ref(how, i, j))
    sgs = [dict(zip(Ns, c)) for c in itertools.product(W, repeat=len(Ns))]
    S = frozenset(trip(i, j, fun(sg)) for (i, j) in F for sg in sgs if sat_ref(t, how, i, j, sg, W)) if W else frozenset()
    return dict(s=fun({p: nat(c) for p, c in enumerate(t)}), h=nat(len(t)), C=C, IX=IX,
                Ns=frozenset(nat(m) for m in Ns), FV=FVt, S=S, V=V, F=F, how=how, sgs=sgs, Nsl=Ns)

NAMES = ["s", "h", "C", "IX", "Ns", "FV", "S", "W", "K0"]
def make(ctx):
    vs = ctx.fresh(len(NAMES))
    env_vars = dict(zip(NAMES, vs))
    return FS.FS(ctx, *vs), env_vars

def evaluate(f, env_vars, vals, extra_univ=()):
    env = {env_vars[k]: vals[k] for k in NAMES if k in vals}
    univ = set(vals.values()) | {nat(k) for k in range(30)} | set(extra_univ)
    D = transitive_closure(univ)
    udom = {nat(k) for k in range(30)} | set(extra_univ)
    return Evaluator(D, ORC, udom).ev(f, env)

STRS = ["(x∈x)", "(x=x′)", "¬(x∈x)", "∀x′(x′∈x)", "((x∈x)∧(x=x))", "∀x(x∈x)", "¬∀x′¬(x′∈x)",
        "(x∈x", "x∈x)", "(x∈∈x)", "∀(x∈x)", "(x∧x)", "¬¬(x′=x′′)", "((x∈x)∧(x∈x)",
        "∀x′∀x′′(x′∈x′′)", "(x′∈x)"]

def layer1():
    bad = total = 0
    for st in STRS:
        t = lex(st); T = tables(t, [])
        ctx = Ctx(oracles=LOW, start=1); fs, ev = make(ctx)
        f_ok = fs.cert_ok(); f_root = fs.inC(ev["K0"], ev["h"], 1)
        vals = {k: T[k] for k in ("s", "h", "C")}; vals["K0"] = nat(0)
        total += 2
        if not evaluate(f_ok, ev, vals): bad += 1; print("  cert_ok 不一致", st)
        want = (0, len(t)) in T["F"]
        if evaluate(f_root, ev, vals) != want: bad += 1; print("  根 不一致", st)
        # 偽の項目：式でない区間 (i, j) に式の項目を足す
        for i in range(len(t)):
            for j in range(i + 1, len(t) + 1):
                if (i, j) not in T["F"]:
                    total += 1
                    v2 = dict(vals); v2["C"] = T["C"] | {trip(i, j, nat(1))}
                    if evaluate(f_ok, ev, v2): bad += 1; print("  偽の項目を受理", st, i, j)
    return bad, total

def layer2():
    bad = total = 0
    for st in STRS:
        t = lex(st); T = tables(t, [])
        if (0, len(t)) not in T["F"]: continue
        ctx = Ctx(oracles=LOW, start=1); fs, ev = make(ctx)
        fs_ = [fs.ix_ok(), fs.ns_ok(), fs.fv_ok()]
        f_x = fs.only_x()
        vals = {k: T[k] for k in ("s", "h", "C", "IX", "Ns", "FV")}; vals["K0"] = nat(0)
        for f in fs_:
            total += 1
            if not evaluate(f, ev, vals): bad += 1; print("  正しい表を拒否", st)
        total += 1
        want = fv_ref(T["how"], 0, len(t)) == {0}
        if evaluate(f_x, ev, vals) != want: bad += 1; print("  only_x 不一致", st)
        # 変異：IX の値を一つずらす、FV に一項目足す・除く
        for (i, j) in sorted(T["V"])[:2]:
            total += 1
            v2 = dict(vals); v2["IX"] = (T["IX"] - {trip(i, j, nat(idx(i, j)))}) | {trip(i, j, nat(idx(i, j) + 1))}
            if evaluate(fs_[0], ev, v2): bad += 1; print("  ずらした IX を受理", st)
        for (i, j) in list(T["F"])[:3]:
            for m in T["Nsl"]:
                e = trip(i, j, nat(m)); total += 1
                v2 = dict(vals); v2["FV"] = T["FV"] ^ {e}
                if evaluate(fs_[2], ev, v2): bad += 1; print("  変えた FV を受理", st, i, j, m)
    return bad, total

E = frozenset()
W2 = [nat(0), nat(1)]
W3 = [nat(0), nat(1), frozenset({nat(1)}), nat(2)]
DEFS = ["∀x′¬(x′∈x)", "¬∀x′¬(x′∈x)", "(x=x)", "¬(x∈x)", "∀x′(x′∈x)", "¬∀x′¬(x∈x′)", "(x∈x)",
        "∀x′((x′∈x)∧¬(x′∈x))", "¬∀x′(¬(x′∈x)∧¬(x′=x))"]

def layer3():
    bad = total = 0
    for Wl in (W2, W3):
        Wset = frozenset(Wl)
        for st in DEFS:
            t = lex(st); T = tables(t, Wl)
            ctx = Ctx(oracles=LOW, start=1); fs, ev = make(ctx)
            a, b = ctx.fresh(2)
            f_s = fs.s_ok()
            f_hold = fs.holds(a)
            vals = {k: T[k] for k in ("s", "h", "C", "IX", "Ns", "FV", "S")}; vals["K0"] = nat(0); vals["W"] = Wset
            sg_sets = [fun(sg) for sg in T["sgs"]]
            total += 1
            if not evaluate(f_s, ev, vals, sg_sets): bad += 1; print("  正しい S を拒否", st)
            for (i, j) in list(T["F"])[:4]:
                for sg in sg_sets[:3]:
                    total += 1
                    v2 = dict(vals); v2["S"] = T["S"] ^ {trip(i, j, sg)}
                    if evaluate(f_s, ev, v2, sg_sets): bad += 1; print("  反転した S を受理", st, i, j)
            for e in Wl:
                total += 1
                want = sat_ref(t, T["how"], 0, len(t), {**{m: Wl[0] for m in T["Nsl"]}, 0: e}, Wl)
                env = dict(vals)
                ev2 = dict(ev); ev2["a"] = a
                got = evaluate_with(f_hold, ev, vals, {a: e}, sg_sets)
                if got != want: bad += 1; print("  holds 不一致", st, e)
    return bad, total

def evaluate_with(f, env_vars, vals, extra_env, extra_univ):
    env = {env_vars[k]: vals[k] for k in NAMES if k in vals}; env.update(extra_env)
    univ = set(vals.values()) | {nat(k) for k in range(30)} | set(extra_univ) | set(extra_env.values())
    D = transitive_closure(univ)
    udom = {nat(k) for k in range(30)} | set(extra_univ)
    return Evaluator(D, ORC, udom).ev(f, env)

def layer4():
    bad = total = 0
    sets = {"A": {2, 5}, "B": set(), "C": {0}, "D": {7, 1, 3}}
    for name, Sset in sets.items():
        W = frozenset({nat(100 + len(name))})
        ctx = Ctx(oracles=LOW | {"defines_in"}, start=1)
        vW, vk, vx = ctx.fresh(3)
        f = FS.f_sub(ctx, vW, vk, vx)
        orc = dict(ORC); orc["defines_in"] = raw(lambda Wv, k, n: to_nat(n) is not None and to_nat(n) in Sset)
        Dset = frozenset(nat(n) for n in Sset)
        want = 1 + max(Sset) if Sset else 1
        for x in range(10):
            total += 1
            univ = {W, nat(3), nat(x), Dset} | {nat(k) for k in range(12)}
            D = transitive_closure(univ)
            got = Evaluator(D, orc, univ).ev(f, {vW: W, vk: nat(3), vx: nat(x)})
            if got != (x == want): bad += 1; print("  f_sub 不一致", name, x)
    return bad, total

def layer5():
    bad = total = 0
    univ = {nat(k) for k in range(45)}
    D = transitive_closure(univ)
    for y in range(1, 41):
        f = FS.num_formula(y)
        for u in range(45):
            total += 1
            got = Evaluator(D, ORC, univ).ev(_orc(f), {1: nat(u)})
            if got != (u == y): bad += 1; print("  Num 不一致", y, u)
    return bad, total

def _orc(f):
    return f

if __name__ == "__main__":
    # Num は Ctx(start=3) で本物の add を使うので、代用に差し替えた版を作る
    import fsub
    def _step(u, w, bit):
        ctx = Ctx(start=3, oracles={"add", "succ", "numeral", "empty"})
        if bit == 0:
            return A.add(ctx, w, w, u)
        t = ctx.fresh()
        return fsub.Ex(t, fsub.And(A.add(ctx, w, w, t), A.succ_of(ctx, t, u)))
    fsub._step = _step
    _num = fsub.num_formula
    def num_formula(y, u=1):
        bits = bin(y)[2:]; w = 2 if u == 1 else 1
        if len(bits) == 1:
            return A.numeral(Ctx(start=3, oracles={"numeral"}), u, 1)
        return fsub.Ex(w, fsub.And(num_formula(int(bits[:-1], 2), w), _step(u, w, int(bits[-1]))))
    fsub.num_formula = num_formula
    for name, fn in (("層 1（証明書）", layer1), ("層 2（IX・Ns・FV・only_x）", layer2),
                     ("層 3（充足の表 S・holds）", layer3), ("層 4（f_sub）", layer4), ("層 5（Num_y）", layer5)):
        b, t = fn()
        print(f"{name}: {t} 件中 不一致 {b}", flush=True)
