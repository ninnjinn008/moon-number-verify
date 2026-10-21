"""
改訂31 の構造の再帰表（structure.fn_ok の SU 版、lorder.struct_rec・struct_full）の検証。

1. fn_ok（SU 版、本物の式）：D = V_3、α = 2、構造の表 SU = {0 ↦ s0, 1 ↦ s1} の下で、
   ┌U┐ の値が「順序数 x ∈ α なら SU(x)、それ以外は ∅」の表だけを受理する。
   偽の表（U(1) = s0、U(0) = ∅、U(2) = s1）と、別の SU（SU(1) = s0）の下での判定も確かめる。
2. struct_rec（本物の式。下の層は代用）：L(γ) = γ + 1、D_γ = V_{γ+1} と縮め、vstage・cn_ok・l_order・theta_L は代用、
   fn_ok は「Fn が SU から作った正しい表と一致する」代用にする。α = 0, 1, 2 で正しい表を受理し、
   (a) SU(1) の ┌U┐ の値が本物の SU(0) と違う表、(b) ある段の領域が違う表、(c) 段が欠けた表、
   (d) 段が一つ多い表 を拒否する。
3. struct_full（本物の式。ord_of は代用で O(i) = i）：i = 0, 1, 2 で U(i) の五つ組だけを受理する。
"""
import itertools, sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair, to_nat
import structure as ST
import lorder as LO
import test_parse as TP
import test_structure as TSt

def raw(f): f.raw = True; return f
ORC = dict(TP.ORC)
LOW = {"pair", "empty", "succ", "numeral", "nat", "tuple4"}
Vs = TSt.Vs
T4 = TP.tset
U_, TH, F00, F10 = (8, 2, 0, 1), (8, 3, 0, 1), (8, 4, 0, 0), (8, 4, 0, 1)
def seq(vals): return frozenset(pair(nat(i), v) for i, v in enumerate(vals))
def graph(d): return frozenset(pair(a, b) for a, b in d.items())
def tup5(D, E, Cn, Fn, Rel): return pair(pair(D, E), pair(Cn, pair(Fn, Rel)))

# ---------- 1 ----------
def test_fn_su():
    Dm, alpha = Vs[3], nat(2)
    s0, s1 = frozenset({nat(5)}), frozenset({nat(6)})
    SU = graph({nat(0): s0, nat(1): s1})
    SUbad = graph({nat(0): s0, nat(1): s0})
    def uval(x, d):
        k = to_nat(x)
        return d[k] if (k is not None and k < 2) else frozenset()
    def make(d, override=None):
        e = {(T4(F00), seq([])): frozenset()}
        for x in Dm:
            e[(T4(F10), seq([x]))] = frozenset()
            e[(T4(U_), seq([x]))] = uval(x, d)
            e[(T4(TH), seq([x]))] = frozenset()
        if override: e.update(override)
        return frozenset(pair(pair(t, w), v) for (t, w), v in e.items())
    d = {0: s0, 1: s1}
    good = make(d)
    cands = [(good, SU, True), (make(d, {(T4(U_), seq([nat(1)])): s0}), SU, False),
             (make(d, {(T4(U_), seq([nat(0)])): frozenset()}), SU, False),
             (make(d, {(T4(U_), seq([nat(2)])): s1}), SU, False),
             (good, SUbad, False), (make({0: s0, 1: s0}), SUbad, True)]
    Ths = [frozenset(pair(x, frozenset()) for x in Dm)]
    D = transitive_closure({c[0] for c in cands} | {SU, SUbad} | set(Ths) | {Dm} | {nat(k) for k in range(12)})
    ctx = Ctx(oracles=LOW, start=1); vF, vD, va, vS = ctx.fresh(4)
    f = ST.fn_ok(ctx, vF, vD, va, vS)
    bad = 0
    for Fn, S, want in cands:
        if Evaluator(D, ORC).ev(f, {vF: Fn, vD: Dm, va: alpha, vS: S}) != want: bad += 1; print("  NG fn_ok", want)
    return bad, len(cands)

# ---------- 2・3 ----------
CN0 = frozenset({nat(9)})
def Dlev(g): return Vs[g + 1]
def Elev(g): return frozenset(pair(a, b) for b in Dlev(g) for a in b)
def WLev(g):
    lst = sorted(Dlev(g), key=lambda z: (len(z), sorted(map(len, z))))
    return frozenset(pair(lst[i], lst[j]) for i in range(len(lst)) for j in range(i + 1, len(lst)))
def toyFn(g, sud):
    """γ 段の Fn の代用：┌U┐ の値だけを記録（順序数 x < γ なら sud[x]、それ以外は ∅）。"""
    out = set()
    for x in Dlev(g):
        k = to_nat(x)
        out.add(pair(seq([x]), sud[k] if (k is not None and k < g) else frozenset()))
    return frozenset(out)

def build(n, corrupt=None):
    """段 0〜n の正しい表（corrupt で一部を壊す）。"""
    sud = {}
    for g in range(n + 1):
        ref = dict(sud)
        if corrupt == "u" and g == 1: ref[0] = frozenset({nat(4)})
        D = Dlev(g) if not (corrupt == "dom" and g == n) else Dlev(g + 1)
        sud[g] = tup5(D, Elev(g) if D == Dlev(g) else Elev(g + 1), CN0, toyFn(g, ref), frozenset())
    return sud

def orc2():
    o = dict(ORC)
    o["lam_of"] = raw(lambda g, l: to_nat(g) is not None and l == nat(to_nat(g) + 1))
    o["vstage"] = raw(lambda l, D: to_nat(l) is not None and to_nat(l) < len(Vs) and D == Vs[to_nat(l)])
    o["cn_ok"] = raw(lambda C: C == CN0)
    def fnok(Fn, D, g, SU):
        k = to_nat(g)
        if k is None: return False
        sud = {}
        for q in SU:
            for a in TSt.__dict__.get("_dummy", []): pass
        # SU をほどく
        for q in SU:
            els = list(q)
            if len(els) != 2: continue
            a_set, b_set = sorted(els, key=len)
            (a,) = a_set; (b,) = b_set - {a}
            if to_nat(a) is not None: sud[to_nat(a)] = b
        return Fn == toyFn(k, sud)
    o["fn_ok"] = raw(fnok)
    o["l_order"] = raw(lambda l, D, W: any(D == Dlev(g) and W == WLev(g) and to_nat(l) == g + 1 for g in range(3)))
    o["theta_L"] = raw(lambda D, E, Cn, Fn, Rel, W: True)
    o["ord_of"] = raw(lambda i, a: i == a)
    return o
LOW2 = LOW | {"lam_of", "vstage", "cn_ok", "fn_ok", "l_order", "theta_L", "ord_of"}

def test_rec():
    orc = orc2()
    ctx = Ctx(oracles=LOW2, start=1); va, vS = ctx.fresh(2)
    f = LO.struct_rec(ctx, va, vS)
    bad, total = 0, 0
    for n in range(3):
        cands = [(build(n), True)]
        if n >= 1: cands.append((build(n, "u"), False))
        cands.append((build(n, "dom"), False))
        if n >= 1: cands.append(({k: v for k, v in build(n).items() if k != n - 1}, False))
        cands.append((build(n + 1), False))
        udom = {nat(k) for k in range(6)} | {WLev(g) for g in range(4)}
        sets = [graph({nat(k): v for k, v in c.items()}) for c, _ in cands]
        D = transitive_closure(udom | set(sets))
        for S, (_, want) in zip(sets, cands):
            total += 1
            if Evaluator(D, orc, udom).ev(f, {va: nat(n), vS: S}) != want: bad += 1; print("  NG struct_rec", n, want)
    # struct_full
    ctx = Ctx(oracles=LOW2, start=1); vi, vD, vE, vC, vF, vR = ctx.fresh(6)
    g2 = LO.struct_full(ctx, vi, vD, vE, vC, vF, vR)
    tabs = [graph({nat(k): v for k, v in build(n).items()}) for n in range(3)]
    udom = {nat(k) for k in range(6)} | {WLev(g) for g in range(4)} | set(tabs)
    D = transitive_closure(udom)
    for i in range(3):
        for j in range(3):
            s = build(2)[j]
            parts = [(Dlev(j), Elev(j), CN0, toyFn(j, build(2)), frozenset())]
            Dj, Ej, Cj, Fj, Rj = parts[0]
            total += 1
            got = Evaluator(D, orc, udom).ev(g2, {vi: nat(i), vD: Dj, vE: Ej, vC: Cj, vF: Fj, vR: Rj})
            if got != (i == j): bad += 1; print("  NG struct_full", i, j, got)
    return bad, total

def main():
    b1, t1 = test_fn_su(); print(f"fn_ok（SU 版）：{t1} 件で {'すべて一致' if b1 == 0 else str(b1) + ' 件の不一致'}")
    b2, t2 = test_rec(); print(f"struct_rec・struct_full：{t2} 件で {'すべて一致' if b2 == 0 else str(b2) + ' 件の不一致'}")
    return b1 + b2

def mutation():
    import types
    src = open(LO.__file__, encoding="utf-8").read()
    a = "        AllIn(g, a1, A.lookup(ctx, SU, g, lambda x: ST.struct_parts(ctx, x,"
    assert src.count(a) == 1
    m = types.ModuleType("lo_mut"); exec(compile(src.replace(a, "        AllIn(g, alpha, A.lookup(ctx, SU, g, lambda x: ST.struct_parts(ctx, x,"), "m", "exec"), m.__dict__)
    saved = LO.struct_rec; LO.struct_rec = m.struct_rec
    try: b, _ = test_rec()
    finally: LO.struct_rec = saved
    print(f"変異テスト（最後の段 γ = α の条件を外す）：{b} 件の不一致を検出")
    return 0 if b else 1

if __name__ == "__main__":
    import resource; resource.setrlimit(resource.RLIMIT_AS, (6_000_000_000, 6_000_000_000))
    b = main()
    if "--mutation" in sys.argv: b += mutation()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)

