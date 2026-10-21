"""
ffunc.py の検証（下の層は代用関係に差し替える）。

- finite_sum：S ⊆ {0, …, 5} のすべての部分集合（64 個）と v = 0〜16 について、v = ΣS のときだけ真。
  加法は代用関係（test_arith.py で検証済み）。
- definable_set：構造の表は「i ごとに決まったおもちゃの構造」、Definable は「(i, 番号 c) ごとに決まった m」
  （一部の (i, c) では定義される m がない）、Formula と MetaCode は代用。n = 1〜4 で、正しい S を受理し、
  元を一つ欠いた S・余計な元を加えた S を拒否する。おもちゃには、番号 c ≥ n の式や i ≥ n の構造でだけ
  定義される m を入れ、範囲の境界（i ∈ n、MetaCode(P) ∈ n）も確かめる。
- f_val：上の代用を組み合わせ、n = 1〜4 で正しい f(n) だけを受理する（struct_table も含めて本物の式）。
- iterate10：f をおもちゃの関数に差し替え、a = 0〜6 で x = f^10(a) のときだけ真。
- lngn は 10↑^10 10 が大きすぎて有限の宇宙に入らないので、記号数と自由変数だけを確かめる
  （ハイパー演算は test_hyper.py・test_arith.py で小さい値について検証済み）。
"""
import itertools, sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair, to_nat
import ffunc as FF
import test_sat as TS
T = TS.T

def raw(f): f.raw = True; return f
def fun(d): return frozenset(pair(nat(k), v) for k, v in d.items())

ORC = dict(TS.ORC)
ORC["add"] = lambda a, b, c: a + b == c
ORC["nat"] = raw(lambda a: to_nat(a) is not None)
LOW = TS.LOW | {"add", "nat"}

# ---------- finite_sum ----------
def test_sum():
    ctx = Ctx(oracles=LOW, start=1); vS, vv = ctx.fresh(2)
    f = FF.finite_sum(ctx, vS, vv)
    subsets = [frozenset(nat(k) for k in c) for r in range(7) for c in itertools.combinations(range(6), r)]
    # 表 R の候補：各 K（0〜7）について正しい部分和の表を全部入れ、偽の表も混ぜる
    tables = []
    for S in subsets:
        for K in range(max([to_nat(x) + 1 for x in S], default=0), 8):
            R, acc = {0: nat(0)}, 0
            for k in range(K):
                acc += k if nat(k) in S else 0
                R[k + 1] = nat(acc)
            tables.append(fun(R))
            Rb = dict(R); Rb[K] = nat(acc + 1); tables.append(fun(Rb))
    udom = set(tables) | {nat(k) for k in range(20)}
    D = transitive_closure(udom | set(subsets))
    ev = Evaluator(D, ORC, udom)
    bad, total = 0, 0
    for S in subsets:
        want = sum(to_nat(x) for x in S)
        for v in range(17):
            total += 1
            if ev.ev(f, {vS: S, vv: nat(v)}) != (v == want): bad += 1
    return bad, total

# ---------- definable_set / f_val ----------
TOY_D = {i: nat(i + 20) for i in range(6)}           # i ごとのおもちゃの構造の領域（区別できればよい）
def toy_struct(i):
    e = frozenset()
    return pair(pair(TOY_D[i], e), pair(e, pair(e, e)))
CODES = {0: [T.LP, T.X[0], T.ELEM, T.X[1], T.RP], 1: [T.LP, T.X[1], T.ELEM, T.X[0], T.RP],
         2: [T.NEG, T.LP, T.X[0], T.ELEM, T.X[0], T.RP], 3: [T.LP, T.X[0], T.ELEM, T.C0, T.RP],
         4: [T.NEG, T.LP, T.X[1], T.ELEM, T.X[1], T.RP]}
DEFS = {(0, 0): 3, (0, 2): 5, (1, 0): 3, (1, 1): 7, (2, 3): 1, (3, 4): 9, (0, 4): 11, (4, 0): 13, (2, 2): 0}
SSETS = {T.sset(P): c for c, P in CODES.items()}

def ref_S(n):
    return frozenset(nat(m) for (i, c), m in DEFS.items() if i < n and c < n)

def toy_orc():
    o = dict(ORC)
    o["struct_full"] = raw(lambda i, D, E, Cn, Fn, Rel: to_nat(i) is not None and to_nat(i) in TOY_D and
                       pair(pair(D, E), pair(Cn, pair(Fn, Rel))) == toy_struct(to_nat(i)))
    o["formula"] = raw(lambda s: s in SSETS)
    o["metacode"] = raw(lambda c, s: s in SSETS and SSETS[s] == to_nat(c))
    def dfn(s, D, E, Cn, Fn, Rel, m):
        if s not in SSETS: return False
        i = next((k for k, d in TOY_D.items() if d == D), None)
        return i is not None and DEFS.get((i, SSETS[s])) == to_nat(m)
    o["definable"] = raw(dfn)
    return o
LOW2 = LOW | {"struct_full", "formula", "metacode", "definable"}

def test_defset():
    orc = toy_orc()
    ctx = Ctx(oracles=LOW2, start=1); vn, vST, vS = ctx.fresh(3)
    f = FF.definable_set(ctx, vn, vST, vS)
    g = FF.struct_table(ctx, vn, vST)
    bad, total = 0, 0
    for n in range(1, 5):
        ST = fun({i: toy_struct(i) for i in range(n)})
        STbad = fun({i: toy_struct(i if i != n - 1 else 5) for i in range(n)})
        STshort = fun({i: toy_struct(i) for i in range(n - 1)})
        S = ref_S(n)
        cands = [(S, True)]
        for x in S: cands.append((S - {x}, False))
        for extra in (2, 4, 15):
            if nat(extra) not in S: cands.append((S | {nat(extra)}, False))
        udom = set(T.sset(P) for P in CODES.values()) | {nat(k) for k in range(25)}
        D = transitive_closure(udom | {c for c, _ in cands} | {ST, STbad, STshort})
        ev = Evaluator(D, orc, udom)
        for Sc, want in cands:
            total += 1
            if ev.ev(f, {vn: nat(n), vST: ST, vS: Sc}) != want: bad += 1; print("  NG defset", n, want)
        for STc, want in ((ST, True), (STbad, False), (STshort, False)):
            total += 1
            if ev.ev(g, {vn: nat(n), vST: STc}) != want: bad += 1; print("  NG struct_table", n, want)
    return bad, total

def test_fval():
    orc = toy_orc()
    ctx = Ctx(oracles=LOW2, start=1); vn, vv = ctx.fresh(2)
    f = FF.f_val(ctx, vn, vv)
    bad, total, vals = 0, 0, []
    for n in range(1, 5):
        S = ref_S(n); want = sum(to_nat(x) for x in S); vals.append(want)
        ST = fun({i: toy_struct(i) for i in range(n)})
        tables = []
        for K in range(max([to_nat(x) + 1 for x in S], default=0), max([to_nat(x) + 1 for x in S], default=0) + 2):
            R, acc = {0: nat(0)}, 0
            for k in range(K):
                acc += k if nat(k) in S else 0
                R[k + 1] = nat(acc)
            tables.append(fun(R))
        Sdec = [S - {x} for x in S] + [S | {nat(2)}]
        udom = set(T.sset(P) for P in CODES.values()) | {nat(k) for k in range(40)} | {ST, S} | set(tables) | set(Sdec)
        D = transitive_closure(udom)
        ev = Evaluator(D, orc, udom)
        for v in range(want + 3):
            total += 1
            if ev.ev(f, {vn: nat(n), vv: nat(v)}) != (v == want): bad += 1; print("  NG f_val", n, v)
    return bad, total, vals

# ---------- iterate10 ----------
def toy_f(k): return (3 * k + 2) % 11
def test_iter():
    orc = dict(ORC); orc["f_val"] = lambda n, v: toy_f(n) == v
    ctx = Ctx(oracles=LOW | {"f_val"}, start=1); va, vx = ctx.fresh(2)
    f = FF.iterate10(ctx, va, vx)
    bad, total = 0, 0
    for a in range(7):
        seq = [a]
        for _ in range(10): seq.append(toy_f(seq[-1]))
        G = fun({j: nat(v) for j, v in enumerate(seq)})
        Gbad = fun({j: nat(v if j != 5 else (v + 1) % 11) for j, v in enumerate(seq)})
        G9 = fun({j: nat(v) for j, v in enumerate(seq[:10])})
        udom = {G, Gbad, G9} | {nat(k) for k in range(13)}
        D = transitive_closure(udom)
        ev = Evaluator(D, orc, udom)
        for x in range(11):
            total += 1
            if ev.ev(f, {va: nat(a), vx: nat(x)}) != (x == seq[10]): bad += 1; print("  NG iter", a, x)
    return bad, total

def main():
    b1, t1 = test_sum(); print(f"finite_sum：{t1} 件で {'すべて一致' if b1 == 0 else str(b1) + ' 件の不一致'}")
    b2, t2 = test_defset(); print(f"definable_set・struct_table：{t2} 件で {'すべて一致' if b2 == 0 else str(b2) + ' 件の不一致'}")
    b3, t3, vals = test_fval(); print(f"f_val：n = 1〜4（f(n) = {vals}）、{t3} 件で {'すべて一致' if b3 == 0 else str(b3) + ' 件の不一致'}")
    b4, t4 = test_iter(); print(f"iterate10：{t4} 件で {'すべて一致' if b4 == 0 else str(b4) + ' 件の不一致'}")
    return b1 + b2 + b3 + b4

def _mut(src, old, new):
    """変異版のソース。置換する箇所がちょうど一か所あることを確かめる（置換の空振りで変異テストが素通りしないように）。"""
    assert src.count(old) == 1, f"変異させる箇所が {src.count(old)} 個（1 個であるべき）: {old.strip()[:60]}"
    return src.replace(old, new)

def mutation():
    import types
    src = open(FF.__file__, encoding="utf-8").read()
    n = 0
    # 1. MetaCode(P) ∈ n の条件を外す（c を n で縛らない）
    a = "           ExIn(c, n, Ex(s, conj(P.formula(ctx, s), MC.metacode(ctx, c, s),"
    m1 = types.ModuleType("ff1"); exec(compile(_mut(src, a, "           Ex(c, Ex(s, conj(P.formula(ctx, s), MC.metacode(ctx, c, s),"), "m1", "exec"), m1.__dict__)
    saved = FF.definable_set; FF.definable_set = m1.definable_set
    try: b, _ = test_defset()
    finally: FF.definable_set = saved
    print(f"変異 1（MetaCode(P) ∈ n を外す）：{b} 件の不一致を検出"); n += bool(b)
    # 2. 反復の回数を 9 回にする
    m2 = types.ModuleType("ff2"); exec(compile(_mut(src, "def iterate10(ctx, a, x, times=10):", "def iterate10(ctx, a, x, times=9):"), "m2", "exec"), m2.__dict__)
    saved = FF.iterate10; FF.iterate10 = m2.iterate10
    try: b, _ = test_iter()
    finally: FF.iterate10 = saved
    print(f"変異 2（反復を 9 回にする）：{b} 件の不一致を検出"); n += bool(b)
    return 0 if n == 2 else 1

if __name__ == "__main__":
    import resource; resource.setrlimit(resource.RLIMIT_AS, (6_000_000_000, 6_000_000_000))
    b = main()
    if "--mutation" in sys.argv: b += mutation()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)
