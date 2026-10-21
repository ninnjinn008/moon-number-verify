"""
structure.py の検証（縮めた有限の例）。

- vstage：λ = 0〜4 で、D = V_λ のときだけ真。宇宙には正しい段階の関数 R と、1 段ずらした偽の R を入れる。
- e_restrict：D = V_3 で、∈ の制限の正しい表は受理、1 組の過不足がある表は拒否。
- cn_ok：定数記号 c_0, c_1 だけが現れる宇宙で、{(c_0, ∅), (c_1, ∅)} は受理、欠けた表・値の違う表は拒否。
- fn_ok：D = V_3、α = 2、L を差し替え（L(0) = 1, L(1) = 2）。U(0) = V_1, U(1) = V_2、それ以外は ∅。
  f_{0,0}・f_{1,0} は ∅ を返し、Θ は D 上の関数。正しい表は受理、U の値・f の欠け・Θ の欠けを入れた偽の表は拒否。
  順序対・数・後者・空集合・4 つ組は代用関係（検証済み）、L は差し替え。
- 極限段階（vstage の極限の場合）は有限の例に現れないので、この検査では確かめられない。
"""
import itertools, sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair, to_nat
import structure as ST
import test_parse as TP

def raw(f): f.raw = True; return f
ORC = dict(TP.ORC)
LOW = {"pair", "empty", "succ", "numeral", "nat", "tuple4"}

def powerset(xs):
    xs = list(xs)
    return frozenset(frozenset(c) for r in range(len(xs) + 1) for c in itertools.combinations(xs, r))

Vs = [frozenset()]
for _ in range(4): Vs.append(powerset(Vs[-1]))

def graph(d): return frozenset(pair(a, b) for a, b in d.items())
def seq(vals): return frozenset(pair(nat(i), v) for i, v in enumerate(vals))
T4 = TP.tset

def test_vstage():
    ctx = Ctx(oracles=LOW, start=1); vl, vD = ctx.fresh(2)
    f = ST.vstage(ctx, vl, vD)
    bad = 0
    for lam in range(5):
        R = {nat(k): Vs[k] for k in range(lam + 1)}
        Rbad = dict(R); Rbad[nat(lam)] = Vs[lam - 1] if lam > 0 else Vs[1]
        D = transitive_closure({graph(R), graph(Rbad)} | set(Vs) | {nat(k) for k in range(6)})
        ev = Evaluator(D, ORC)
        for cand in range(5):
            if ev.ev(f, {vl: nat(lam), vD: Vs[cand]}) != (cand == lam): bad += 1
    return bad

def test_erestrict():
    ctx = Ctx(oracles=LOW, start=1); vD, vE = ctx.fresh(2)
    f = ST.e_restrict(ctx, vD, vE)
    Dm = Vs[3]
    E = {pair(a, b) for b in Dm for a in b}
    some = next(iter(E))
    cands = [frozenset(E), frozenset(E - {some}), frozenset(E | {pair(nat(0), nat(0))})]
    D = transitive_closure(set(cands) | {Dm})
    ev = Evaluator(D, ORC)
    return sum(ev.ev(f, {vD: Dm, vE: c}) != (k == 0) for k, c in enumerate(cands))

def test_cn():
    ctx = Ctx(oracles=LOW | {"sym"}, start=1); vC = ctx.fresh()
    f = ST.cn_ok(ctx, vC)
    c0, c1 = (6, 0, 0, 0), (6, 0, 1, 0)
    good = frozenset({pair(T4(c0), frozenset()), pair(T4(c1), frozenset())})
    cands = [good, frozenset({pair(T4(c0), frozenset())}), frozenset({pair(T4(c0), frozenset()), pair(T4(c1), nat(1))})]
    D = transitive_closure(set(cands) | {T4((7, 1, 0, 0)), T4((8, 2, 0, 1))} | {nat(k) for k in range(12)})
    ev = Evaluator(D, ORC)
    return sum(ev.ev(f, {vC: c}) != (k == 0) for k, c in enumerate(cands))

def test_fn():
    Dm, alpha = Vs[3], nat(2)
    Ltoy = {0: 1, 1: 2}
    orc = dict(ORC); orc["lam_of"] = raw(lambda x, lam: to_nat(x) in Ltoy and lam == nat(Ltoy[to_nat(x)]))
    U_, TH, F00, F10 = (8, 2, 0, 1), (8, 3, 0, 1), (8, 4, 0, 0), (8, 4, 0, 1)
    def uval(x):
        k = to_nat(x)
        return Vs[Ltoy[k]] if (k is not None and k < 2) else frozenset()
    entries = {}
    entries[(T4(F00), seq([]))] = frozenset()
    for x in Dm:
        entries[(T4(F10), seq([x]))] = frozenset()
        entries[(T4(U_), seq([x]))] = uval(x)
        entries[(T4(TH), seq([x]))] = frozenset()
    mk = lambda e: frozenset(pair(pair(t, w), v) for (t, w), v in e.items())
    good = mk(entries)
    xs = sorted(Dm, key=lambda z: len(z))
    bad1 = dict(entries); bad1[(T4(U_), seq([nat(1)]))] = Vs[1]                 # U(1) を V_1 に（本当は V_2）
    bad2 = dict(entries); del bad2[(T4(F10), seq([xs[-1]]))]                     # f_{1,0} の値が一つ欠ける
    bad3 = dict(entries); del bad3[(T4(TH), seq([xs[0]]))]                       # Θ が全域でない
    bad4 = dict(entries); bad4[(T4(U_), seq([nat(2)]))] = Vs[2]                 # 2 ∉ α なのに ∅ でない
    cands = [good, mk(bad1), mk(bad2), mk(bad3), mk(bad4)]
    Rgraphs = [graph({nat(k): Vs[k] for k in range(l + 1)}) for l in range(4)]
    Ths = [frozenset(pair(x, frozenset()) for x in Dm), frozenset(pair(x, frozenset()) for x in Dm if x != xs[0])]
    D = transitive_closure(set(cands) | set(Rgraphs) | set(Ths) | {Dm} | set(Vs[:4]) | {nat(k) for k in range(12)})
    ctx = Ctx(oracles=LOW | {"lam_of"}, start=1); vF, vD, va = ctx.fresh(3)
    f = ST.fn_ok(ctx, vF, vD, va)
    res = []
    for k, c in enumerate(cands):
        ev = Evaluator(D, orc)
        res.append(ev.ev(f, {vF: c, vD: Dm, va: alpha}))
    return sum(r != (k == 0) for k, r in enumerate(res)), res

def main():
    b = test_vstage(); print(f"vstage：λ = 0〜4 × 候補 5 個で {'すべて一致' if b == 0 else str(b) + ' 件の不一致'}")
    b2 = test_erestrict(); print(f"e_restrict：{'すべて一致' if b2 == 0 else str(b2) + ' 件の不一致'}")
    b3 = test_cn(); print(f"cn_ok：{'すべて一致' if b3 == 0 else str(b3) + ' 件の不一致'}")
    b4, res = test_fn(); print(f"fn_ok：正しい表と偽の表 4 個で {'すべて一致' if b4 == 0 else str(b4) + ' 件の不一致'}（判定 {res}）")
    return b + b2 + b3 + b4

if __name__ == "__main__":
    import resource; resource.setrlimit(resource.RLIMIT_AS, (6_000_000_000, 6_000_000_000))
    b = main()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)
