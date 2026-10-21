"""
inacc_seq.py の検証。本物の ω・ε0・到達不能基数は有限の宇宙に入らないので、次のように縮めて確かめる。

- O：名前の範囲 W を、CNF の値が有限になる名前（0〜N−1 のうち）に限る。W の中で、各名前 i の値より小さい値を
  もつ名前がそろっていれば、O(i) は自然数 CNF(i) にならなければならない。正しい表は受理され、
  値を一つずらした偽の表はすべて拒否されることを確かめる。比較 cnf_lt は代用関係（test_cnf.py で検証済み）。
- L：「到達不能」を有限順序数の集合 S への所属に差し替え、定義域 E = 有限順序数 m とする。
  L(β) は S の β 番目の元にならなければならない。正しい表は受理され、偽の表は拒否されることを確かめる。
"""
import itertools, random, sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair, to_nat
import inacc_seq as IS
import test_cnf as TC

def raw(f): f.raw = True; return f
ORC = {
    "pair": raw(lambda p, a, b: p == pair(a, b)),
    "empty": raw(lambda a: a == frozenset()),
    "succ": raw(lambda b, c: c == (b | {b})),
    "numeral": raw(lambda k, v: v == nat(int(k))),
    "cnf_cmp": lambda i, k, c: TC.cmp_ref(i, k) == c,
}
LOW = {"pair", "empty", "succ", "numeral", "cnf_cmp"}

def finite_value(i):
    """CNF(i) が有限なら自然数の値、そうでなければ None。"""
    o = TC.CNF(i)
    return len(o) if all(e == () for e in o) else None

def graph(d): return frozenset(pair(a, b) for a, b in d.items())

def test_O(N=40, n_decoy=30, seed=1, mod=IS):
    W = [i for i in range(N) if finite_value(i) is not None]
    vals = {i: finite_value(i) for i in W}
    assert all(set(range(v)) <= set(vals.values()) for v in vals.values()), "W に足りない値がある"
    Of = {nat(i): nat(vals[i]) for i in W}
    rnd = random.Random(seed)
    decoys = []
    for _ in range(n_decoy):
        i = rnd.choice(W); d = dict(Of)
        d[nat(i)] = nat(vals[i] + rnd.choice([1, -1])) if vals[i] > 0 else nat(1)
        decoys.append(d)
    decoys.append({k: v for k, v in Of.items() if k != nat(W[-1])})          # 定義域が欠けた表
    Wset = frozenset(nat(i) for i in W)
    D = transitive_closure({graph(Of), Wset} | {graph(d) for d in decoys} | {nat(k) for k in range(max(vals.values()) + 3)})
    ctx = Ctx(oracles=LOW, start=1); vO, vW = ctx.fresh(2)
    f = mod.o_ok(ctx, vO, vW)
    ev = Evaluator(D, ORC)
    bad = int(not ev.ev(f, {vO: graph(Of), vW: Wset}))
    accepted = sum(ev.ev(f, {vO: graph(d), vW: Wset}) for d in decoys)
    return bad, accepted, len(W), sorted(set(vals.values()))

def test_L(S=(2, 4, 5, 7, 9, 11), m=5, n_decoy=20, seed=2, mod=IS):
    Sset = set(S)
    ORC2 = dict(ORC); ORC2["inaccessible"] = raw(lambda x: to_nat(x) in Sset)
    Lf = {nat(b): nat(S[b]) for b in range(m)}
    rnd = random.Random(seed)
    decoys = []
    for _ in range(n_decoy):
        b = rnd.randrange(m); d = dict(Lf)
        d[nat(b)] = nat(rnd.choice([x for x in range(13) if x != S[b]]))
        decoys.append(d)
    E = nat(m)
    D = transitive_closure({graph(Lf), E} | {graph(d) for d in decoys} | {nat(k) for k in range(14)})
    ctx = Ctx(oracles=LOW | {"inaccessible"}, start=1); vL, vE = ctx.fresh(2)
    f = mod.lam_ok(ctx, vL, vE)
    ev = Evaluator(D, ORC2)
    bad = int(not ev.ev(f, {vL: graph(Lf), vE: E}))
    accepted = sum(ev.ev(f, {vL: graph(d), vE: E}) for d in decoys)
    return bad, accepted

def main():
    b1, a1, nW, vs = test_O()
    print(f"O：名前 {nW} 個（値 {vs}）で、正しい表 {'受理' if not b1 else '拒否（不一致）'}、偽の表 31 個のうち受理 {a1} 個")
    b2, a2 = test_L()
    print(f"L：到達不能の代わりに S = (2, 4, 5, 7, 9, 11)、定義域 5 で、正しい表 {'受理' if not b2 else '拒否（不一致）'}、偽の表 20 個のうち受理 {a2} 個")
    return b1 + a1 + b2 + a2

def _mut(src, old, new):
    """変異版のソース。置換する箇所がちょうど一か所あることを確かめる（置換の空振りで変異テストが素通りしないように）。"""
    assert src.count(old) == 1, f"変異させる箇所が {src.count(old)} 個（1 個であるべき）: {old.strip()[:60]}"
    return src.replace(old, new)

def mutation():
    import types
    n = 0
    src = open(IS.__file__, encoding="utf-8").read()
    # O：上向きの条件（小さい名前の値がすべて O(i) に入る）を外す
    a = "        return And(down, up)"
    m1 = types.ModuleType("is_bad1"); exec(compile(_mut(src, a, "        return down"), "b1", "exec"), m1.__dict__)
    _, acc, _, _ = test_O(mod=m1)
    # L：最小性の条件を外す
    b = "        return conj(OR.inaccessible(ctx, lam), above, least)"
    m2 = types.ModuleType("is_bad2"); exec(compile(_mut(src, b, "        return conj(OR.inaccessible(ctx, lam), above)"), "b2", "exec"), m2.__dict__)
    _, acc2 = test_L(mod=m2)
    print(f"変異テスト：O の上向きの条件を外した版で偽の表を {acc} 個受理、L の最小性を外した版で {acc2} 個受理"
          + ("" if acc and acc2 else "　※検出できていないものがある"))
    return 0 if acc and acc2 else 1

if __name__ == "__main__":
    import resource; resource.setrlimit(resource.RLIMIT_AS, (6_000_000_000, 6_000_000_000))
    b = main()
    if "--mutation" in sys.argv: b += mutation()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)
