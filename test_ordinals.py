"""
ordinals.py の検証。到達不能基数は無限なので有限の宇宙には現れない。ここで確かめるのは、
各判定式が**定義を正しく書き写しているか**であり、有限の場合について定義どおりの総当たりと照合する。

- ordinal：V_3 の全元と有限順序数で、「推移的かつ元も推移的」の総当たりと照合。
- func / bij：小さな集合の間の全関係について、関数・全単射の定義と照合。
- regular / strong_limit：有限順序数 n ≤ 5 について、定義（すべての β < n と f : β → n、すべての β < n と |P(β)|）
  を Python で総当たりした値と照合。宇宙には必要な関数・冪集合・全単射をすべて入れる。
- is_omega / inaccessible：有限の宇宙には ω がないので、すべて偽になることを確かめる（弱い検査）。
"""
import itertools, sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair
import ordinals as OR

def raw(f): f.raw = True; return f
# 順序対・空集合・後者は検証済み（test_semantics.py・test_arith.py）なので代用関係に差し替える
ORC = {"pair": raw(lambda p, a, b: p == pair(a, b)),
       "empty": raw(lambda a: a == frozenset()),
       "succ": raw(lambda b, c: c == (b | {b}))}
LOW = {"pair", "empty", "succ"}

def powerset(xs):
    xs = list(xs)
    return [frozenset(c) for r in range(len(xs) + 1) for c in itertools.combinations(xs, r)]

def V(n):
    v = set()
    for _ in range(n): v = set(powerset(v))
    return v

def graph(f): return frozenset(pair(a, b) for a, b in f.items())

def all_funcs(A, B):
    A = list(A); B = list(B)
    return [dict(zip(A, vals)) for vals in itertools.product(B, repeat=len(A))]

def regular_ref(n):
    for beta in range(n):
        for f in all_funcs(range(beta), range(n)):
            if not any(all(f[d] < g for d in range(beta)) for g in range(n)):
                return False
    return True

def strong_limit_ref(n):
    return all(any(2 ** beta == g for g in range(n)) for beta in range(n))

def main():
    bad = 0
    # ordinal
    ctx = Ctx(oracles=LOW, start=1); vx = ctx.fresh()
    f_ord = OR.ordinal(ctx, vx)
    U = V(4) | {nat(k) for k in range(6)} | {frozenset({nat(2)}), frozenset({nat(0), nat(2)}), frozenset({nat(1), nat(2)})}
    D = transitive_closure(U)
    ev = Evaluator(D, ORC)
    trans = lambda a: all(u in a for z in a for u in z)
    for a in D:
        want = trans(a) and all(trans(z) for z in a)
        if ev.ev(f_ord, {vx: a}) != want: bad += 1
    print(f"ordinal：{len(D)} 個の集合で {'すべて一致' if bad == 0 else str(bad) + ' 件の不一致'}")

    # func / bij
    b0 = bad
    ctx = Ctx(oracles=LOW, start=1); vf, vA, vB = ctx.fresh(3)
    f_func = OR.func(ctx, vf, vA, vB); f_bij = OR.bij(ctx, vf, vA, vB)
    Aset, Bset = nat(2), frozenset({nat(0), nat(3)})
    rels = [frozenset(c) for r in range(0, 4) for c in itertools.combinations([pair(a, b) for a in Aset for b in Bset | {nat(1)}], r)]
    D = transitive_closure(set(rels) | {Aset, Bset, nat(4)})
    ev = Evaluator(D, ORC)
    for R in rels:
        pairs = [(a, b) for a in Aset for b in Bset | {nat(1)} if pair(a, b) in R]
        is_f = all(b in Bset for _, b in pairs) and sorted(a for a, _ in pairs) == sorted(Aset) and len({a for a, _ in pairs}) == len(pairs)
        is_b = is_f and len({b for _, b in pairs}) == len(pairs) and {b for _, b in pairs} == set(Bset)
        if ev.ev(f_func, {vf: R, vA: Aset, vB: Bset}) != is_f: bad += 1
        if ev.ev(f_bij, {vf: R, vA: Aset, vB: Bset}) != is_b: bad += 1
    print(f"func / bij：関係 {len(rels)} 個で {'すべて一致' if bad == b0 else str(bad - b0) + ' 件の不一致'}")

    # regular / strong_limit
    b0 = bad
    ctx = Ctx(oracles=LOW, start=1); vl = ctx.fresh()
    f_reg = OR.regular(ctx, vl); f_sl = OR.strong_limit(ctx, vl); f_om = OR.is_omega(ctx, vl); f_in = OR.inaccessible(ctx, vl)
    N = 5
    sets = {nat(k) for k in range(N + 4)}
    for n in range(N + 1):
        for beta in range(n):
            for f in all_funcs([nat(d) for d in range(beta)], [nat(k) for k in range(n)]):
                sets.add(graph(f))
    for beta in range(3):        # n ≤ 5 では 2^β < n となりうるのは β ≤ 2 だけ
        P = powerset(nat(beta)); sets.add(frozenset(P))
        g = len(P)
        if g < N + 4:
            for perm in itertools.permutations(range(g)):
                sets.add(frozenset(pair(P[i], nat(perm[i])) for i in range(g)))
    D = transitive_closure(sets)
    for n in range(N + 1):
        ev = Evaluator(D, ORC)
        x = nat(n)
        r1, r2 = ev.ev(f_reg, {vl: x}), ev.ev(f_sl, {vl: x})
        if r1 != regular_ref(n): bad += 1; print("NG regular", n, r1)
        if r2 != strong_limit_ref(n): bad += 1; print("NG strong_limit", n, r2)
        if ev.ev(f_om, {vl: x}) or ev.ev(f_in, {vl: x}): bad += 1; print("NG ω/到達不能", n)
    refs = [(n, regular_ref(n), strong_limit_ref(n)) for n in range(N + 1)]
    print(f"regular / strong_limit / is_omega / inaccessible：n = 0〜{N}（宇宙 {len(D)} 元）で {'すべて一致' if bad == b0 else str(bad - b0) + ' 件の不一致'}")
    print(f"  参考（定義どおりの値）：{refs}")
    return bad

def mutation():
    """変異テスト：正則性で『上から抑える γ が λ 未満』を『γ が任意』に緩めた版（λ 自身も許す）。"""
    import types
    src = open(OR.__file__, encoding="utf-8").read()
    a = "    bounded = ExIn(g, lam, AllIn(d, beta, A.lookup(ctx, f, d, lambda v: In(v, g))))"
    assert src.count(a) == 1
    bad_mod = types.ModuleType("ord_bad")
    exec(compile(src.replace(a, "    bounded = Or(ExIn(g, lam, AllIn(d, beta, A.lookup(ctx, f, d, lambda v: In(v, g)))), AllIn(d, beta, A.lookup(ctx, f, d, lambda v: In(v, lam))))"), "ord_bad", "exec"), bad_mod.__dict__)
    ctx = Ctx(oracles=LOW, start=1); vl = ctx.fresh(); f = bad_mod.regular(ctx, vl)
    sets = {nat(k) for k in range(6)}
    for n in range(5):
        for beta in range(n):
            for fn in all_funcs([nat(d) for d in range(beta)], [nat(k) for k in range(n)]):
                sets.add(graph(fn))
    ev = Evaluator(transitive_closure(sets), ORC)
    n_bad = sum(ev.ev(f, {vl: nat(n)}) != regular_ref(n) for n in range(5))
    print(f"変異テスト（正則性の上界を λ まで許した版）: {n_bad} 件の不一致を検出" + ("" if n_bad else "　※検出できていない"))
    return 0 if n_bad else 1

if __name__ == "__main__":
    import resource; resource.setrlimit(resource.RLIMIT_AS, (6_000_000_000, 6_000_000_000))
    b = main()
    if "--mutation" in sys.argv: b += mutation()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)
