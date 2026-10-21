"""
順序対の判定 pair(p, a, b) の検証（改訂29）。

1. 推移的な有限集合 U = V_3 ∪ {必要な順序対} の上で、すべての p, a, b ∈ U について、
   pair の判定が p = {{a},{a,b}} と一致すること（総当たり）。
2. 「宇宙が {a} や {a,b} を含まない」場合の回帰テスト（別の AI による審査の反例）：
   宇宙 V_2、a = V_1、p = ∅ で、旧版は真（偽の陽性）、新版は偽になること。
   さらに V_3 の上で、宇宙の外にある {a} や {a,b} が原因の偽の陽性を、すべての p, a, b について調べる。
新版は Δ0 式なので、推移的な宇宙のどの元についても判定は真の意味と一致する（原理 A）。
"""
import itertools, sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair
import arith as A

def powerset(xs):
    xs = list(xs)
    return [frozenset(c) for r in range(len(xs) + 1) for c in itertools.combinations(xs, r)]
def V(n):
    v = set()
    for _ in range(n): v = set(powerset(v))
    return frozenset(v)

def check(build, U):
    ctx = Ctx(start=1); vp, va, vb = ctx.fresh(3)
    f = build(ctx, vp, va, vb)
    ev = Evaluator(U)
    bad = []
    for a in U:
        for b in U:
            for p in U:
                if ev.ev(f, {vp: p, va: a, vb: b}) != (p == pair(a, b)): bad.append((p, a, b))
    return bad

def main():
    V2, V3 = V(2), V(3)
    U = transitive_closure(set(V3) | {pair(a, b) for a in V3 for b in V3})
    b1 = check(A.pair, U)
    print(f"新版：宇宙 {len(U)} 元、{len(U) ** 3:,} 通りで {'すべて一致' if not b1 else str(len(b1)) + ' 件の不一致'}")
    ctx = Ctx(start=1); vp, va, vb = ctx.fresh(3)
    a = V(1); p = frozenset()
    old = Evaluator(V2).ev(A.pair_old(ctx, vp, va, vb), {vp: p, va: a, vb: a})
    new = Evaluator(V2).ev(A.pair(ctx, vp, va, vb), {vp: p, va: a, vb: a})
    print(f"審査の反例（宇宙 V_2、a = V_1、p = ∅）：旧版 {old}、新版 {new}")
    b_old = check(A.pair_old, V3); b_new = check(A.pair, V3)
    print(f"宇宙 V_3（順序対を補わない）：旧版の不一致 {len(b_old)} 件、新版の不一致 {len(b_new)} 件")
    return len(b1) + int(new) + len(b_new) + int(not old) + int(not b_old)

if __name__ == "__main__":
    b = main()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)
