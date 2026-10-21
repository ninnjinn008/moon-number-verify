"""
算術・Encode の式の記号数を、計数条件を固定して出力する。

計数条件：
- Ctx(start=1) で文脈を作る（変数番号 0 は空けておく）。
- 部品の引数として、その部品の引数の個数だけ ctx.fresh() で変数を確保する（番号 1, 2, …）。
- その後、部品の内部の束縛変数を順に確保する。
変数番号の割当てが変われば記号数も変わる（プライムの数が変わるため）。
"""
from fol import Ctx, length, render, free, has_oracle, ALPHABET
import arith as A

PARTS = [
    ("hyper(n,a,b,c)", 4, A.hyper),
    ("add(a,b,c)", 3, A.add),
    ("mul(a,b,c)", 3, A.mul),
    ("exp(a,b,c)", 3, A.exp),
    ("prime(p)", 1, A.prime),
    ("nth_prime(i,p)", 2, A.nth_prime),
    ("encode(s,c)", 2, A.encode),
]

if __name__ == "__main__":
    print("計数条件：Ctx(start=1)、引数は番号 1 から順に確保")
    for name, k, build in PARTS:
        ctx = Ctx(start=1)
        args = [ctx.fresh() for _ in range(k)]
        f = build(ctx, *args)
        assert not has_oracle(f)
        assert free(f) == set(args), (name, free(f), args)
        n = length(f)
        if n < 3_000_000:
            st = render(f)
            assert len(st) == n and set(st) <= ALPHABET
        print(f"{name:16s} {n:>12,} 記号   最大の変数番号 {ctx.n - 1}")
