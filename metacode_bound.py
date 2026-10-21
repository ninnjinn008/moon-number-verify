"""
別紙 B「解釈全体にわたる非有界性」で使う式 P ≡ (x_0 = c_0) の MetaCode の上からの評価。

原文の符号（ω^4 未満の順序数 ω^3·a3 + ω^2·a2 + ω·a1 + a0 を 4 つ組 (a0,a1,a2,a3) とみなす）：
  ⊥=0, →=1, ¬=2, ∃=3, (=4, )=5, Constant=6, Variable=7, Function=8, Relation=9,
  Number=ω, Index=ω^2, Arity=ω^3
  c_i = (6,0,i,0), x_i = (7,1,i,0), U = (8,2,0,1), Θ = (8,3,0,1), f_{a,i} = (8,4,i,a),
  ∈ = (9,5,0,2), r_{a,i} = (9,6,i,a)
Encode(a) = -1 + 2^h ∏_{i<h} p_{i+1}^{a_i}。記号の符号は Encode(4 つ組)、式の符号 MetaCode は
記号の符号の列にもう一度 Encode を施したもの。

等号 = は原文で略記とされ、展開の仕方は明記されていない。そこで展開後の記号数 L と、
各記号の 4 つ組の成分の上限を大きめに仮定して、上から抑える。
"""
from math import log10

def primes(n):
    ps, k = [], 2
    while len(ps) < n:
        if all(k % p for p in ps if p * p <= k):
            ps.append(k)
        k += 1
    return ps

def log10_encode(tup, P):
    """log10(Encode(tup) + 1)"""
    return len(tup) * log10(2) + sum(a * log10(P[i + 1]) for i, a in enumerate(tup))

P = primes(5000)

# 実際の記号の符号（例）
for name, t in [("x_0", (7, 1, 0, 0)), ("c_0", (6, 0, 0, 0)), ("∈", (9, 5, 0, 2))]:
    v = 2 ** 4
    for i, a in enumerate(t):
        v *= P[i + 1] ** a
    print(f"記号 {name}: 4 つ組 {t} → 符号 {v - 1}")

# 仮定：展開後の記号数 L ≤ 1000、各成分 a0 ≤ 9, a1 ≤ 6, 変数・定数の添字 a2 ≤ 10, a3 ≤ 2
L = 1000
worst = (9, 6, 10, 2)
lg_sym = log10_encode(worst, P)              # 1 記号の符号 + 1 の log10 の上限
sym_max = 10 ** lg_sym                      # 1 記号の符号の上限（実数で）
# MetaCode + 1 = 2^L ∏_{k<L} p_{k+1}^{s_k} ≤ 2^L · p_L^{L · sym_max}
lg_meta = L * log10(2) + L * sym_max * log10(P[L])
print(f"1 記号の符号の上限：10^{lg_sym:.2f}")
print(f"MetaCode(P) の上限：10^(10^{log10(lg_meta):.2f})")
print("比較：10↑↑4 = 10^(10^(10^10))。10^(10^{:.2f}) < 10↑↑4 ≤ 10↑↑10 ≤ 10↑^10 10".format(log10(lg_meta)))
assert log10(lg_meta) < 10 ** 10
