"""
名前から本物の順序数を作る O と、到達不能基数の列 L。

■ O：名前（自然数）から順序数へ
  O(i) = { O(k) : k ∈ ω, CNF(k) < CNF(i) }
  フォン・ノイマン順序数は自分より小さい順序数の集合なので、CNF が ε0 への全射であることから、
  CNF(i) の値の大きさに関する帰納法で O(i) = CNF(i)（本物の順序数）となる。
  O は ω 上の関数で、値は ε0 未満の順序数なので V_κ に属する。存在と一意性は ε0 上の帰納法による。

  o_ok(Of, W)：Of は W 上の関数で、各 i ∈ W について上の等式が W の中で成り立つ（本番では W = ω）。

■ L：順序数から到達不能基数へ
  L(β) = 「すべての γ < β について L(γ) より大きい」最小の到達不能基数
  （= β 番目の到達不能基数 λ_β）。定義域 E は ε0（= O の値域。ε0 は推移的なので β ⊆ E）。
  κ が Mahlo なので到達不能基数は κ の下で非有界であり、κ は正則なので L は存在し、L ∈ V_κ。

  lam_ok(Lf, E)：Lf は E 上の関数で、各 β ∈ E について L(β) は到達不能、γ < β なら L(γ) < L(β)、
                 L(β) より小さい到達不能基数 μ はどれも、ある γ < β について μ ≤ L(γ)。
"""
from fol import Oracle, In, Eq, And, Not, Or, Imp, Ex, All, AllIn, ExIn, conj, disj
import arith as A
import ordinals as OR
import cnf as CN

def o_ok(ctx, Of, W):
    """Of は W 上の関数で、O(i) = { O(k) : k ∈ W, CNF(k) < CNF(i) }。"""
    if ctx.use_oracle("o_ok"):
        return Oracle("o_ok", [Of, W])
    i, k, y = ctx.fresh(3)
    def value_ok(x):                       # x = O(i)
        down = AllIn(y, x, ExIn(k, W, And(CN.cnf_lt(ctx, k, i), A.lookup(ctx, Of, k, lambda ok: Eq(ok, y)))))
        up = AllIn(k, W, Imp(CN.cnf_lt(ctx, k, i), A.lookup(ctx, Of, k, lambda ok: In(ok, x))))
        return And(down, up)
    q, q1, q2 = ctx.fresh(3)
    is_func = conj(
        AllIn(q, Of, A.pair_parts(ctx, q, lambda a_, b_: In(a_, W))),
        A.all_pairs(ctx, Of, lambda _1, a1, b1: A.all_pairs(ctx, Of, lambda _2, a2, b2:
            Imp(Eq(a1, a2), Eq(b1, b2)))))
    return And(is_func, AllIn(i, W, A.lookup(ctx, Of, i, value_ok)))

def ord_of(ctx, i, x):
    """x = O(i) = 順序数 CNF(i)。"""
    if ctx.use_oracle("ord_of"):
        return Oracle("ord_of", [i, x])
    w, Of = ctx.fresh(2)
    return Ex(w, And(OR.is_omega(ctx, w), Ex(Of, And(o_ok(ctx, Of, w), A.lookup(ctx, Of, i, lambda v: Eq(v, x))))))

def lam_ok(ctx, Lf, E):
    """Lf は E 上の関数で、L(β) は β 番目の到達不能基数。"""
    if ctx.use_oracle("lam_ok"):
        return Oracle("lam_ok", [Lf, E])
    beta, g, mu = ctx.fresh(3)
    def value_ok(lam):                     # lam = L(β)
        above = AllIn(g, beta, A.lookup(ctx, Lf, g, lambda lg: In(lg, lam)))
        least = AllIn(mu, lam, Imp(OR.inaccessible(ctx, mu),
                      ExIn(g, beta, A.lookup(ctx, Lf, g, lambda lg: Or(In(mu, lg), Eq(mu, lg))))))
        return conj(OR.inaccessible(ctx, lam), above, least)
    q = ctx.fresh()
    is_func = conj(
        AllIn(q, Lf, A.pair_parts(ctx, q, lambda a_, b_: In(a_, E))),
        A.all_pairs(ctx, Lf, lambda _1, a1, b1: A.all_pairs(ctx, Lf, lambda _2, a2, b2:
            Imp(Eq(a1, a2), Eq(b1, b2)))))
    return And(is_func, AllIn(beta, E, A.lookup(ctx, Lf, beta, value_ok)))

def eps0(ctx, E):
    """E = ε0 = O の値域（O は ω 上で o_ok を満たす関数）。"""
    if ctx.use_oracle("eps0"):
        return Oracle("eps0", [E])
    w, Of, y, i = ctx.fresh(4)
    rng = And(AllIn(y, E, ExIn(i, w, A.lookup(ctx, Of, i, lambda v: Eq(v, y)))),
              AllIn(i, w, A.lookup(ctx, Of, i, lambda v: In(v, E))))
    return Ex(w, And(OR.is_omega(ctx, w), Ex(Of, And(o_ok(ctx, Of, w), rng))))

def lam_of(ctx, beta, lam):
    """lam = L(β) = β 番目の到達不能基数（β < ε0）。"""
    if ctx.use_oracle("lam_of"):
        return Oracle("lam_of", [beta, lam])
    E, Lf = ctx.fresh(2)
    return Ex(E, And(eps0(ctx, E), Ex(Lf, And(lam_ok(ctx, Lf, E), A.lookup(ctx, Lf, beta, lambda v: Eq(v, lam))))))
