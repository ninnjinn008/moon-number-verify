"""
順序数・関数・到達不能基数を、M の純粋な {∈,=} 一階式として表す。

M = V_{κ+1} は推移的で、κ 未満の順序数 λ について、λ の部分集合・λ 上の関数・P(β)（β < λ）とその間の
全単射はすべて V_κ に属する。よって以下の判定は、λ < κ について M の中で計算しても真の値と一致する（絶対的）。

  ordinal(x)      ：x は推移的で、その元も推移的（基礎の公理の下で順序数）
  is_omega(w)     ：w = ω（0 でも後者でもない最小の順序数。元はすべて 0 か後者）
  func(f, A, B)   ：f は A から B への全域関数（順序対の集合）
  bij(f, A, B)    ：f は A から B への全単射
  regular(λ)      ：λ 未満の任意の β と任意の関数 f : β → λ について、f の値は λ 未満のある γ で上から抑えられる
  strong_limit(λ) ：λ 未満の任意の β について、P(β) と全単射で結ばれる γ < λ がある（|P(β)| < λ）
  inaccessible(λ) ：λ は順序数、ω ∈ λ、正則、強極限
"""
from fol import Oracle, In, Eq, And, Not, Or, Imp, Iff, Ex, All, AllIn, ExIn, conj, disj
import arith as A

def transitive(ctx, a):
    z, u = ctx.fresh(2)
    return AllIn(z, a, AllIn(u, z, In(u, a)))

def ordinal(ctx, x):
    if ctx.use_oracle("ordinal"):
        return Oracle("ordinal", [x])
    z = ctx.fresh()
    return And(transitive(ctx, x), AllIn(z, x, transitive(ctx, z)))

def is_succ(ctx, z):
    w = ctx.fresh()
    return ExIn(w, z, A.succ_of(ctx, w, z))

def is_omega(ctx, w):
    """w = ω：w は順序数で、0 でも後者でもなく、w の元はすべて 0 か後者。"""
    if ctx.use_oracle("omega"):
        return Oracle("omega", [w])
    z = ctx.fresh()
    return conj(ordinal(ctx, w), Not(A.empty(ctx, w)), Not(is_succ(ctx, w)),
                AllIn(z, w, Or(A.empty(ctx, z), is_succ(ctx, z))))

def func(ctx, f, Adom, B):
    """f は Adom から B への全域関数。"""
    q, a, b, b2, q2 = ctx.fresh(5)
    return conj(
        AllIn(q, f, A.pair_parts(ctx, q, lambda a_, b_: And(In(a_, Adom), In(b_, B)))),
        AllIn(a, Adom, A.lookup(ctx, f, a, lambda b_: In(b_, B))),
        A.all_pairs(ctx, f, lambda _1, a1, b1: A.all_pairs(ctx, f, lambda _2, a2, b2_:
            Imp(Eq(a1, a2), Eq(b1, b2_)))))

def bij(ctx, f, Adom, B):
    """f は Adom から B への全単射。"""
    b = ctx.fresh()
    a = ctx.fresh()
    onto = AllIn(b, B, ExIn(a, Adom, A.lookup(ctx, f, a, lambda v: Eq(v, b))))
    inj = A.all_pairs(ctx, f, lambda _1, a1, b1: A.all_pairs(ctx, f, lambda _2, a2, b2_:
            Imp(Eq(b1, b2_), Eq(a1, a2))))
    return conj(func(ctx, f, Adom, B), onto, inj)

def regular(ctx, lam):
    if ctx.use_oracle("regular"):
        return Oracle("regular", [lam])
    beta, f, g, d = ctx.fresh(4)
    bounded = ExIn(g, lam, AllIn(d, beta, A.lookup(ctx, f, d, lambda v: In(v, g))))
    return AllIn(beta, lam, All(f, Imp(func(ctx, f, beta, lam), bounded)))

def strong_limit(ctx, lam):
    if ctx.use_oracle("strong_limit"):
        return Oracle("strong_limit", [lam])
    beta, pb, g, h = ctx.fresh(4)
    return AllIn(beta, lam, Ex(pb, And(_power_of(ctx, pb, beta),
                 ExIn(g, lam, Ex(h, bij(ctx, h, pb, g))))))

def _power_of(ctx, a, b):                 # a = P(b)
    # b ∈ a は P(b) なら必ず成り立つ（評価の際に候補を早く絞るために先に置く。意味は変わらない）
    z, u = ctx.fresh(2)
    return And(In(b, a), All(z, Iff(In(z, a), AllIn(u, z, In(u, b)))))

def inaccessible(ctx, lam):
    if ctx.use_oracle("inaccessible"):
        return Oracle("inaccessible", [lam])
    w = ctx.fresh()
    return conj(ordinal(ctx, lam),
                Ex(w, And(is_omega(ctx, w), In(w, lam))),
                regular(ctx, lam),
                strong_limit(ctx, lam))
