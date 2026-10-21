"""
原文の f と、巨大数庭園数 LNGN_I = f^10(10↑^10 10)。

■ 原文
  f(n)：i ∈ n かつ P ∈ Formula かつ MetaCode(P) ∈ n かつ Definable(m, i, P) を満たす i と P が存在するような
        m ∈ ℕ の総和。
  LNGN = f^10(10↑^10 10)。

■ 表し方
  struct_table(n, ST)  ：ST は n 上の関数で、ST(i) = ((D, E), (Cn, (Fn, Rel))) は struct_full(i, …) を満たす
                          （構造を i ごとに一度だけ導入し、以後は表を参照する）
  definable_set(n, ST, S)：S = { m ∈ ℕ : ∃i ∈ n ∃c ∈ n ∃P (P ∈ Formula ∧ c = MetaCode(P) ∧ ST(i) で P が m を定義する) }
  finite_sum(S, v)     ：S ⊆ K となる自然数 K と、R(0) = 0、R(k+1) = R(k) + (k ∈ S なら k、そうでなければ 0)
                          を満たす K+1 上の表 R があり、v = R(K)（K の取り方によらない）
  f_val(n, v)          ：v = f(n)
  iterate10(a, x)      ：G(0) = a、G(j+1) = f(G(j))（j < 10）を満たす 11 上の表 G があり、x = G(10)
  lngn(x)              ：x = f^10(H(12, 10, 10))、H はハイパー演算（10↑^10 10 = H(12, 10, 10)）
各 i ∈ n について struct_full を満たす構造はちょうど一つ（lorder.py）、各 (i, P) について Definable な m は
高々一つ（別紙 E 第 9 項）なので、S は有限で、f(n) は一意に定まる。表 ST の値は V_κ の元、S・R・G は
遺伝的有限なので、すべて M に属する。
"""
from fol import Oracle, In, Eq, And, Not, Or, Imp, Iff, Ex, All, AllIn, ExIn, conj, disj
import arith as A
import parse as P
import metacode as MC
import definable as DF
import lorder as LO

def _func_on(ctx, f, K):
    """f は K 上の関数（値は任意）。"""
    q, k = ctx.fresh(2)
    return conj(
        AllIn(q, f, A.pair_parts(ctx, q, lambda k_, a_: In(k_, K))),
        AllIn(k, K, A.lookup(ctx, f, k, lambda a_: Eq(a_, a_))),
        A.all_pairs(ctx, f, lambda _1, k1, a1: A.all_pairs(ctx, f, lambda _2, k2, a2:
            Imp(Eq(k1, k2), Eq(a1, a2)))))

def _struct_parts(ctx, x, body):
    """x = ((D, E), (Cn, (Fn, Rel))) のとき body(D, E, Cn, Fn, Rel)。"""
    return A.pair_parts(ctx, x, lambda de, rest: A.pair_parts(ctx, de, lambda D, E:
           A.pair_parts(ctx, rest, lambda Cn, fr: A.pair_parts(ctx, fr, lambda Fn, Rel:
           body(D, E, Cn, Fn, Rel)))))

def struct_table(ctx, n, ST):
    if ctx.use_oracle("struct_table"):
        return Oracle("struct_table", [n, ST])
    i = ctx.fresh()
    return And(_func_on(ctx, ST, n),
               AllIn(i, n, A.lookup(ctx, ST, i, lambda x: _struct_parts(ctx, x,
                   lambda D, E, Cn, Fn, Rel: LO.struct_full(ctx, i, D, E, Cn, Fn, Rel)))))

def definable(ctx, s, D, E, Cn, Fn, Rel, m):
    if ctx.use_oracle("definable"):
        return Oracle("definable", [s, D, E, Cn, Fn, Rel, m])
    return DF.definable_in(ctx, s, D, E, Cn, Fn, Rel, m)

def definable_set(ctx, n, ST, S):
    if ctx.use_oracle("definable_set"):
        return Oracle("definable_set", [n, ST, S])
    m, i, c, s = ctx.fresh(4)
    cond = ExIn(i, n, A.lookup(ctx, ST, i, lambda x: _struct_parts(ctx, x, lambda D, E, Cn, Fn, Rel:
           ExIn(c, n, Ex(s, conj(P.formula(ctx, s), MC.metacode(ctx, c, s),
                                 definable(ctx, s, D, E, Cn, Fn, Rel, m)))))))
    return All(m, Iff(In(m, S), And(A.nat(ctx, m), cond)))

def finite_sum(ctx, S, v):
    if ctx.use_oracle("finite_sum"):
        return Oracle("finite_sum", [S, v])
    K, K1, R, k, k1, x = ctx.fresh(6)
    def rec(k_, k1_):
        return A.lookup(ctx, R, k_, lambda a: A.lookup(ctx, R, k1_, lambda b: And(
            Imp(In(k_, S), A.add(ctx, a, k_, b)), Imp(Not(In(k_, S)), Eq(b, a)))))
    body = conj(_func_on(ctx, R, K1),
                Ex(x, And(A.empty(ctx, x), A.lookup(ctx, R, x, lambda a: A.empty(ctx, a)))),
                AllIn(k, K, AllIn(k1, K1, Imp(A.succ_of(ctx, k, k1), rec(k, k1)))),
                A.lookup(ctx, R, K, lambda a: Eq(a, v)))
    return Ex(K, conj(A.nat(ctx, K), AllIn(x, S, In(x, K)),
                      Ex(K1, And(A.succ_of(ctx, K, K1), Ex(R, body)))))

def f_val(ctx, n, v):
    """v = f(n)。"""
    if ctx.use_oracle("f_val"):
        return Oracle("f_val", [n, v])
    ST, S = ctx.fresh(2)
    return Ex(ST, And(struct_table(ctx, n, ST), Ex(S, And(definable_set(ctx, n, ST, S), finite_sum(ctx, S, v)))))

def iterate10(ctx, a, x, times=10):
    """x = f^times(a)。"""
    if ctx.use_oracle("iterate10"):
        return Oracle("iterate10", [a, x])
    t, t1, G, j, j1, z = ctx.fresh(6)
    body = conj(_func_on(ctx, G, t1),
                Ex(z, And(A.empty(ctx, z), A.lookup(ctx, G, z, lambda g0: Eq(g0, a)))),
                AllIn(j, t, AllIn(j1, t1, Imp(A.succ_of(ctx, j, j1),
                    A.lookup(ctx, G, j, lambda gj: A.lookup(ctx, G, j1, lambda gj1: f_val(ctx, gj, gj1)))))),
                A.lookup(ctx, G, t, lambda g: Eq(g, x)))
    return Ex(t, And(A.numeral(ctx, t, times), Ex(t1, And(A.succ_of(ctx, t, t1), Ex(G, body)))))

def lngn(ctx, x):
    """x = LNGN_I = f^10(10↑^10 10)。"""
    a, n12, n10 = ctx.fresh(3)
    num = Ex(n12, And(A.numeral(ctx, n12, 12), Ex(n10, And(A.numeral(ctx, n10, 10), A.hyper(ctx, n12, n10, n10, a)))))
    return Ex(a, And(num, iterate10(ctx, a, x)))
