"""
候補解釈 I の下での構造 U(α) を、充足関係 sat に渡せる五つの集合 (dom, E, Cn, Fn, Rel) として表す。

  vstage(λ, D)      ：D = V_λ（R(0) = ∅、R(β+1) = P(R(β))、極限では和集合、という関数 R の存在）
  e_restrict(D, E)  ：E = ∈ ↾ D（D は推移的）
  cn_ok(Cn)         ：すべての定数記号 c_i を ∅ と解釈する
  rel_empty(Rel)    ：∈ 以外の関係記号 r_{a,i} はすべて空関係（Rel = ∅）
  fn_ok(Fn, D, α)   ：関数記号の解釈
                        f_{a,i}：D^a の各引数の列に ∅ を返す
                        U      ：x が順序数で x ∈ α なら V_{L(x)}、そうでなければ ∅
                        Θ      ：D から D への関数（中身の <_L 最小の証人は未構成。下記 theta_ok を参照）
  struct_of(i, …)   ：α = O(i)、λ = L(α)、D = V_λ として、上の条件をすべて満たす

Θ について：原文の Henkin 公理を満たす Θ の解釈として、本書は「<_L で最小の証人」を採る（別紙 B）。
その形式化（構成可能宇宙 L の整列順序 <_L の定義）は未了であり、ここでは Θ の解釈を
「D 上の関数」という条件だけで受け取る（theta_ok は差し替え可能な部品）。
"""
from fol import Oracle, In, Eq, And, Not, Or, Imp, Iff, Ex, All, AllIn, ExIn, conj, disj
import arith as A
import parse as P
import ordinals as OR
import inacc_seq as IS

def vstage(ctx, lam, D):
    """D = V_λ。"""
    if ctx.use_oracle("vstage"):
        return Oracle("vstage", [lam, D])
    l1, R, g, y, b = ctx.fresh(5)
    def at_R(x, body):
        return A.lookup(ctx, R, x, body)
    def value_ok(gm, X):                   # X = R(γ)
        zero = Imp(A.empty(ctx, gm), A.empty(ctx, X))
        b0 = ctx.fresh()
        succ = AllIn(b0, gm, Imp(A.succ_of(ctx, b0, gm), at_R(b0, lambda Y: OR._power_of(ctx, X, Y))))
        limit = Imp(And(Not(A.empty(ctx, gm)), Not(OR.is_succ(ctx, gm))),
                    And(AllIn(y, X, ExIn(b, gm, at_R(b, lambda Y: In(y, Y)))),
                        AllIn(b, gm, at_R(b, lambda Y: AllIn(y, Y, In(y, X))))))
        return conj(zero, succ, limit)
    q = ctx.fresh()
    is_func = conj(
        AllIn(q, R, A.pair_parts(ctx, q, lambda a_, b_: In(a_, l1))),
        A.all_pairs(ctx, R, lambda _1, a1, b1: A.all_pairs(ctx, R, lambda _2, a2, b2:
            Imp(Eq(a1, a2), Eq(b1, b2)))))
    body = conj(is_func, AllIn(g, l1, at_R(g, lambda X: value_ok(g, X))), at_R(lam, lambda X: Eq(X, D)))
    return And(OR.ordinal(ctx, lam), Ex(l1, And(A.succ_of(ctx, lam, l1), Ex(R, body))))

def e_restrict(ctx, D, E):
    """E = { (a, b) : a, b ∈ D, a ∈ b }（D は推移的）。"""
    q, a, b = ctx.fresh(3)
    return And(AllIn(q, E, A.pair_parts(ctx, q, lambda a_, b_: conj(In(a_, D), In(b_, D), In(a_, b_)))),
               AllIn(b, D, AllIn(a, b, ExIn(q, E, A.pair(ctx, q, a, b)))))

def cn_ok(ctx, Cn):
    """Cn = { (c, ∅) : c は定数記号 }。"""
    if ctx.use_oracle("cn_ok"):
        return Oracle("cn_ok", [Cn])
    q, t, z = ctx.fresh(3)
    return And(AllIn(q, Cn, A.pair_parts(ctx, q, lambda t_, v_: conj(P.tuple4(ctx, t_), P.is_const(ctx, t_), A.empty(ctx, v_)))),
               All(t, Imp(And(P.tuple4(ctx, t), P.is_const(ctx, t)),
                          ExIn(q, Cn, Ex(z, And(A.empty(ctx, z), A.pair(ctx, q, t, z)))))))

def rel_empty(ctx, Rel):
    return A.empty(ctx, Rel)

def theta_ok(ctx, Th, D):
    """Θ の解釈 Th は D から D への関数（中身は未構成。差し替え可能な部品）。"""
    if ctx.use_oracle("theta_ok"):
        return Oracle("theta_ok", [Th, D])
    return OR.func(ctx, Th, D, D)

def _singleton_seq(ctx, w_, x_, one=None):
    """w = ⟨x⟩（長さ 1 の列で、第 0 成分が x）。"""
    one = one or ctx.fresh()
    z0 = ctx.fresh()
    return Ex(one, And(A.numeral(ctx, one, 1), And(P.seq_with(ctx, w_, one, lambda u: Eq(u, u)),
              Ex(z0, And(A.empty(ctx, z0), A.lookup(ctx, w_, z0, lambda u: Eq(u, x_)))))))

def theta_value(ctx, Fn, m, v):
    """((Θ, ⟨m⟩), v) ∈ Fn。"""
    r, tw, vv = ctx.fresh(3)
    def inner(tw_, v_):
        return And(Eq(v_, v), A.pair_parts(ctx, tw_, lambda t_, w_: And(P.sym(ctx, t_, 8, 3, 0, 1), _singleton_seq(ctx, w_, m))))
    return ExIn(r, Fn, A.pair_parts(ctx, r, inner))

def fn_ok(ctx, Fn, D, alpha, SU=None):
    """関数記号の解釈 Fn（Θ の部分は theta_ok に委ねる）。
    SU を与えると（改訂31）、U の値は構造そのもの：x が順序数で x ∈ α なら U(x) = SU(x)（構造の表 SU の値）。
    SU を与えないと（改訂30 までの版）、U(x) = V_{L(x)}（領域だけ）。原文の U2 を満たすのは SU を与えた版である。"""
    if ctx.use_oracle("fn_ok"):
        return Oracle("fn_ok", [Fn, D, alpha] + ([SU] if SU is not None else []))
    q, t, w, v, x, z, Th = ctx.fresh(7)
    is_U = lambda t_: P.sym(ctx, t_, 8, 2, 0, 1)
    is_Th = lambda t_: P.sym(ctx, t_, 8, 3, 0, 1)
    is_f = lambda t_: And(P.comp_is(ctx, t_, 0, 8), P.comp_is(ctx, t_, 1, 4))
    one = ctx.fresh()
    singleton_seq = lambda w_, x_: _singleton_seq(ctx, w_, x_, one)
    def u_value(x_, v_):                   # v = U(x)：x が順序数で x ∈ α なら V_{L(x)}、そうでなければ ∅
        lam = ctx.fresh()
        good = And(OR.ordinal(ctx, x_), In(x_, alpha))
        if SU is not None:
            return Or(And(good, A.lookup(ctx, SU, x_, lambda s_: Eq(s_, v_))),
                      And(Not(good), A.empty(ctx, v_)))
        return Or(And(good, Ex(lam, And(IS.lam_of(ctx, x_, lam), vstage(ctx, lam, v_)))),
                  And(Not(good), A.empty(ctx, v_)))
    # 1. Fn の元はすべて ((t, w), v) の形で、記号ごとの条件を満たす
    def entry(t_, w_, v_):
        f_case = conj(is_f(t_), P.comp(ctx, t_, 3, lambda ar: P.seq_with(ctx, w_, ar, lambda u: In(u, D))), A.empty(ctx, v_))
        U_case = conj(is_U(t_), ExIn(x, D, And(singleton_seq(w_, x), u_value(x, v_))))
        Th_case = conj(is_Th(t_), ExIn(x, D, And(singleton_seq(w_, x), In(v_, D))))
        return And(P.tuple4(ctx, t_), disj(f_case, U_case, Th_case))
    q1, r1, tw, s2 = ctx.fresh(4)
    shape = AllIn(q, Fn, A.pair_parts(ctx, q, lambda tw_, v_: A.pair_parts(ctx, tw_, lambda t_, w_: entry(t_, w_, v_))))
    # 2. 完全性：f_{a,i} は D^a のすべての列で、U は D のすべての元で定義されている
    f_total = All(t, Imp(And(P.tuple4(ctx, t), is_f(t)), P.comp(ctx, t, 3, lambda ar:
              All(w, Imp(P.seq_with(ctx, w, ar, lambda u: In(u, D)),
                         ExIn(q, Fn, A.pair_parts(ctx, q, lambda tw_, v_: A.pair(ctx, tw_, t, w))))))))
    U_total = All(t, Imp(And(P.tuple4(ctx, t), is_U(t)), AllIn(x, D, Ex(w, And(singleton_seq(w, x),
              ExIn(q, Fn, A.pair_parts(ctx, q, lambda tw_, v_: A.pair(ctx, tw_, t, w))))))))
    # 3. Θ の部分：Th = { (x, y) : ((Θ, ⟨x⟩), y) ∈ Fn } が theta_ok を満たす
    def fn_has_theta(x_, y_):             # ((Θ, ⟨x⟩), y) ∈ Fn
        def inner(tw_, v_):
            return And(Eq(v_, y_), A.pair_parts(ctx, tw_, lambda t_, w_: And(is_Th(t_), singleton_seq(w_, x_))))
        return ExIn(r1, Fn, A.pair_parts(ctx, r1, inner))
    def theta_entry_in_Th(tw_, v_):        # Fn の Θ の元は Th に載っている
        def inner(t_, w_):
            return Imp(is_Th(t_), ExIn(x, D, And(singleton_seq(w_, x), ExIn(q, Th, A.pair(ctx, q, x, v_)))))
        return A.pair_parts(ctx, tw_, inner)
    th_def = And(AllIn(q, Th, A.pair_parts(ctx, q, fn_has_theta)),
                 AllIn(r1, Fn, A.pair_parts(ctx, r1, theta_entry_in_Th)))
    Th_part = Ex(Th, And(th_def, theta_ok(ctx, Th, D)))
    # 4. 関数性：同じ (t, w) に二つの値はない
    func = A.all_pairs(ctx, Fn, lambda _1, a1, b1: A.all_pairs(ctx, Fn, lambda _2, a2, b2: Imp(Eq(a1, a2), Eq(b1, b2))))
    return conj(shape, f_total, U_total, Th_part, func)

def struct_of(ctx, i, D, E, Cn, Fn, Rel):
    """(D, E, Cn, Fn, Rel) は候補解釈 I の下での U(CNF(i))（Θ の中身を除く）。"""
    alpha, lam = ctx.fresh(2)
    return Ex(alpha, And(IS.ord_of(ctx, i, alpha), Ex(lam, conj(
        IS.lam_of(ctx, alpha, lam), vstage(ctx, lam, D),
        e_restrict(ctx, D, E), cn_ok(ctx, Cn), rel_empty(ctx, Rel), fn_ok(ctx, Fn, D, alpha)))))

# ---------- 構造の符号（改訂31） ----------
def struct_parts(ctx, x, body):
    """x = ((D, E), (Cn, (Fn, Rel))) のとき body(D, E, Cn, Fn, Rel)。構造を一つの集合として表す本書の約束。"""
    return A.pair_parts(ctx, x, lambda de, rest: A.pair_parts(ctx, de, lambda D, E:
           A.pair_parts(ctx, rest, lambda Cn, fr: A.pair_parts(ctx, fr, lambda Fn, Rel:
           body(D, E, Cn, Fn, Rel)))))
