"""
LNGN の形式言語 ┌L┐ の整形判定 Formula(s) と Formula₋(s) を、M の純粋な {∈,=} 一階式として表す。

■ 記号（原文の符号。4 つ組 (a0, a1, a2, a3) は順序数 ω^3·a3 + ω^2·a2 + ω·a1 + a0）
  ⊥ (0,0,0,0)  → (1,0,0,0)  ¬ (2,0,0,0)  ∃ (3,0,0,0)  ( (4,0,0,0)  ) (5,0,0,0)
  c_i (6,0,i,0)   x_i (7,1,i,0)
  U (8,2,0,1)  Θ (8,3,0,1)  f_{a,i} (8,4,i,a)     … 関数記号、引数の個数は a3
  ∈ (9,5,0,2)  r_{a,i} (9,6,i,a)                  … 関係記号、引数の個数は a3

■ 文法（本書の読み。原文はコンマ記号をもたず、例として (x_0 ∈ x_1)、Θ(x_0)、∃y(Q) を用いる）
  項     t ::= x_i | c_i | F ( t_1 … t_a )          （F は関数記号、a はその引数の個数）
  原子式   ::= ⊥ | ( t_1 ∈ t_2 ) | R ( t_1 … t_a )   （R は ∈ 以外の関係記号）
  論理式 φ ::= 原子式 | ( φ → ψ ) | ¬ φ | ∃ x_i ( φ )
  項は自己区切り的（変数・定数は 1 記号、適用は括弧で閉じる）なので、コンマなしの並置で曖昧さは生じない。

■ 表し方
  s は有限列（順序対 (i, t_i) の集合、i < h）で、各 t_i は長さ 4 の自然数の列。
  s が論理式であることを「構文解析の証明書 C が存在し、((0, h), 1) ∈ C」で表す。
  C は三つ組 ((i, j), k) の有限集合で、k = 0 は「区間 [i, j) は項」、k = 1 は「論理式」、
  k = n + 2 は「項がちょうど n 個並んだ列」を意味する。C の各項目は、より短い区間（または
  同じ区間でより少ない個数の列）の項目だけを使う規則で正当化されていなければならない。

  健全性：区間の長さ（と列の個数）に関する帰納法で、C の項目はすべて真である。
  完全性：本当の論理式なら、その構文木に現れる区間の全体が証明書になる。
  証明書は遺伝的有限集合なので M に属する。
"""
from fol import (Atom, Not, And, All, Oracle, In, Eq, Or, Imp, Iff, Ex, AllIn, ExIn, conj, disj)
import arith as A

# ---------------- 列と記号 ----------------

def seq_with(ctx, s, h, valpred):
    """s は定義域 h の関数で、各値 v は valpred(v) を満たす。"""
    i, q0 = ctx.fresh(2)
    elems = AllIn(q0, s, A.pair_parts(ctx, q0, lambda i_, v_: And(In(i_, h), valpred(v_))))
    total = AllIn(i, h, A.lookup(ctx, s, i, lambda v_: Eq(v_, v_)))
    func = A.all_pairs(ctx, s, lambda q1, i1, v1:
             A.all_pairs(ctx, s, lambda q2, i2, v2: Imp(Eq(i1, i2), Eq(v1, v2))))
    return conj(A.nat(ctx, h), elems, total, func)

def tuple4(ctx, t):
    if ctx.use_oracle("tuple4"):
        return Oracle("tuple4", [t])
    four = ctx.fresh()
    return Ex(four, And(A.numeral(ctx, four, 4), seq_with(ctx, t, four, lambda v: A.nat(ctx, v))))

def comp(ctx, t, k, pred):
    """t の第 k 成分 a が pred(a) を満たす。"""
    kk = ctx.fresh()
    return Ex(kk, And(A.numeral(ctx, kk, k), A.lookup(ctx, t, kk, pred)))

def comp_is(ctx, t, k, value):
    return comp(ctx, t, k, lambda a: A.numeral(ctx, a, value))

def sym(ctx, t, a0, a1=None, a2=None, a3=None):
    parts = [comp_is(ctx, t, 0, a0)]
    for k, v in ((1, a1), (2, a2), (3, a3)):
        if v is not None:
            parts.append(comp_is(ctx, t, k, v))
    return conj(*parts) if len(parts) > 1 else parts[0]

def _o(ctx, name, t, build):
    return Oracle(name, [t]) if ctx.use_oracle("sym") else build()

def is_punct(ctx, t, a0):   return _o(ctx, f"punct:{a0}", t, lambda: sym(ctx, t, a0, 0, 0, 0))   # ⊥ → ¬ ∃ ( )
def is_var(ctx, t):         return _o(ctx, "var", t, lambda: sym(ctx, t, 7, 1, None, 0))
def is_const(ctx, t):       return _o(ctx, "const", t, lambda: sym(ctx, t, 6, 0, None, 0))
def is_func(ctx, t):        return _o(ctx, "func", t, lambda: disj(
                                       sym(ctx, t, 8, 2, 0, 1),                         # U は (8,2,0,1) のみ
                                       sym(ctx, t, 8, 3, 0, 1),                         # Θ は (8,3,0,1) のみ
                                       And(comp_is(ctx, t, 0, 8), comp_is(ctx, t, 1, 4))))  # f_{a,i} = (8,4,i,a)
def is_rel(ctx, t):         return _o(ctx, "rel", t, lambda: conj(comp_is(ctx, t, 0, 9), comp_is(ctx, t, 1, 6)))   # ∈ 以外
def is_elem(ctx, t):        return _o(ctx, "elem", t, lambda: sym(ctx, t, 9, 5, 0, 2))   # ∈
def is_theta(ctx, t):       return _o(ctx, "theta", t, lambda: sym(ctx, t, 8, 3, 0, 1))

BOT, IMP, NEG, EXI, LP, RP = 0, 1, 2, 3, 4, 5

# ---------------- 証明書 ----------------

def in_cert(ctx, C, i, j, kpred):
    """((i, j), k) ∈ C かつ kpred(k)。"""
    p, s1, q, k = ctx.fresh(4)
    return ExIn(p, C, ExIn(s1, p, ExIn(q, s1, ExIn(k, s1, And(A.triple(ctx, p, i, j, k), kpred(k))))))

def all_cert(ctx, C, body):
    """C のすべての元が三つ組 ((i, j), k) で、body(i, j, k) を満たす。"""
    p, s1, q, k, s2, i, j = ctx.fresh(7)
    return AllIn(p, C, ExIn(s1, p, ExIn(q, s1, ExIn(k, s1, ExIn(s2, q, ExIn(i, s2, ExIn(j, s2,
           And(A.triple(ctx, p, i, j, k), body(i, j, k)))))))))

def plus2(ctx, n, k):        # k = n + 2
    n1 = ctx.fresh()
    return ExIn(n1, k, And(A.succ_of(ctx, n, n1), A.succ_of(ctx, n1, k)))

def certificate_ok(ctx, s, C, K0, K1):
    """C の各項目が正当化されている。K0, K1 は数 0, 1 を指す変数。"""
    if ctx.use_oracle("certificate"):
        return Oracle("certificate", [s, C, K0, K1])
    at = lambda i, pred: A.lookup(ctx, s, i, pred)
    isT = lambda k: Eq(k, K0)
    isF = lambda k: Eq(k, K1)

    def nxt(i, body):            # i の後者 i1 をとって body(i1)
        i1 = ctx.fresh()
        return Ex(i1, And(A.succ_of(ctx, i, i1), body(i1)))

    def prv(j, body):            # j = j1 + 1 となる j1 をとって body(j1)
        j1 = ctx.fresh()
        return ExIn(j1, j, And(A.succ_of(ctx, j1, j), body(j1)))

    def args_ok(i, j, arity_of):
        """s(i) は引数 a 個の記号、s(i+1) = (、s(j−1) = )、[i+2, j−1) は項 a 個の列。"""
        return at(i, lambda t: comp(ctx, t, 3, lambda a:
               nxt(i, lambda i1: nxt(i1, lambda i2: prv(j, lambda j1: conj(
                   arity_of(t),
                   at(i1, lambda u: is_punct(ctx, u, LP)),
                   at(j1, lambda u: is_punct(ctx, u, RP)),
                   in_cert(ctx, C, i2, j1, lambda k: plus2(ctx, a, k))))))))

    def term_ok(i, j):
        single = And(A.succ_of(ctx, i, j), at(i, lambda t: Or(is_var(ctx, t), is_const(ctx, t))))
        app = args_ok(i, j, lambda t: is_func(ctx, t))
        return Or(single, app)

    def list_ok(i, j, k):
        """k = n + 2：[i, j) は項 n 個の列。"""
        n, n0, m = ctx.fresh(3)
        empty_list = And(A.empty(ctx, n), Eq(i, j))
        cons = ExIn(n0, n, And(A.succ_of(ctx, n0, n), Or(
            ExIn(m, j, And(in_cert(ctx, C, i, m, isT),
                           in_cert(ctx, C, m, j, lambda k2: plus2(ctx, n0, k2)))),
            And(in_cert(ctx, C, i, j, isT), in_cert(ctx, C, j, j, lambda k2: plus2(ctx, n0, k2))))))
        nn1 = ctx.fresh()
        return ExIn(nn1, k, ExIn(n, nn1, And(plus2(ctx, n, k), Or(empty_list, cons))))

    def formula_ok(i, j):
        m = ctx.fresh()
        bot = And(A.succ_of(ctx, i, j), at(i, lambda t: is_punct(ctx, t, BOT)))
        def infix(op_pred, kind):
            return And(at(i, lambda t: is_punct(ctx, t, LP)),
                   nxt(i, lambda i1: prv(j, lambda j1: And(
                       at(j1, lambda u: is_punct(ctx, u, RP)),
                       ExIn(m, j, conj(in_cert(ctx, C, i1, m, kind),
                                       at(m, op_pred),
                                       nxt(m, lambda m1: in_cert(ctx, C, m1, j1, kind))))))))
        elem = infix(lambda u: is_elem(ctx, u), isT)
        rel = args_ok(i, j, lambda t: is_rel(ctx, t))
        imp = infix(lambda u: is_punct(ctx, u, IMP), isF)
        neg = And(at(i, lambda t: is_punct(ctx, t, NEG)), nxt(i, lambda i1: in_cert(ctx, C, i1, j, isF)))
        exi = And(at(i, lambda t: is_punct(ctx, t, EXI)),
              nxt(i, lambda i1: And(at(i1, lambda t: is_var(ctx, t)),
              nxt(i1, lambda i2: And(at(i2, lambda t: is_punct(ctx, t, LP)),
              nxt(i2, lambda i3: prv(j, lambda j1: And(
                  at(j1, lambda u: is_punct(ctx, u, RP)),
                  in_cert(ctx, C, i3, j1, isF)))))))))
        return disj(bot, elem, rel, imp, neg, exi)

    return all_cert(ctx, C, lambda i, j, k: disj(
        And(isT(k), term_ok(i, j)),
        And(isF(k), formula_ok(i, j)),
        list_ok(i, j, k)))

def formula(ctx, s, minus=False):
    """s は ┌L┐ の論理式（minus=True なら Θ を含まない論理式、すなわち Formula₋）。
    0 と 1 を指す変数を先に確定し、次に長さ h、最後に証明書 C を量化する。"""
    if ctx.use_oracle("formula"):
        return Oracle("formula_minus" if minus else "formula", [s])
    K0, K1, h, C = ctx.fresh(4)
    body = And(seq_with(ctx, s, h, lambda t: tuple4(ctx, t)),
               Ex(C, And(in_cert(ctx, C, K0, h, lambda k: Eq(k, K1)),
                         certificate_ok(ctx, s, C, K0, K1))))
    if minus:
        w = ctx.fresh()
        body = And(body, Not(ExIn(w, h, A.lookup(ctx, s, w, lambda t: is_theta(ctx, t)))))
    return Ex(K0, And(A.empty(ctx, K0), Ex(K1, And(A.succ_of(ctx, K0, K1), Ex(h, body)))))
