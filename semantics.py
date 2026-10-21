"""
┌L┐ の論理式の充足関係（Tarski の意味論）を、M の純粋な {∈,=} 一階式として表す。

■ 構造 𝔄 の表し方（すべて集合）
  dom ：領域
  E   ：┌∈┐ の解釈。順序対 (a, b) の集合
  Cn  ：定数の解釈。順序対 (t, a) の集合（t は定数記号の 4 つ組）
  Fn  ：関数記号の解釈。三つ組 ((t, w), a) の集合（w は引数の列）。U・Θ・f_{a,i} をまとめて扱う
  Rel ：関係記号の解釈。順序対 (t, w) の集合（成り立つ引数の列 w を集めたもの）
  原文の構造 U(α) では、dom = V_λ、E = ∈ ↾ V_λ で、U・Θ・追加記号の解釈が Fn・Cn・Rel に入る。

■ 割当て
  論理式 s に現れる変数の添字の集合を Ns とし、割当て σ は Ns から dom への関数とする。
  ∃x_k(φ) では σ の k の値だけを取り替える。

■ 表し方
  sat(s, 𝔄, σ) は「次を満たす集合 Ns, C, TV, S が存在し、((0, h), σ) ∈ S」と述べる。
   - Ns：s に現れる変数の添字の集合。
   - C ：s の構文解析の証明書（parse.py）。各区間が項・論理式・項の列のどれかを与える。
   - TV：項と項の列の値。元は ( ((i, j), k), (σ, v) ) の形で、区間 [i, j) の種類 k の対象の、
         割当て σ の下での値が v であることを表す（項なら v ∈ dom、列なら v は dom の元の有限列）。
   - S ：論理式の充足。元は ((i, j), σ) の形で、区間 [i, j) の論理式が σ の下で真であることを表す。
  TV と S には、C のすべての区間とすべての割当てについて、Tarski の条件を課す。
   - TV：(i, j, k, σ) ごとに値が少なくとも一つあり、TV に載っている値はすべて条件を満たす。
   - S ：((i, j), σ) ∈ S ⟺ 条件。
  区間の長さに関する帰納法で、TV の値は一意で正しく、S は真の充足関係と一致する。
  dom ∈ V_κ なら Ns, C, TV, S はすべて V_κ の部分集合（の元）なので M に属し、存在も保証される。
"""
from fol import (Oracle, In, Eq, And, Not, Or, Imp, Iff, Ex, All, AllIn, ExIn, conj, disj)
import arith as A
import parse as P

class SatParts:
    """sat の内部の部品。sat の式に現れる集合の変数（s, dom, E, Cn, Fn, Rel, K0, K1, h, Ns, C, TV, S）を保持する。
    改訂45 で、内部の関数をこのクラスのメソッドにまとめた（生成される式は以前と記号列として同一）。
    書き写しの検証（lean_tr_export.py）が、各メソッドを部品として個別に照合できるようにするためである。"""
    def __init__(self, ctx, s, dom, E, Cn, Fn, Rel, K0, K1, h, Ns, C, TV, S):
        self.ctx = ctx
        self.s, self.dom, self.E, self.Cn, self.Fn, self.Rel = s, dom, E, Cn, Fn, Rel
        self.K0, self.K1, self.h, self.Ns, self.C, self.TV, self.S = K0, K1, h, Ns, C, TV, S

    def at(self, i, pred): return A.lookup(self.ctx, self.s, i, pred)
    def isT(self, k): return Eq(k, self.K0)
    def isF(self, k): return Eq(k, self.K1)

    def nxt(self, i, body):
        i1 = self.ctx.fresh()
        return Ex(i1, And(A.succ_of(self.ctx, i, i1), body(i1)))
    def prv(self, j, body):
        j1 = self.ctx.fresh()
        return ExIn(j1, j, And(A.succ_of(self.ctx, j1, j), body(j1)))
    def var_index(self, t, body):                  # t = x_k のとき body(k)
        return And(P.is_var(self.ctx, t), P.comp(self.ctx, t, 2, body))

    # ---- 割当て ----
    def assign(self, sg):
        ctx = self.ctx
        q, q1, q2 = ctx.fresh(3)
        k = ctx.fresh()
        return conj(
            AllIn(q, sg, A.pair_parts(ctx, q, lambda k_, a_: And(In(k_, self.Ns), In(a_, self.dom)))),
            AllIn(k, self.Ns, A.lookup(ctx, sg, k, lambda a_: Eq(a_, a_))),
            A.all_pairs(ctx, sg, lambda q1_, k1, a1: A.all_pairs(ctx, sg, lambda q2_, k2, a2:
                Imp(Eq(k1, k2), Eq(a1, a2)))))

    def update(self, sg, k, a, sg2):               # sg2 = sg[k := a]
        ctx = self.ctx
        return conj(self.assign(sg2),
                    A.lookup(ctx, sg2, k, lambda b: Eq(b, a)),
                    A.all_pairs(ctx, sg, lambda q, k1, b1: Or(Eq(k1, k),
                        A.lookup(ctx, sg2, k1, lambda b2: Eq(b2, b1)))))

    def all_assign(self, body):
        sg = self.ctx.fresh()
        return All(sg, Imp(self.assign(sg), body(sg)))

    # ---- C・TV・S の参照 ----
    def inC(self, i, j, kpred):
        return P.in_cert(self.ctx, self.C, i, j, kpred)

    def tv(self, i, j, kpred, sg, valpred):
        """TV に ( ((i, j), k), (sg, v) ) があり、kpred(k) かつ valpred(v)。"""
        ctx = self.ctx
        e = ctx.fresh()
        return ExIn(e, self.TV, A.pair_parts(ctx, e, lambda a, b:
               And(A.pair_parts(ctx, a, lambda ij, k: And(A.pair(ctx, ij, i, j), kpred(k))),
                   A.pair_parts(ctx, b, lambda sg2, v: And(Eq(sg2, sg), valpred(v))))))

    def tv_all(self, i, j, kpred, sg, valpred):
        """TV の ( ((i, j), k), (sg, v) ) の形の元はすべて valpred(v) を満たす。"""
        ctx = self.ctx
        e = ctx.fresh()
        return AllIn(e, self.TV, A.pair_parts(ctx, e, lambda a, b:
               Imp(A.pair_parts(ctx, a, lambda ij, k: And(A.pair(ctx, ij, i, j), kpred(k))),
                   A.pair_parts(ctx, b, lambda sg2, v: Imp(Eq(sg2, sg), valpred(v))))))

    def inS(self, i, j, sg):
        ctx = self.ctx
        e = ctx.fresh()
        return ExIn(e, self.S, A.pair_parts(ctx, e, lambda ij, sg2: And(A.pair(ctx, ij, i, j), Eq(sg2, sg))))

    def in_pair_set(self, X, a, b):                # (a, b) ∈ X
        q = self.ctx.fresh()
        return ExIn(q, X, A.pair(self.ctx, q, a, b))

    def in_triple_set(self, X, a, b, c):           # ((a, b), c) ∈ X
        q = self.ctx.fresh()
        return ExIn(q, X, A.triple(self.ctx, q, a, b, c))

    # ---- 列の cons：w = ⟨v⟩ ⌢ w2 ----
    def cons(self, v, w2, w):
        ctx = self.ctx
        q, z = ctx.fresh(2)
        mem = lambda X, k, x: self.in_pair_set(X, k, x)
        return conj(
            Ex(z, And(A.empty(ctx, z), mem(w, z, v))),
            AllIn(q, w, A.pair_parts(ctx, q, lambda k, x: Or(
                And(A.empty(ctx, k), Eq(x, v)),
                ExIn(ctx_k0 := ctx.fresh(), k, And(A.succ_of(ctx, ctx_k0, k), mem(w2, ctx_k0, x)))))),
            AllIn(q, w2, A.pair_parts(ctx, q, lambda k0, x:
                self.nxt(k0, lambda k: mem(w, k, x)))))

    # ---- 項の値の条件 ----
    def term_clause(self, i, j, sg, v):
        ctx, at, nxt, prv = self.ctx, self.at, self.nxt, self.prv
        single_var = And(A.succ_of(ctx, i, j),
                         at(i, lambda t: self.var_index(t, lambda k: A.lookup(ctx, sg, k, lambda a: Eq(a, v)))))
        single_const = And(A.succ_of(ctx, i, j),
                           at(i, lambda t: And(P.is_const(ctx, t), self.in_pair_set(self.Cn, t, v))))
        app = at(i, lambda t: And(P.is_func(ctx, t), P.comp(ctx, t, 3, lambda ar:
              nxt(i, lambda i1: nxt(i1, lambda i2: prv(j, lambda j1: conj(
                  at(i1, lambda u: P.is_punct(ctx, u, P.LP)),
                  at(j1, lambda u: P.is_punct(ctx, u, P.RP)),
                  self.tv(i2, j1, lambda k: P.plus2(ctx, ar, k), sg, lambda w: self.in_triple_set(self.Fn, t, w, v)))))))))
        return disj(single_var, single_const, app)

    def list_clause(self, i, j, n, sg, w):
        ctx, isT = self.ctx, self.isT
        m, n0 = ctx.fresh(2)
        empty_case = conj(A.empty(ctx, n), Eq(i, j), A.empty(ctx, w))
        def via(mm):
            return And(self.inC(i, mm, isT), self.tv(i, mm, isT, sg, lambda v:
                   self.tv(mm, j, lambda k2: P.plus2(ctx, n0, k2), sg, lambda w2: self.cons(v, w2, w))))
        cons_case = ExIn(n0, n, And(A.succ_of(ctx, n0, n), Or(ExIn(m, j, via(m)), via(j))))
        return Or(empty_case, cons_case)

    # ---- 論理式の充足の条件 ----
    def formula_clause(self, i, j, sg):
        ctx, at, nxt, prv, inC, isT, isF, tv, inS = (self.ctx, self.at, self.nxt, self.prv, self.inC,
                                                     self.isT, self.isF, self.tv, self.inS)
        m = ctx.fresh()
        def infix(op_pred, kind, combine):
            return And(at(i, lambda t: P.is_punct(ctx, t, P.LP)),
                   nxt(i, lambda i1: prv(j, lambda j1: And(
                       at(j1, lambda u: P.is_punct(ctx, u, P.RP)),
                       ExIn(m, j, conj(inC(i1, m, kind), at(m, op_pred),
                                       nxt(m, lambda m1: And(inC(m1, j1, kind), combine(i1, m, m1, j1)))))))))
        bot = And(A.succ_of(ctx, i, j), And(at(i, lambda t: P.is_punct(ctx, t, P.BOT)), Not(Eq(i, i))))
        elem = infix(lambda u: P.is_elem(ctx, u), isT, lambda a, b, c, d:
                     tv(a, b, isT, sg, lambda v1: tv(c, d, isT, sg, lambda v2: self.in_pair_set(self.E, v1, v2))))
        rel = at(i, lambda t: And(P.is_rel(ctx, t), P.comp(ctx, t, 3, lambda ar:
              nxt(i, lambda i1: nxt(i1, lambda i2: prv(j, lambda j1: conj(
                  at(i1, lambda u: P.is_punct(ctx, u, P.LP)),
                  at(j1, lambda u: P.is_punct(ctx, u, P.RP)),
                  tv(i2, j1, lambda k: P.plus2(ctx, ar, k), sg, lambda w: self.in_pair_set(self.Rel, t, w)))))))))
        imp = infix(lambda u: P.is_punct(ctx, u, P.IMP), isF, lambda a, b, c, d:
                    Or(Not(inS(a, b, sg)), inS(c, d, sg)))
        neg = And(at(i, lambda t: P.is_punct(ctx, t, P.NEG)),
                  nxt(i, lambda i1: And(inC(i1, j, isF), Not(inS(i1, j, sg)))))
        a_, sg2 = ctx.fresh(2)
        exi = And(at(i, lambda t: P.is_punct(ctx, t, P.EXI)),
              nxt(i, lambda i1: at(i1, lambda t: self.var_index(t, lambda k:
              nxt(i1, lambda i2: And(at(i2, lambda u: P.is_punct(ctx, u, P.LP)),
              nxt(i2, lambda i3: prv(j, lambda j1: conj(
                  at(j1, lambda u: P.is_punct(ctx, u, P.RP)),
                  inC(i3, j1, isF),
                  ExIn(a_, self.dom, Ex(sg2, And(self.update(sg, k, a_, sg2), inS(i3, j1, sg2)))))))))))))
        return disj(bot, elem, rel, imp, neg, exi)

    # ---- TV と S に課す条件 ----
    def tv_ok(self):
        ctx, isT = self.ctx, self.isT
        def per_entry(i, j, k):
            n, nn1 = ctx.fresh(2)
            term_part = Imp(isT(k), self.all_assign(lambda sg: And(
                self.tv(i, j, isT, sg, lambda v: Eq(v, v)),
                self.tv_all(i, j, isT, sg, lambda v: self.term_clause(i, j, sg, v)))))
            # k = n + 2 となる n について（k が 0 や 1 なら条件は空）
            list_part = AllIn(nn1, k, AllIn(n, nn1, Imp(P.plus2(ctx, n, k), self.all_assign(lambda sg: And(
                self.tv(i, j, lambda k2: Eq(k2, k), sg, lambda w: Eq(w, w)),
                self.tv_all(i, j, lambda k2: Eq(k2, k), sg, lambda w: self.list_clause(i, j, n, sg, w)))))))
            return And(term_part, list_part)
        return P.all_cert(ctx, self.C, per_entry)

    def s_ok(self):
        return P.all_cert(self.ctx, self.C, lambda i, j, k: Imp(self.isF(k), self.all_assign(lambda sg:
               Iff(self.inS(i, j, sg), self.formula_clause(i, j, sg)))))

    def varset(self):
        ctx, at = self.ctx, self.at
        p, k = ctx.fresh(2)
        return And(AllIn(k, self.Ns, ExIn(p, self.h, at(p, lambda t: self.var_index(t, lambda k2: Eq(k2, k))))),
                   AllIn(p, self.h, at(p, lambda t: Imp(P.is_var(ctx, t), P.comp(ctx, t, 2, lambda k2: In(k2, self.Ns))))))

    def body(self, sg):           # sg は Ns 上の割当て
        ctx, C, TV, S = self.ctx, self.C, self.TV, self.S
        return Ex(C, conj(self.inC(self.K0, self.h, self.isF), P.certificate_ok(ctx, self.s, C, self.K0, self.K1),
               Ex(TV, And(self.tv_ok(), Ex(S, And(self.s_ok(), self.inS(self.K0, self.h, sg)))))))


def sat(ctx, s, dom, E, Cn, Fn, Rel, sigma, extended=False):
    """extended=True なら、sigma は Ns を含むより大きな定義域の関数でもよい（Ns への制限で評価する）。"""
    if ctx.use_oracle("sat"):
        return Oracle("sat_ext" if extended else "sat", [s, dom, E, Cn, Fn, Rel, sigma])
    K0, K1, h, Ns, C, TV, S = ctx.fresh(7)
    sp = SatParts(ctx, s, dom, E, Cn, Fn, Rel, K0, K1, h, Ns, C, TV, S)

    if extended:            # sigma の Ns への制限 sr をとって評価する
        sr, q = ctx.fresh(2)
        top = Ex(sr, conj(sp.assign(sr), AllIn(q, sr, In(q, sigma)), sp.body(sr)))
    else:
        top = And(sp.assign(sigma), sp.body(sigma))

    return Ex(K0, And(A.empty(ctx, K0), Ex(K1, And(A.succ_of(ctx, K0, K1), Ex(h, And(
        P.seq_with(ctx, s, h, lambda t: P.tuple4(ctx, t)),
        Ex(Ns, And(sp.varset(), top))))))))
