"""
原文の IsDefinition と Definable の意味を、M の純粋な {∈,=} 一階式として表す。

■ 原文
  IsDefinition(P) ≡ ∃x_0 ( P ∧ ∀x_1 ( P[x_1/x_0] → x_1 = x_0 ) )
  Definable(m, i, P) ≡ i ∈ ℕ ∧ P ∈ Formula ∧ U(CNF(i)) ⊨ IsDefinition(P) ∧ U(CNF(i)) ⊨ P[Parameter(m)/x_0]
  ⊨ は全称閉包で読む（別紙 E 第 9 項）。代入は原文の規則（P の内側の束縛変数は付け替えて捕獲を回避）。

■ 意味への書き換え
  原文の代入規則は捕獲を回避するので、代入補題により
    τ ⊨ P[x_1/x_0]  ⟺  τ[x_0 := τ(x_1)] ⊨ P
  が成り立つ。よって、割当て σ（定義域は W = Ns ∪ {0, 1}）の下で
    σ ⊨ IsDefinition(P)  ⟺  ∃a ∈ dom ( σ[0:=a] ⊨ P  ∧  ∀b ∈ dom ( σ[0:=b][1:=b] ⊨ P → b = a ) )
  外側の ∀x_1 は x_1 の値を b に取り替え、P の自由な x_1 も同じ b になる（これが「外側の ∀x_1 による捕獲」）。
  また P[Parameter(m)/x_0] の充足は、x_0 に m を割り当てた P の充足と同じである。
  等号 = は原文では略記だが、U(α) = V_λ では真の等号と一致するので、集合の等号として扱う。

  is_definition(s, 𝔄)：W 上のすべての割当て σ について上の条件
  param_true(s, 𝔄, m) ：σ(0) = m となる W 上のすべての割当て σ について σ ⊨ P
"""
from fol import (Oracle, In, Eq, And, Not, Or, Imp, Ex, All, AllIn, ExIn, conj)
import arith as A
import parse as P
import semantics as SM

class WParts:
    """W = Ns ∪ {0, 1} 上の割当ての部品（改訂45 で関数からメソッドにした。生成される式は同一）。"""
    def __init__(self, ctx, W, dom):
        self.ctx, self.W, self.dom = ctx, W, dom

    def assign_W(self, sg):
        ctx, W, dom = self.ctx, self.W, self.dom
        q1, kk = ctx.fresh(2)
        return conj(
            AllIn(q1, sg, A.pair_parts(ctx, q1, lambda k_, a_: And(In(k_, W), In(a_, dom)))),
            AllIn(kk, W, A.lookup(ctx, sg, kk, lambda a_: Eq(a_, a_))),
            A.all_pairs(ctx, sg, lambda _1, k1, a1: A.all_pairs(ctx, sg, lambda _2, k2_, a2:
                Imp(Eq(k1, k2_), Eq(a1, a2)))))

    def update(self, sg, kv, a, sg2):            # sg2 = sg[kv := a]（定義域 W）
        ctx = self.ctx
        return conj(self.assign_W(sg2),
                    A.lookup(ctx, sg2, kv, lambda b: Eq(b, a)),
                    A.all_pairs(ctx, sg, lambda _, k1, b1: Or(Eq(k1, kv),
                        A.lookup(ctx, sg2, k1, lambda b2: Eq(b2, b1)))))

def _common(ctx, s, dom, body):
    """W = Ns ∪ {0, 1}（Ns は s に現れる変数の添字の集合）を導入して body(W, assign_W, update) を返す。"""
    h, Ns, W, Z, O = ctx.fresh(5)
    at = lambda i, pred: A.lookup(ctx, s, i, pred)
    def var_index(t, b):
        return And(P.is_var(ctx, t), P.comp(ctx, t, 2, b))
    p, k, k2 = ctx.fresh(3)
    varset = And(AllIn(k, Ns, ExIn(p, h, at(p, lambda t: var_index(t, lambda kk: Eq(kk, k))))),
                 AllIn(p, h, at(p, lambda t: Imp(P.is_var(ctx, t), P.comp(ctx, t, 2, lambda kk: In(kk, Ns))))))
    q = ctx.fresh()
    wdef = conj(AllIn(q, W, Or(In(q, Ns), Or(Eq(q, Z), Eq(q, O)))),      # W ⊆ Ns ∪ {0, 1}
                AllIn(q, Ns, In(q, W)), In(Z, W), In(O, W))               # W ⊇ Ns ∪ {0, 1}

    wp = WParts(ctx, W, dom)
    assign_W, update = wp.assign_W, wp.update
    return Ex(Z, And(A.empty(ctx, Z), Ex(O, And(A.succ_of(ctx, Z, O), Ex(h, And(
        P.seq_with(ctx, s, h, lambda t: P.tuple4(ctx, t)),
        Ex(Ns, And(varset, Ex(W, And(wdef, body(W, Z, O, assign_W, update)))))))))))

def is_definition(ctx, s, dom, E, Cn, Fn, Rel, mutate=False):
    if ctx.use_oracle("is_definition"):
        return Oracle("is_definition", [s, dom, E, Cn, Fn, Rel])
    sat = lambda sg: SM.sat(ctx, s, dom, E, Cn, Fn, Rel, sg, extended=True)
    def body(W, Z, O, assign_W, update):
        sg, a, b, sa, sb, sb1 = ctx.fresh(6)
        if mutate:   # 変異版：外側の ∀x_1 が x_1 を取り替えない（「意図した意味」の読み）
            inner = Ex(sb, And(update(sg, Z, b, sb), sat(sb)))
        else:
            inner = Ex(sb1, And(update(sg, Z, b, sb1), Ex(sb, And(update(sb1, O, b, sb), sat(sb)))))
        return All(sg, Imp(assign_W(sg), ExIn(a, dom, And(
            Ex(sa, And(update(sg, Z, a, sa), sat(sa))),
            AllIn(b, dom, Imp(inner, Eq(b, a)))))))
    return _common(ctx, s, dom, body)

def param_true(ctx, s, dom, E, Cn, Fn, Rel, m):
    if ctx.use_oracle("param_true"):
        return Oracle("param_true", [s, dom, E, Cn, Fn, Rel, m])
    sat = lambda sg: SM.sat(ctx, s, dom, E, Cn, Fn, Rel, sg, extended=True)
    def body(W, Z, O, assign_W, update):
        sg = ctx.fresh()
        return All(sg, Imp(And(assign_W(sg), A.lookup(ctx, sg, Z, lambda v: Eq(v, m))), sat(sg)))
    return _common(ctx, s, dom, body)

def definable_in(ctx, s, dom, E, Cn, Fn, Rel, m, mutate=False):
    """構造 (dom, E, Cn, Fn, Rel) で、式 s が m を定義する：m ∈ dom ∧ IsDefinition ∧ P[m/x_0]。"""
    return conj(In(m, dom),
                is_definition(ctx, s, dom, E, Cn, Fn, Rel, mutate),
                param_true(ctx, s, dom, E, Cn, Fn, Rel, m))
