"""
MetaCode と Formula の接続。

原文：Symbol の元（4 つ組）を Encode で自然数にし、その列にもう一度 Encode を施したものが
┌L┐ 論理式 P の番号 MetaCode(P) である。

  metacode(n, s)    ：s は 4 つ組の有限列で、n = Encode(⟨Encode(s(0)), …, Encode(s(h−1))⟩)
  formula_code(n)   ：∃s (Formula(s) ∧ metacode(n, s))      … n は論理式の番号
  formula_code_minus：∃s (Formula₋(s) ∧ metacode(n, s))     … n は Θ を含まない論理式の番号

Encode は単射なので、n から s は一意に定まる（s が論理式かどうかに関係なく）。
中間の列 c（記号ごとの番号の列）は自然数の有限列で、遺伝的有限なので M に属する。
"""
from fol import Oracle, In, Eq, And, Not, Ex, AllIn, ExIn, conj
import arith as A
import parse as P

def metacode(ctx, n, s):
    if ctx.use_oracle("metacode"):
        return Oracle("metacode", [n, s])
    # 長さ h を先に確定し、次に記号ごとの番号の列 c を量化する
    h, c, i = ctx.fresh(3)
    return Ex(h, And(
        P.seq_with(ctx, s, h, lambda t: P.tuple4(ctx, t)),       # s は長さ h の 4 つ組の列
        Ex(c, conj(
            A.encode(ctx, c, n),                                  # n = Encode(c)
            P.seq_with(ctx, c, h, lambda v: A.nat(ctx, v)),      # c は長さ h の自然数の列
            AllIn(i, h, A.lookup(ctx, s, i, lambda t:            # 各 i < h で c(i) = Encode(s(i))
                         A.lookup(ctx, c, i, lambda v: A.encode(ctx, t, v))))))))

def formula_code(ctx, n, minus=False):
    if ctx.use_oracle("formula_code"):
        return Oracle("formula_code_minus" if minus else "formula_code", [n])
    s = ctx.fresh()
    return Ex(s, And(P.formula(ctx, s, minus), metacode(ctx, n, s)))
