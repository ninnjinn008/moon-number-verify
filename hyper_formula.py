"""
10↑^10 10 を M = V_{κ+1} で一意に名指す純粋な {∈,=} 一階式 UpArrow(x) を生成する。

ハイパー演算 H(n, a, b)：
    H(0, a, b)     = b + 1
    H(1, a, 0)     = a,   H(2, a, 0) = 0,   H(n, a, 0) = 1 (n ≥ 3)
    H(n+1, a, b+1) = H(n, a, H(n+1, a, b))
このとき H(1)=加法, H(2)=乗法, H(3)=冪, H(k+2, a, b) = a ↑^k b。
よって 10↑^10 10 = H(12, 10, 10)。

計算に必要な表（三つ組 ((n,b),v) の有限集合）t は遺伝的有限集合なので M に属する。
式は「a = 10 で、再帰の条件を満たす表 t があり、((12,10),x) ∈ t」と述べる。
表の各三つ組が正しい値をもつことは (n, b) の辞書式順序に関する帰納法で従うので、x は一意。

量化はすべて有界にしてある（p∈t、p の成分は p の元の元、など）。
M は推移的なので、有界化しても意味は変わらない。
"""
import sys
import num_formula as nf
from num_formula import (Atom, Not, And, All, In, Eq, Or, Imp, Iff, Ex,
                         AllIn, ExIn, conj, Empty, Pair, hygienic, render, length, free)

# 変数番号（num_formula の 0〜14 と重ならないもの）
SU = 15                 # SuccOf の内部
Q3, S3 = 16, 17         # Triple の内部（成分を取り出す補助）
C1, C2 = 18, 19         # 数詞の鎖で交互に使う
TT, PP = 20, 21         # 表 t、三つ組 p
SA, SB = 22, 23         # 三つ組の成分を取り出す補助
NN, BB, VV = 24, 25, 26 # 三つ組の成分 n, b, v
N1, B1x, WW = 27, 28, 29
P2, P3 = 30, 31
EE = 32                 # IsOne の内部
AA, MM, M1 = 33, 34, 35 # a = 10、m = 12
XX = 0                  # 定義される数（唯一の自由変数）

def SuccOf(b, c):        # c = b ∪ {b}
    hygienic([b, c], [SU])
    return All(SU, Iff(In(SU, c), Or(In(SU, b), Eq(SU, b))))

def IsOne(z):            # z = {∅}：∃e∈z (e = ∅ ∧ z = e ∪ {e})
    hygienic([z], [EE])
    return ExIn(EE, z, And(Empty(EE), SuccOf(EE, z)))

def Triple(p, n, b, v):  # p = ((n, b), v)：∃s∈p ∃q∈s (Pair(p,q,v) ∧ Pair(q,n,b))
    hygienic([p, n, b, v], [S3, Q3])
    return ExIn(S3, p, ExIn(Q3, S3, And(Pair(p, Q3, v), Pair(Q3, n, b))))

def Numeral(v, k, other):
    """v = k（後者を k 回たどる）。v と other を交互に使う。"""
    if k == 0:
        return Empty(v)
    hygienic([v], [other])
    return ExIn(other, v, And(SuccOf(other, v), Numeral(other, k - 1, v)))

def Base(n1, v, a):
    # H(n1+1, a, 0)：n1 = 0 なら a、n1 = 1 なら 0、n1 ≥ 2 なら 1
    return Or(Or(And(Empty(n1), Eq(v, a)),
                 And(IsOne(n1), Empty(v))),
              conj(Not(Empty(n1)), Not(IsOne(n1)), IsOne(v)))

def Case(n, b, v, t, a):
    zero_n = And(Empty(n), SuccOf(b, v))
    zero_b = ExIn(N1, n, conj(SuccOf(N1, n), Empty(b), Base(N1, v, a)))
    # H(n, a, b) = H(n-1, a, H(n, a, b-1))：((n, b-1), w) ∈ t かつ ((n-1, w), v) ∈ t
    rec = ExIn(N1, n, ExIn(B1x, b, conj(
            SuccOf(N1, n), SuccOf(B1x, b),
            ExIn(P2, t, ExIn(SA, P2, ExIn(WW, SA, And(
                Triple(P2, n, B1x, WW),
                ExIn(P3, t, Triple(P3, N1, WW, v)))))))))
    return Or(Or(zero_n, zero_b), rec)

def Table(t, a):
    # ∀p∈t ∀s1∈p ∀q∈s1 ∀v∈s1 ∀s2∈q ∀n∈s2 ∀b∈s2 (Triple(p,n,b,v) → Case)
    hygienic([t, a], [PP, SA, SB, NN, BB, VV, N1, B1x, WW, P2, P3])
    return AllIn(PP, t, AllIn(SA, PP, AllIn(SB, SA, AllIn(VV, SA,
           AllIn(SA, SB, AllIn(NN, SA, AllIn(BB, SA,
           Imp(Triple(PP, NN, BB, VV), Case(NN, BB, VV, t, a)))))))))

def Hyper(x, nk, ak, bk):
    """x = H(nk, ak, bk)。数詞は後者の鎖で作る（テスト用の一般形）。"""
    A_, N_, B_ = AA, MM, M1
    return Ex(A_, conj(
        Numeral(A_, ak, C1),
        Ex(N_, And(Numeral(N_, nk, C1),
        Ex(B_, And(Numeral(B_, bk, C1),
        Ex(TT, And(Table(TT, A_),
                   ExIn(PP, TT, Triple(PP, N_, B_, x))))))))))

def UpArrow(x):
    """x = 10↑^10 10 = H(12, 10, 10)。12 は 10 の後者の後者として作る。"""
    return Ex(AA, And(Numeral(AA, 10, C1),
           Ex(M1, And(SuccOf(AA, M1),
           Ex(MM, And(SuccOf(M1, MM),
           Ex(TT, And(Table(TT, AA),
                      ExIn(PP, TT, Triple(PP, MM, AA, x))))))))))

if __name__ == "__main__":
    f = UpArrow(XX)
    s = render(f)
    assert len(s) == length(f)
    assert set(s) <= nf.ALPHABET
    assert free(f) == {XX}
    print("|UpArrow| =", length(f), "記号")
    if len(sys.argv) > 1:
        print(s)
