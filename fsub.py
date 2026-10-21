"""
別紙 C 第 5 項（改訂64）：基準点 λ′ に対する F の類似物 F_{λ′} の値を、M の中で名指す式。

  F_{λ′}(k) = 1 + max D′_k、D′_k = { n : n は k 記号未満の L-式（第 2 節の文法）で V_{λ′+1} において一意に定まる }

を、M の純粋な {∈, =} 式 G(λ, k, x)「λ+1 での V の段 W について x = F_W(k)」として書く。
λ′ を定める式 ψ(λ) と、k を定める式 Num_k(k) を合成して

  Φ(x) ≡ ∃k (Num_k(k) ∧ ∃λ (ψ(λ) ∧ G(λ, k, x)))

とすれば、M ⊨ ∃!x Φ(x) かつ M ⊨ Φ[F_{λ′}(k)] なので、F_{λ′}(k) ∈ D_{|Φ|+1}、すなわち
F_{λ′}(k) < F(|Φ| + 1)。|Φ| = |Num_k| + |ψ| + |G| + （つなぎの記号）で、|G| は k・λ′ によらない定数。

■ L-式の表し方
  記号の番号：x 0、′ 1、¬ 2、∧ 3、∀ 4、∈ 5、= 6、( 7、) 8。式は長さ h の記号の列 s（順序対 (i, t_i) の集合）。
  証明書 C は三つ組 ((i, j), k) の有限集合で、k = 0 は「区間 [i, j) は変数（x の後に ′ が並ぶ）」、
  k = 1 は「区間 [i, j) は式」。式の項目は、より短い区間の項目だけを使う規則で正当化される：
    原子式 ( u ∈ v )・( u = v )、否定 ¬φ、連言 ( φ ∧ ψ )、全称 ∀u φ。
  変数の番号（′ の個数）m は表 IX（((i, j), m)、j = i + 1 + m）で引く。Ns は式に現れる変数の番号の集合。
  自由変数の表 FV（((i, j), m)）と、充足の表 S（((i, j), σ)、σ は Ns から W への関数）を、
  証明書の式の項目ごとの同値条件で定める（改訂65 で説明を訂正）。
  ・証明書 C は一意ではない（根の構文解析に使わない真の項目を余分に入れてよい）。FV・S も、
    C の式の項目以外の区間には余分な元があってよい。
  ・それでも、C の項目はすべて真で（区間の長さに関する帰納法）、根の構文解析に現れる区間は C に入る。
    L の一意読み（先頭の記号で規則が決まり、連言の ∧ の位置は一意）により、FV・S の C 上の値は
    真の自由変数・Tarski の充足と一致する。よって根の式についての判定は、表の取り方によらない。
  ・C・IX・Ns・FV は有限だが、S は W が無限なら一般に無限集合である（V_{λ′+ω} の部分集合として M にある）。
"""
from fol import (Atom, Not, And, All, Oracle, In, Eq, Or, Imp, Iff, Ex, AllIn, ExIn, conj, disj, Ctx, length, free)
import arith as A
import structure as St

TOK = dict(x=0, prime=1, neg=2, conj=3, all=4, elem=5, eq=6, lp=7, rp=8)


class FS:
    """F_W の式の部品。保持する変数：s, h, C, IX, Ns, FV, S, W, K0（= ∅）。"""
    def __init__(self, ctx, s, h, C, IX, Ns, FV, S, W, K0):
        self.ctx, self.s, self.h, self.C, self.IX, self.Ns, self.FV, self.S, self.W, self.K0 = \
            ctx, s, h, C, IX, Ns, FV, S, W, K0

    # ---- 列と表の参照 ----
    def tok(self, i, c):
        return A.lookup(self.ctx, self.s, i, lambda v: A.numeral(self.ctx, v, c))

    def nxt(self, i, body):
        i1 = self.ctx.fresh()
        return Ex(i1, And(A.succ_of(self.ctx, i, i1), body(i1)))

    def in3(self, X, a, b, c):                      # ((a, b), c) ∈ X
        p = self.ctx.fresh()
        return ExIn(p, X, A.triple(self.ctx, p, a, b, c))

    def inC(self, i, j, kind):
        kk = self.ctx.fresh()
        return Ex(kk, And(A.numeral(self.ctx, kk, kind), self.in3(self.C, i, j, kk)))

    def for3(self, X, body):
        """X の元で三つ組 ((i, j), k) の形のものすべてについて body(i, j, k)。"""
        ctx = self.ctx
        r, i, j = ctx.fresh(3)
        return A.all_pairs(ctx, X, lambda q, nb, k:
            AllIn(r, nb, AllIn(i, r, AllIn(j, r, Imp(A.pair(ctx, nb, i, j), body(i, j, k))))))

    def ix(self, i, j, m): return self.in3(self.IX, i, j, m)
    def fv(self, i, j, m): return self.in3(self.FV, i, j, m)
    def inS(self, i, j, sg): return self.in3(self.S, i, j, sg)

    # ---- 規則（extra は規則の各部分を受け取って追加の条件を述べる） ----
    def r_atom(self, i, j, extra):
        ctx = self.ctx
        a, b = ctx.fresh(2)
        return And(self.tok(i, TOK["lp"]), self.nxt(i, lambda i1:
            ExIn(a, j, ExIn(b, j, conj(
                self.inC(i1, a, 0),
                Or(self.tok(a, TOK["elem"]), self.tok(a, TOK["eq"])),
                self.nxt(a, lambda a1: And(self.inC(a1, b, 0), extra(i1, a, a1, b))),
                self.tok(b, TOK["rp"]),
                A.succ_of(ctx, b, j))))))

    def r_not(self, i, j, extra):
        return And(self.tok(i, TOK["neg"]), self.nxt(i, lambda i1: And(self.inC(i1, j, 1), extra(i1))))

    def r_and(self, i, j, extra):
        ctx = self.ctx
        a, b = ctx.fresh(2)
        return And(self.tok(i, TOK["lp"]), self.nxt(i, lambda i1:
            ExIn(a, j, conj(self.inC(i1, a, 1), self.tok(a, TOK["conj"]), self.nxt(a, lambda a1:
                ExIn(b, j, conj(self.inC(a1, b, 1), self.tok(b, TOK["rp"]), A.succ_of(ctx, b, j),
                                extra(i1, a, a1, b))))))))

    def r_all(self, i, j, extra):
        a = self.ctx.fresh()
        return And(self.tok(i, TOK["all"]), self.nxt(i, lambda i1:
            ExIn(a, j, conj(self.inC(i1, a, 0), self.inC(a, j, 1), extra(i1, a)))))

    def is_var(self, i, j):
        ctx = self.ctx
        p = ctx.fresh()
        return conj(self.tok(i, TOK["x"]), In(i, j), Or(In(j, self.h), Eq(j, self.h)),
                    AllIn(p, j, Imp(In(i, p), self.tok(p, TOK["prime"]))))

    # ---- 表の条件 ----
    def cert_ok(self):
        T = lambda *a: Eq(a[0], a[0])
        return self.for3(self.C, lambda i, j, k: Or(
            And(A.numeral(self.ctx, k, 0), self.is_var(i, j)),
            And(A.numeral(self.ctx, k, 1), disj(
                self.r_atom(i, j, lambda *a: Eq(i, i)), self.r_not(i, j, lambda *a: Eq(i, i)),
                self.r_and(i, j, lambda *a: Eq(i, i)), self.r_all(i, j, lambda *a: Eq(i, i))))))

    def ix_ok(self):
        ctx = self.ctx
        m = ctx.fresh()
        return And(
            self.for3(self.C, lambda i, j, k: Imp(A.numeral(ctx, k, 0), Ex(m, self.ix(i, j, m)))),
            self.for3(self.IX, lambda i, j, mm: And(self.inC(i, j, 0),
                                                     self.nxt(i, lambda i1: A.add(ctx, i1, mm, j)))))

    def ns_ok(self):
        ctx = self.ctx
        m, i, j = ctx.fresh(3)
        return And(AllIn(m, self.Ns, Ex(i, Ex(j, self.ix(i, j, m)))),
                   self.for3(self.IX, lambda i_, j_, mm: In(mm, self.Ns)))

    def fv_clause(self, i, j, m):
        return disj(
            self.r_atom(i, j, lambda i1, a, a1, b: Or(self.ix(i1, a, m), self.ix(a1, b, m))),
            self.r_not(i, j, lambda i1: self.fv(i1, j, m)),
            self.r_and(i, j, lambda i1, a, a1, b: Or(self.fv(i1, a, m), self.fv(a1, b, m))),
            self.r_all(i, j, lambda i1, a: And(self.fv(a, j, m), Not(self.ix(i1, a, m)))))

    def fv_ok(self):
        ctx = self.ctx
        m = ctx.fresh()
        return And(
            self.for3(self.C, lambda i, j, k: Imp(A.numeral(ctx, k, 1),
                AllIn(m, self.Ns, Iff(self.fv(i, j, m), self.fv_clause(i, j, m))))),
            self.for3(self.FV, lambda i, j, mm: In(mm, self.Ns)))

    def assign(self, sg):
        ctx = self.ctx
        q, k = ctx.fresh(2)
        return conj(
            AllIn(q, sg, A.pair_parts(ctx, q, lambda k_, a_: And(In(k_, self.Ns), In(a_, self.W)))),
            AllIn(k, self.Ns, A.lookup(ctx, sg, k, lambda a_: Eq(a_, a_))),
            A.all_pairs(ctx, sg, lambda q1, k1, a1: A.all_pairs(ctx, sg, lambda q2, k2, a2:
                Imp(Eq(k1, k2), Eq(a1, a2)))))

    def update(self, sg, k, a, sg2):                 # sg2 = sg[k := a]
        ctx = self.ctx
        return conj(self.assign(sg2),
                    A.lookup(ctx, sg2, k, lambda b: Eq(b, a)),
                    A.all_pairs(ctx, sg, lambda q, k1, b1: Or(Eq(k1, k),
                        A.lookup(ctx, sg2, k1, lambda b2: Eq(b2, b1)))))

    def val(self, sg, i, j, body):                   # 変数 [i, j) の σ での値 u について body(u)
        m = self.ctx.fresh()
        return Ex(m, And(self.ix(i, j, m), A.lookup(self.ctx, sg, m, body)))

    def s_clause(self, i, j, sg):
        ctx = self.ctx
        m, e, sg2 = ctx.fresh(3)
        return disj(
            self.r_atom(i, j, lambda i1, a, a1, b: self.val(sg, i1, a, lambda u: self.val(sg, a1, b, lambda v:
                Or(And(self.tok(a, TOK["elem"]), In(u, v)), And(self.tok(a, TOK["eq"]), Eq(u, v)))))),
            self.r_not(i, j, lambda i1: Not(self.inS(i1, j, sg))),
            self.r_and(i, j, lambda i1, a, a1, b: And(self.inS(i1, a, sg), self.inS(a1, b, sg))),
            self.r_all(i, j, lambda i1, a: Ex(m, And(self.ix(i1, a, m),
                AllIn(e, self.W, All(sg2, Imp(self.update(sg, m, e, sg2), self.inS(a, j, sg2))))))))

    def s_ok(self):
        ctx = self.ctx
        sg = ctx.fresh()
        return self.for3(self.C, lambda i, j, k: Imp(A.numeral(ctx, k, 1),
            All(sg, Imp(self.assign(sg), Iff(self.inS(i, j, sg), self.s_clause(i, j, sg))))))

    def holds(self, a):                               # φ[x := a]（自由変数は x だけ）
        sg = self.ctx.fresh()
        return Ex(sg, conj(self.assign(sg), A.lookup(self.ctx, sg, self.K0, lambda b: Eq(b, a)),
                           self.inS(self.K0, self.h, sg)))

    def only_x(self):
        m = self.ctx.fresh()
        return And(In(self.K0, self.Ns), AllIn(m, self.Ns, Iff(self.fv(self.K0, self.h, m), Eq(m, self.K0))))


def sym_seq(ctx, s, h):
    """s は長さ h の記号の列（値は 9 未満の自然数）。"""
    import parse as P
    nine = ctx.fresh()
    return Ex(nine, And(A.numeral(ctx, nine, 9), P.seq_with(ctx, s, h, lambda v: In(v, nine))))


def defines_in(ctx, W, k, n):
    """n は、k 記号未満の L-式で W において一意に定まる自然数。"""
    if ctx.use_oracle("defines_in"):
        return Oracle("defines_in", [W, k, n])
    s, h, C, IX, Ns, FV, S, K0, a, b = ctx.fresh(10)
    fs = FS(ctx, s, h, C, IX, Ns, FV, S, W, K0)
    body = conj(sym_seq(ctx, s, h), In(h, k),
                fs.cert_ok(), fs.inC(K0, h, 1), fs.ix_ok(), fs.ns_ok(), fs.fv_ok(), fs.only_x(), fs.s_ok(),
                ExIn(a, W, And(fs.holds(a), AllIn(b, W, Imp(fs.holds(b), Eq(b, a))))),
                In(n, W), fs.holds(n))
    for v in (S, FV, Ns, IX, C, h, s):
        body = Ex(v, body)
    return conj(A.nat(ctx, n), Ex(K0, And(A.empty(ctx, K0), body)))


def f_sub(ctx, W, k, x):
    """x = F_W(k) = 1 + max{ n : defines_in(W, k, n) }（空なら 1）。"""
    D, n, m, m2 = ctx.fresh(4)
    return Ex(D, conj(
        All(n, Iff(In(n, D), defines_in(ctx, W, k, n))),
        Or(And(A.empty(ctx, D), A.numeral(ctx, x, 1)),
           ExIn(m, D, And(A.succ_of(ctx, m, x), AllIn(m2, D, Or(In(m2, m), Eq(m2, m))))))))


def G(ctx, lam, k, x):
    """x = F_{λ}(k)：W = V_{λ+1} での F の類似物。"""
    l1, W = ctx.fresh(2)
    return Ex(l1, Ex(W, conj(A.succ_of(ctx, lam, l1), St.vstage(ctx, l1, W), f_sub(ctx, W, k, x))))


# ---------------- Num_y：y を名指す式（Horner 法） ----------------
# 変数番号：u と w は 1 と 2 を交互に使い、各段の内部の束縛変数は 3 番以降を使い回す（各段で自由なのは u, w だけ）。

def _step(u, w, bit):
    """u = 2w + bit。"""
    ctx = Ctx(start=3)
    if bit == 0:
        return A.add(ctx, w, w, u)
    t = ctx.fresh()
    return Ex(t, And(A.add(ctx, w, w, t), A.succ_of(ctx, t, u)))

def num_formula(y, u=1):
    """Num_y(u)（y ≥ 1）。"""
    bits = bin(y)[2:]
    w = 2 if u == 1 else 1
    if len(bits) == 1:
        return A.numeral(Ctx(start=3), u, 1)
    return Ex(w, And(num_formula(int(bits[:-1], 2), w), _step(u, w, int(bits[-1]))))


def phi_sub(y, psi_len=None):
    """Φ(x) ≡ ∃k (Num_y(k) ∧ ∃λ (ψ(λ) ∧ G(λ, k, x)))。ψ は Oracle で代用し、記号数は別に足す。
       変数：x = 0、k = 1（Num の最終段の変数）、λ = 2（Num の内部とは衝突しない：Num は k に閉じた部分式）。"""
    ctx = Ctx(start=3, oracles={"psi"})
    g = G(ctx, 2, 1, 0)
    return g


if __name__ == "__main__":
    import sys
    ctx = Ctx(start=3)
    g = G(ctx, 2, 1, 0)
    LG = length(g)
    print("|G(λ, k, x)| =", LG, " 自由変数", sorted(free(g)))
    # 一段あたりの Num の記号数
    for y in (1, 2, 3, 10, 1000, 10**6, 2**64 - 1):
        print(f"|Num_{y}| =", length(num_formula(y)))
