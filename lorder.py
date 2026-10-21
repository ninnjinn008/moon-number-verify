"""
構成可能宇宙の段階 L_β とその整列順序 <_L、およびそれを使った Θ の解釈。

■ 定義可能な部分集合
  ┌L┐ の式のうち、記号が変数・┌∈┐・論理記号・括弧だけのもの（定数・関数・関係記号を含まない）を「純粋な式」と呼ぶ。
  純粋な式 P（番号 n = MetaCode(P)）とパラメータ τ（Ns ∖ {0} から X への関数。Ns は P に現れる変数の添字）について
      y = { z ∈ X : (X, ∈) ⊨ P [x_0 := z, 他の変数は τ] }
  のとき「(n, τ) は X 上で y を定義する」という（defines）。Def(X) はそのような y 全体。
  空の X では z がないので、定義される集合は ∅ だけになり、Def(∅) = {∅}（τ = ∅ で x_0 だけの式を使う）。

■ 定義の順序
  (n, τ) ≺ (n′, τ′) ⟺ n < n′、または n = n′ かつ τ が τ′ より辞書式で小さい
  （添字の小さい順に比べ、最初に値が異なる添字 k で τ(k) <_β τ′(k)）。
  n が同じなら τ と τ′ の定義域は同じ（n から Ns が決まる）。<_β が整列順序なら ≺ も整列順序。

■ 段階と順序（l_order）
  L_0 = ∅、<_0 = ∅。
  L_{β+1} = Def(L_β)。<_{β+1}：L_β の元どうしは <_β、L_β の元は新しい元より前、
      新しい元 a, b は「a の最小の定義 ≺ b の最小の定義」（≺ が整列順序なので、
      「a のある定義が b のどの定義よりも小さい」と同値）。
  極限 β：L_β = ⋃_{γ<β} L_γ、<_β = ⋃_{γ<β} <_γ（各段は前の段の終切片への延長なので、これで整列順序）。
  外側の宇宙 L では、L で到達不能な λ について V_λ = L_λ である（M 自身は ZF のモデルではなく、
  M の中で V = L が成り立つと言っているのではない）。段階の表とその証人はすべて V_κ ⊆ M に属し、
  各条件は V_κ の元について絶対的なので、M で評価しても L における本物の L_β と <_β が得られ、D = V_λ の上の順序 <_λ になる。
  これは Gödel の <_L の一つの具体化である（式の番号の付け方とパラメータの比べ方だけが流儀による）。

■ Θ の解釈（theta_L）
  m ∈ D について、m が Formula₋ の式 P の番号なら、Z = { σ : σ ⊨ P }（σ は Ns 上の割当て）として
      good(a) ⟺ Ns のどの i についても、「P の真偽が x_i の値だけで決まり（dep_only）、かつ Z ≠ ∅」ならば
                 すべての σ で σ[i := a] ⊨ P
  とし、Θ(m) は good な元のうち <_λ で最小のもの。m が Formula₋ の式の番号でなければ Θ(m) = ∅。
  - P の真偽が一つの変数 x_i だけで決まり、しかも定数でないなら、i は一つに定まり、Θ(m) は P を満たす最小の元。
  - P が定数（つねに真、またはつねに偽）なら、どの a も good で、Θ(m) = ∅（<_λ の最小元）。
  - それ以外（二つ以上の変数に依存する）なら、どの a も good で、Θ(m) = ∅。
  修復版の Henkin 公理（読み 1：自由変数が x_i だけの Formula₋ の式 P に限る）は、
  そのような P の真偽が x_i だけで決まることから、すべて成り立つ。P は Θ を含まないので、
  sat が Fn の Θ の部分を参照することはなく、この条件は Θ について循環しない。
"""
from fol import Oracle, In, Eq, And, Not, Or, Imp, Iff, Ex, All, AllIn, ExIn, conj, disj
import arith as A
import parse as P
import ordinals as OR
import metacode as MC
import semantics as SM
import structure as ST

# ---------- 補助 ----------
def _varset(ctx, s, h, Ns):
    """Ns = s（長さ h の記号列）に現れる変数の添字の集合。"""
    p, k = ctx.fresh(2)
    at = lambda i, pred: A.lookup(ctx, s, i, pred)
    vi = lambda t, b: And(P.is_var(ctx, t), P.comp(ctx, t, 2, b))
    return And(AllIn(k, Ns, ExIn(p, h, at(p, lambda t: vi(t, lambda kk: Eq(kk, k))))),
               AllIn(p, h, at(p, lambda t: Imp(P.is_var(ctx, t), P.comp(ctx, t, 2, lambda kk: In(kk, Ns))))))

def _func_on(ctx, f, K, X):
    """f は K から X への関数（順序対の集合）。"""
    q, k = ctx.fresh(2)
    return conj(
        AllIn(q, f, A.pair_parts(ctx, q, lambda k_, a_: And(In(k_, K), In(a_, X)))),
        AllIn(k, K, A.lookup(ctx, f, k, lambda a_: Eq(a_, a_))),
        A.all_pairs(ctx, f, lambda _1, k1, a1: A.all_pairs(ctx, f, lambda _2, k2, a2:
            Imp(Eq(k1, k2), Eq(a1, a2)))))

def _in_pair(ctx, X, a, b):
    q = ctx.fresh()
    return ExIn(q, X, A.pair(ctx, q, a, b))

def pure(ctx, s, h):
    """s の記号はどれも定数・関数・関係記号ではない。"""
    p = ctx.fresh()
    return AllIn(p, h, A.lookup(ctx, s, p, lambda t: conj(
        Not(P.is_const(ctx, t)), Not(P.is_func(ctx, t)), Not(P.is_rel(ctx, t)))))

def def_code(ctx, n):
    """n は純粋な式の番号。"""
    if ctx.use_oracle("def_code"):
        return Oracle("def_code", [n])
    s, h = ctx.fresh(2)
    return Ex(s, conj(P.formula(ctx, s, True), MC.metacode(ctx, n, s),
                      Ex(h, And(P.seq_with(ctx, s, h, lambda t: Eq(t, t)), pure(ctx, s, h)))))

# ---------- 定義可能性 ----------
def defines(ctx, n, tau, X, y):
    """(n, τ) は X 上で y を定義する。"""
    if ctx.use_oracle("defines"):
        return Oracle("defines", [n, tau, X, y])
    s, h, Ns, K, E, Z, z, sg, k, q = ctx.fresh(10)
    # K = Ns ∖ {0}
    kdef = And(AllIn(k, K, And(In(k, Ns), Not(A.empty(ctx, k)))),
               AllIn(k, Ns, Or(A.empty(ctx, k), In(k, K))))
    # σ = τ ∪ {(0, z)}
    def sigma_is(sg_):
        return conj(
            AllIn(q, sg_, Or(In(q, tau), A.pair_parts(ctx, q, lambda k_, a_: And(A.empty(ctx, k_), Eq(a_, z))))),
            AllIn(q, tau, In(q, sg_)),
            ExIn(q, sg_, A.pair_parts(ctx, q, lambda k_, a_: And(A.empty(ctx, k_), Eq(a_, z)))))
    satz = Ex(sg, And(sigma_is(sg), SM.sat(ctx, s, X, E, Z, Z, Z, sg, extended=True)))
    body = conj(
        AllIn(z, y, In(z, X)),
        AllIn(z, X, Iff(In(z, y), satz)))
    return Ex(s, conj(
        P.formula(ctx, s, True), MC.metacode(ctx, n, s),
        Ex(h, conj(P.seq_with(ctx, s, h, lambda t: Eq(t, t)), pure(ctx, s, h),
            Ex(Ns, conj(_varset(ctx, s, h, Ns),
                Ex(K, conj(kdef, _func_on(ctx, tau, K, X),
                    Ex(Z, And(A.empty(ctx, Z), Ex(E, And(ST.e_restrict(ctx, X, E), body))))))))))))

def lex_less(ctx, tau, tau2, Wg):
    """τ が τ′ より辞書式で小さい（同じ定義域、添字の小さい順、<_β は Wg）。"""
    q, q2, r = ctx.fresh(3)
    def at_k(k, u):
        def rest(k2, u2):
            def agree(j, v):
                return Imp(In(j, k), ExIn(q2, tau2, A.pair(ctx, q2, j, v)))
            return conj(Eq(k2, k), _in_pair(ctx, Wg, u, u2),
                        AllIn(r, tau, A.pair_parts(ctx, r, agree)))
        return ExIn(q2, tau2, A.pair_parts(ctx, q2, rest))
    return ExIn(q, tau, A.pair_parts(ctx, q, at_k))

def def_less(ctx, n, tau, n2, tau2, Wg):
    return Or(In(n, n2), And(Eq(n, n2), lex_less(ctx, tau, tau2, Wg)))

def _def_entry(ctx, q, body):
    """q = ((n, τ), y) のとき body(n, τ, y)。"""
    return A.pair_parts(ctx, q, lambda nt, y_: A.pair_parts(ctx, nt, lambda n_, t_: body(n_, t_, y_)))

def def_table(ctx, X, DT):
    """DT = { ((n, τ), y) : n は純粋な式の番号で、(n, τ) は X 上で y を定義する }。"""
    if ctx.use_oracle("def_table"):
        return Oracle("def_table", [X, DT])
    q, n, t, y, r = ctx.fresh(5)
    shape = AllIn(q, DT, _def_entry(ctx, q, lambda n_, t_, y_: def_code(ctx, n_)))
    full = All(n, Imp(def_code(ctx, n), All(t, All(y, Iff(defines(ctx, n, t, X, y),
               ExIn(r, DT, A.triple(ctx, r, n, t, y)))))))
    return And(shape, full)

def new_less(ctx, a, b, DT, Wg):
    """X に新しく加わった a, b について、a の最小の定義 ≺ b の最小の定義（DT は X 上の定義の表）。"""
    q, q2 = ctx.fresh(2)
    return ExIn(q, DT, _def_entry(ctx, q, lambda n, t, y: And(Eq(y, a),
           AllIn(q2, DT, _def_entry(ctx, q2, lambda n2, t2, y2: Imp(Eq(y2, b),
               def_less(ctx, n, t, n2, t2, Wg)))))))

def step(ctx, X, Wg, X1, W1):
    """X1 = Def(X)、W1 = <_{β+1}（X, Wg は L_β と <_β）。"""
    if ctx.use_oracle("step"):
        return Oracle("step", [X, Wg, X1, W1])
    DT, y, a, b, q = ctx.fresh(5)
    defn = And(AllIn(y, X1, ExIn(q, DT, _def_entry(ctx, q, lambda n_, t_, y_: Eq(y_, y)))),
               AllIn(q, DT, _def_entry(ctx, q, lambda n_, t_, y_: In(y_, X1))))
    shape = AllIn(q, W1, A.pair_parts(ctx, q, lambda a_, b_: And(In(a_, X1), In(b_, X1))))
    def rule(a_, b_):
        old = conj(In(a_, X), In(b_, X), _in_pair(ctx, Wg, a_, b_))
        cross = And(In(a_, X), Not(In(b_, X)))
        new = conj(Not(In(a_, X)), Not(In(b_, X)), new_less(ctx, a_, b_, DT, Wg))
        return Iff(_in_pair(ctx, W1, a_, b_), disj(old, cross, new))
    return Ex(DT, conj(def_table(ctx, X, DT), defn, shape, AllIn(a, X1, AllIn(b, X1, rule(a, b)))))

def l_order(ctx, lam, D, WL):
    """D = L_λ、WL = <_λ（WL は順序対 (a, b)、a <_L b の集合）。"""
    if ctx.use_oracle("l_order"):
        return Oracle("l_order", [lam, D, WL])
    l1, T, g, g1, x, q = ctx.fresh(6)
    at_T = lambda b, body: A.lookup(ctx, T, b, lambda p: A.pair_parts(ctx, p, body))
    def value_ok(gm, X, W):
        zero = Imp(A.empty(ctx, gm), And(A.empty(ctx, X), A.empty(ctx, W)))
        succ = AllIn(g1, gm, Imp(A.succ_of(ctx, g1, gm), at_T(g1, lambda X0, W0: step(ctx, X0, W0, X, W))))
        def union(sel):   # sel(X0, W0) が X0 または W0
            Y = sel(X, W)
            return And(AllIn(x, Y, ExIn(g1, gm, at_T(g1, lambda X0, W0: In(x, sel(X0, W0))))),
                       AllIn(g1, gm, at_T(g1, lambda X0, W0: AllIn(x, sel(X0, W0), In(x, Y)))))
        limit = Imp(And(Not(A.empty(ctx, gm)), Not(OR.is_succ(ctx, gm))),
                    And(union(lambda X_, W_: X_), union(lambda X_, W_: W_)))
        return conj(zero, succ, limit)
    is_func = conj(
        AllIn(q, T, A.pair_parts(ctx, q, lambda a_, b_: In(a_, l1))),
        A.all_pairs(ctx, T, lambda _1, a1, b1: A.all_pairs(ctx, T, lambda _2, a2, b2:
            Imp(Eq(a1, a2), Eq(b1, b2)))))
    body = conj(is_func, AllIn(g, l1, at_T(g, lambda X, W: value_ok(g, X, W))),
                at_T(lam, lambda X, W: And(Eq(X, D), Eq(W, WL))))
    return And(OR.ordinal(ctx, lam), Ex(l1, And(A.succ_of(ctx, lam, l1), Ex(T, body))))

# ---------- Θ ----------
def least_good(ctx, s, v, D, E, Cn, Fn, Rel, WL):
    """v は、式 s について good な元のうち <_λ で最小のもの。"""
    if ctx.use_oracle("least_good"):
        return Oracle("least_good", [s, v, D, E, Cn, Fn, Rel, WL])
    h, Ns, Z, sg, sg2, sg3, i, a, k = ctx.fresh(9)
    def assign(x):
        return _func_on(ctx, x, Ns, D)
    def update(x, kk, val, x2):            # x2 = x[kk := val]
        return conj(assign(x2), A.lookup(ctx, x2, kk, lambda b: Eq(b, val)),
                    A.all_pairs(ctx, x, lambda _, k1, b1: Or(Eq(k1, kk),
                        A.lookup(ctx, x2, k1, lambda b2: Eq(b2, b1)))))
    zdef = All(sg, Iff(In(sg, Z), And(assign(sg), SM.sat(ctx, s, D, E, Cn, Fn, Rel, sg))))
    def dep_only(i_):
        return AllIn(sg, Z, All(sg2, Imp(And(assign(sg2), A.lookup(ctx, sg, i_, lambda u:
                   A.lookup(ctx, sg2, i_, lambda u2: Eq(u, u2)))), In(sg2, Z))))
    def good(a_):
        return AllIn(i, Ns, Imp(And(dep_only(i), Ex(sg, In(sg, Z))),
               All(sg, Imp(assign(sg), Ex(sg3, And(update(sg, i, a_, sg3), In(sg3, Z)))))))
    least = AllIn(a, D, Imp(good(a), Or(Eq(a, v), _in_pair(ctx, WL, v, a))))
    return Ex(h, And(P.seq_with(ctx, s, h, lambda t: Eq(t, t)), Ex(Ns, conj(
        _varset(ctx, s, h, Ns), Ex(Z, conj(zdef, In(v, D), good(v), least))))))

def theta_L(ctx, D, E, Cn, Fn, Rel, WL):
    """Fn の Θ の部分が上の規則に従う。"""
    if ctx.use_oracle("theta_L"):
        return Oracle("theta_L", [D, E, Cn, Fn, Rel, WL])
    m, v, s = ctx.fresh(3)
    val = Or(Ex(s, conj(P.formula(ctx, s, True), MC.metacode(ctx, m, s),
                        least_good(ctx, s, v, D, E, Cn, Fn, Rel, WL))),
             And(Not(MC.formula_code(ctx, m, minus=True)), A.empty(ctx, v)))
    return AllIn(m, D, ExIn(v, D, And(ST.theta_value(ctx, Fn, m, v), val)))

def struct_rec(ctx, alpha, SU):
    """SU は α+1 上の関数で、各 γ ≤ α について SU(γ) = ((D, E), (Cn, (Fn, Rel))) は候補解釈 I の下での U(γ)。
    U(γ) の中の ┌U┐ の値は、β ∈ γ なら構造 SU(β) そのもの（原文の U2）。γ に関する再帰。"""
    if ctx.use_oracle("struct_rec"):
        return Oracle("struct_rec", [alpha, SU])
    import inacc_seq as IS
    a1, g, lam, WL, q = ctx.fresh(5)
    def level(g_, D, E, Cn, Fn, Rel):
        return Ex(lam, conj(
            IS.lam_of(ctx, g_, lam), ST.vstage(ctx, lam, D),
            ST.e_restrict(ctx, D, E), ST.cn_ok(ctx, Cn), ST.rel_empty(ctx, Rel), ST.fn_ok(ctx, Fn, D, g_, SU),
            Ex(WL, And(l_order(ctx, lam, D, WL), theta_L(ctx, D, E, Cn, Fn, Rel, WL)))))
    is_func = conj(
        AllIn(q, SU, A.pair_parts(ctx, q, lambda a_, b_: In(a_, a1))),
        A.all_pairs(ctx, SU, lambda _1, x1, y1: A.all_pairs(ctx, SU, lambda _2, x2, y2:
            Imp(Eq(x1, x2), Eq(y1, y2)))))
    return Ex(a1, conj(A.succ_of(ctx, alpha, a1), is_func,
        AllIn(g, a1, A.lookup(ctx, SU, g, lambda x: ST.struct_parts(ctx, x,
            lambda D, E, Cn, Fn, Rel: level(g, D, E, Cn, Fn, Rel))))))

def struct_full(ctx, i, D, E, Cn, Fn, Rel):
    """(D, E, Cn, Fn, Rel) は候補解釈 I の下での U(CNF(i))（Θ を含めて一意。改訂31 で ┌U┐ の値を構造そのものに改めた）。"""
    if ctx.use_oracle("struct_full"):
        return Oracle("struct_full", [i, D, E, Cn, Fn, Rel])
    import inacc_seq as IS
    alpha, SU = ctx.fresh(2)
    return Ex(alpha, And(IS.ord_of(ctx, i, alpha), Ex(SU, And(struct_rec(ctx, alpha, SU),
        A.lookup(ctx, SU, alpha, lambda x: ST.struct_parts(ctx, x, lambda D2, E2, Cn2, Fn2, Rel2:
            conj(Eq(D2, D), Eq(E2, E), Eq(Cn2, Cn), Eq(Fn2, Fn), Eq(Rel2, Rel))))))))
