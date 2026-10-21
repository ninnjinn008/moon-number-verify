"""
原文の CNF : ℕ → ε0 を、順序数を集合として作らずに表す。

■ 原文
  CNF(0) = 0。i ≠ 0 なら、i+1 を割る最小の素数を p、i+1 が p で割り切れる回数を v、
  (i+1)/p^v = j として、CNF(i) = ω^{CNF(v−1)} + CNF(j−1)。

■ 方針
  自然数 i を「順序数 CNF(i) の名前」として扱い、名前どうしの大小だけを有限の計算で決める。
  U(α) に必要なのは α 番目の到達不能基数であり、その定義に使うのは順序数の大小だけである。

  dec(i, a, b)  ：i > 0 のとき a = v−1、b = j−1（CNF(i) = ω^{CNF(a)} + CNF(b)）
  正規化した先頭：i > 0 について、CNF(i) = ω^{CNF(H)} + CNF(R) かつ CNF(R) の先頭の指数 ≤ CNF(H)
                  となる名前の組 (H, R)。b = 0 なら (a, 0)。b > 0 で CNF(H(b)) > CNF(a) なら
                  ω^{CNF(a)} は吸収されて (H(b), R(b))。そうでなければ (a, b)。
  比較          ：cmp(i, k) ∈ {0: <, 1: =, 2: >}。0 は最小。両方正なら先頭の指数を比べ、等しければ残りを比べる。
  これらを「計算表」T の存在で表す。T の行は長さ 4 の自然数の列で、
    (0, i, H, R) … i の正規化した先頭、 (1, i, k, c) … cmp(i, k) = c。
  各行は、より小さい名前についての行だけを使う規則で正当化される（a, b, H, R はすべて i より小さい）。
  健全性は名前の大きさに関する帰納法、完全性は必要な行をすべて集めた表が証人になることによる。
  表は遺伝的有限集合なので M に属する。
"""
from fol import Oracle, In, Eq, And, Not, Or, Imp, Ex, All, AllIn, ExIn, conj, disj
import arith as A
import parse as P

def dec(ctx, i, a, b):
    """i > 0 のとき a = v−1、b = j−1。"""
    if ctx.use_oracle("dec"):
        return Oracle("dec", [i, a, b])
    i1, p, v, pv, j, q = ctx.fresh(6)
    inner_j = conj(A.mul(ctx, pv, j, i1),                     # i1 = p^v · j
                   A.succ_of(ctx, b, j),                      # j = b + 1
                   Not(A.divides(ctx, p, j)))                 # p は j を割らない（v が最大）
    inner_pv = And(A.exp(ctx, p, v, pv), Ex(j, inner_j))      # pv = p^v
    inner_v = And(A.succ_of(ctx, a, v), Ex(pv, inner_pv))     # v = a + 1
    least = AllIn(q, p, Not(And(A.prime(ctx, q), A.divides(ctx, q, i1))))   # より小さい素数は割らない
    inner_p = conj(A.prime(ctx, p), A.divides(ctx, p, i1), least, Ex(v, inner_v))
    return And(Not(A.empty(ctx, i)), Ex(i1, And(A.succ_of(ctx, i, i1), Ex(p, inner_p))))

def row_shape(ctx, r, k0):
    """r は長さ 4 の自然数の列で、第 0 成分が k0。"""
    if ctx.use_oracle("row"):
        return Oracle(f"rowshape:{k0}", [r])
    four = ctx.fresh()
    return And(Ex(four, And(A.numeral(ctx, four, 4), P.seq_with(ctx, r, four, lambda u: A.nat(ctx, u)))),
               P.comp(ctx, r, 0, lambda u: A.numeral(ctx, u, k0)))

def row_get(ctx, T, k0, keys, body):
    """T の行 (k0, keys…, 値…) をとり、残りの成分を有界に束縛して body(値…) を述べる。"""
    r = ctx.fresh()
    parts = [row_shape(ctx, r, k0)]
    for idx, kv in enumerate(keys, start=1):
        parts.append(P.comp(ctx, r, idx, (lambda kv_: lambda u: Eq(u, kv_))(kv)))
    rest = list(range(1 + len(keys), 4))
    def bind(idxs, acc):
        if not idxs:
            return body(*acc)
        return P.comp(ctx, r, idxs[0], lambda u: bind(idxs[1:], acc + [u]))
    parts.append(bind(rest, []))
    return ExIn(r, T, conj(*parts))

def row_is(ctx, r, k0, x, y, z):
    """r = (k0, x, y, z)：長さ 4 の自然数の列。"""
    return conj(row_shape(ctx, r, k0),
                P.comp(ctx, r, 1, lambda u: Eq(u, x)),
                P.comp(ctx, r, 2, lambda u: Eq(u, y)),
                P.comp(ctx, r, 3, lambda u: Eq(u, z)))

def table_ok(ctx, T):
    """T の各行が正当化されている。"""
    if ctx.use_oracle("cnf_table"):
        return Oracle("cnf_table", [T])
    num = lambda v, k: A.numeral(ctx, v, k)

    def hr_ok(i, h, rr):
        a, b = ctx.fresh(2)
        def with_b(hb, rb):                     # T の行 (0, b, hb, rb) と (1, hb, a, c) から
            return row_get(ctx, T, 1, [hb, a], lambda c:
                   Or(conj(num(c, 2), Eq(h, hb), Eq(rr, rb)),               # CNF(H(b)) > CNF(a)：吸収
                      conj(Not(num(c, 2)), Eq(h, a), Eq(rr, b))))
        case_b0 = conj(A.empty(ctx, b), Eq(h, a), A.empty(ctx, rr))         # b = 0：(a, 0)
        case_b = And(Not(A.empty(ctx, b)), row_get(ctx, T, 0, [b], with_b))
        # a, b はともに i より小さい
        return ExIn(a, i, ExIn(b, i, And(dec(ctx, i, a, b), Or(case_b0, case_b))))

    def cmp_ok(i, k, c):
        def step(hi, ri):
            return row_get(ctx, T, 0, [k], lambda hk, rk:
                   row_get(ctx, T, 1, [hi, hk], lambda c1:
                   Or(And(Not(num(c1, 1)), Eq(c, c1)),                       # 先頭の指数が違えばその結果
                      And(num(c1, 1), row_get(ctx, T, 1, [ri, rk], lambda c2: Eq(c2, c))))))  # 等しければ残り
        both = conj(Not(A.empty(ctx, i)), Not(A.empty(ctx, k)), row_get(ctx, T, 0, [i], step))
        return disj(conj(A.empty(ctx, i), A.empty(ctx, k), num(c, 1)),
                    conj(A.empty(ctx, i), Not(A.empty(ctx, k)), num(c, 0)),
                    conj(Not(A.empty(ctx, i)), A.empty(ctx, k), num(c, 2)),
                    both)

    r = ctx.fresh()
    def per_row(kk, xv, yv, zv):
        return Or(And(num(kk, 0), hr_ok(xv, yv, zv)), And(num(kk, 1), cmp_ok(xv, yv, zv)))
    fields = P.comp(ctx, r, 0, lambda kk: P.comp(ctx, r, 1, lambda xv: P.comp(ctx, r, 2, lambda yv:
             P.comp(ctx, r, 3, lambda zv: per_row(kk, xv, yv, zv)))))
    return AllIn(r, T, fields)

def cnf_cmp(ctx, i, k, c):
    """CNF(i) と CNF(k) の比較結果が c（0: <, 1: =, 2: >）。"""
    if ctx.use_oracle("cnf_cmp"):
        return Oracle("cnf_cmp", [i, k, c])
    T = ctx.fresh()
    return Ex(T, And(table_ok(ctx, T), row_get(ctx, T, 1, [i, k], lambda c2: Eq(c2, c))))

def cnf_lt(ctx, i, k):
    c = ctx.fresh()
    return Ex(c, And(A.numeral(ctx, c, 0), cnf_cmp(ctx, i, k, c)))
