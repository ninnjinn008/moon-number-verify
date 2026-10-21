"""
lorder.py の検証。三層に分ける。

層 1（段階と順序の再帰）：
  定義可能性を「おもちゃの定義」に差し替える（番号 0〜3 の 4 通り）。
    0：∅（パラメータなし）  1：{p₁}  2：p₁ の元全体（= p₁）  3：{p₁, p₂}
  Python で L_0 〜 L_4 と順序を独立に計算し（新しい元は最小の定義の順）、
  1a. step(X, <, X′, <′) が正しい次の段を受理し、偽の次の段（新しい元の順序の入れ替え、
      古い元と新しい元の入れ替え、組の欠け、元の欠け）を拒否すること
  1b. l_order(λ, D, W) が λ = 0〜4 で正しい (L_λ, <_λ) を受理し、偽の順序・一つ前の段を拒否すること
  を確かめる（1b では step を答え合わせ役の代用関係にする）。
層 2（定義可能性 defines と純粋な式の判定 def_code）：
  本物の記号列の式を使い、充足関係 sat は Python の評価器に差し替える（test_sat.py で検証済み）。
  X = V_2, V_3 で、式とパラメータとすべての部分集合 y について、defines が総当たりの答えと一致すること、
  定数を含む式（純粋でない）と Θ を含む式が def_code で拒否されることを確かめる。
層 3（Θ の解釈 theta_L）：
  D = V_3 に、わざと ∅ が最小でない整列順序を与え、番号 0, 1, 2 に式を割り当てた三通りの構成で、
  正しい Θ を受理し、Θ(m) の値を一つ変えた表（各 m について他のすべての値）をすべて拒否することを確かめる。
  式の番号は代用（本物の MetaCode は大きすぎて有限の宇宙に入らない。test_metacode.py と同じ方針）。
有界でない量化子は軽量モード（関係しうる集合の範囲）で動かす。範囲には、関係する部分集合・パラメータ・
割当てをすべて入れてあるので、範囲の外に正しい答えを変える集合はない。極限段階は有限の例に現れない。
"""
import itertools, sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair, to_nat
import lorder as LO
import test_sat as TS
T = TS.T

def raw(f): f.raw = True; return f

def powerset(xs):
    xs = list(xs)
    return [frozenset(c) for r in range(len(xs) + 1) for c in itertools.combinations(xs, r)]

def unpair(q):
    """q = (k, a) を (k, a) に戻す（順序対でなければ None）。"""
    els = list(q)
    if len(els) == 1:
        s = list(els[0])
        return (s[0], s[0]) if len(s) == 1 else None
    if len(els) != 2: return None
    a, b = els if len(els[0]) <= len(els[1]) else els[::-1]
    if len(a) != 1 or len(b) != 2: return None
    (k,) = a
    if k not in b: return None
    (v,) = b - {k}
    return (k, v)

def as_func(t):
    d = {}
    for q in t:
        p = unpair(q)
        if p is None: return None
        k, v = p
        kn = to_nat(k)
        if kn is None or kn in d: return None
        d[kn] = v
    return d

def graph(d): return frozenset(pair(a, b) for a, b in d.items())
def fun(d): return frozenset(pair(nat(k), v) for k, v in d.items())
def order_set(lst): return frozenset(pair(lst[i], lst[j]) for i in range(len(lst)) for j in range(i + 1, len(lst)))

# ================= 層 1 =================
KEYS = {0: (), 1: (1,), 2: (1,), 3: (1, 2)}
def toy_val(n, d):
    if n == 0: return frozenset()
    if n == 1: return frozenset({d[1]})
    if n == 2: return d[1]
    return frozenset({d[1], d[2]})

def toy_taus(n, X):
    ks = KEYS[n]
    return [dict(zip(ks, vals)) for vals in itertools.product(list(X), repeat=len(ks))]

def toy_defs(X):
    """X 上のおもちゃの定義 (n, τ, y) をすべて列挙。"""
    return [(n, d, toy_val(n, d)) for n in range(4) for d in toy_taus(n, X)]

def ref_step(X, lst):
    """X（順序 lst）から次の段とその順序。新しい元は最小の定義の順。"""
    pos = {a: i for i, a in enumerate(lst)}
    best = {}
    for n, d, y in toy_defs(X):
        key = (n, tuple(pos[d[k]] for k in sorted(d)))
        if y not in best or key < best[y]: best[y] = key
    new = sorted([y for y in best if y not in X], key=lambda y: best[y])
    X1 = frozenset(best)
    assert set(lst) <= X1 or not X
    return X1, list(lst) + new

def ref_levels(n):
    lv = [(frozenset(), [])]
    for _ in range(n): lv.append(ref_step(*lv[-1]))
    return lv

def toy_defines(n, tau, X, y):
    k = to_nat(n)
    if k is None or k > 3: return False
    d = as_func(tau)
    if d is None or set(d) != set(KEYS[k]) or not all(v in X for v in d.values()): return False
    return toy_val(k, d) == y

ORC1 = dict(TS.ORC)
ORC1["def_code"] = raw(lambda n: to_nat(n) is not None and to_nat(n) <= 3)
ORC1["defines"] = raw(toy_defines)
LOW1 = TS.LOW | {"def_code", "defines"}

def def_table_set(X):
    return frozenset(pair(pair(nat(n), fun(d)), y) for n, d, y in toy_defs(X))

def test_step():
    lv = ref_levels(4)
    ctx = Ctx(oracles=LOW1, start=1); vX, vW, vX1, vW1 = ctx.fresh(4)
    f = LO.step(ctx, vX, vW, vX1, vW1)
    bad, total = 0, 0
    for b in range(4):
        X, lst = lv[b]; X1, lst1 = lv[b + 1]
        new = [y for y in lst1 if y not in X]
        cands = [(X1, order_set(lst1), True)]
        if len(new) >= 2:
            l2 = list(lst1); i = len(lst); l2[i], l2[i + 1] = l2[i + 1], l2[i]
            cands.append((X1, order_set(l2), False))
            l3 = list(lst1); l3[-1], l3[-2] = l3[-2], l3[-1]
            cands.append((X1, order_set(l3), False))
        if lst and new:
            l4 = list(lst1); i = len(lst); l4[i - 1], l4[i] = l4[i], l4[i - 1]
            cands.append((X1, order_set(l4), False))
        full = order_set(lst1)
        if full:
            cands.append((X1, full - {next(iter(full))}, False))
        if new:
            l5 = [y for y in lst1 if y != new[-1]]
            cands.append((frozenset(l5), order_set(l5), False))
        taus = [fun(d) for n in range(4) for d in toy_taus(n, X)]
        DT = def_table_set(X)
        DTbad = DT - {next(iter(DT))}
        udom = set(taus) | {nat(k) for k in range(6)} | set(powerset(X)) | set(X1) | {DT, DTbad}
        D = transitive_closure(udom | {X, order_set(lst)} | {c[0] for c in cands} | {c[1] for c in cands})
        for X1c, W1c, want in cands:
            got = Evaluator(D, ORC1, udom).ev(f, {vX: X, vW: order_set(lst), vX1: X1c, vW1: W1c})
            total += 1
            if got != want: bad += 1; print("  NG step", b, want, got)
    return bad, total

def test_lorder():
    lv = ref_levels(4)
    ref = {(X, order_set(lst)): ref_step(X, lst) for X, lst in lv[:4]}
    def step_oracle(X, W, X1, W1):
        for (X0, W0), (Xn, ln) in ref.items():
            if X0 == X and W0 == W: return X1 == Xn and W1 == order_set(ln)
        return False
    orc = dict(ORC1); orc["step"] = raw(step_oracle)
    ctx = Ctx(oracles=LOW1 | {"step"}, start=1); vl, vD, vW = ctx.fresh(3)
    f = LO.l_order(ctx, vl, vD, vW)
    bad, total = 0, 0
    for lam in range(5):
        Tgood = graph({nat(b): pair(lv[b][0], order_set(lv[b][1])) for b in range(lam + 1)})
        Tbad = graph({nat(b): pair(lv[b][0], order_set(lv[b][1]) if b != lam else frozenset()) for b in range(lam + 1)})
        X, lst = lv[lam]
        cands = [(X, order_set(lst), True)]
        if len(lst) >= 2:
            l2 = list(lst); l2[0], l2[1] = l2[1], l2[0]
            cands.append((X, order_set(l2), False))
        if lam > 0:
            cands.append((lv[lam - 1][0], order_set(lv[lam - 1][1]), False))
        udom = {Tgood, Tbad} | {nat(k) for k in range(7)}
        D = transitive_closure(udom | {c[0] for c in cands} | {c[1] for c in cands})
        for Xc, Wc, want in cands:
            got = Evaluator(D, orc, udom).ev(f, {vl: nat(lam), vD: Xc, vW: Wc})
            total += 1
            if got != want: bad += 1; print("  NG l_order", lam, want, got)
    return bad, total, [len(x) for x, _ in lv]

# ================= 層 2・層 3 共通 =================
LP, RP, ELEM, NEG, EXI, IMP = T.LP, T.RP, T.ELEM, T.NEG, T.EXI, T.IMP
def V(k): return (7, 1, k, 0)
x0, x1, x2 = V(0), V(1), V(2)
def el(a, b): return [LP, a, ELEM, b, RP]
def ex(v, body): return [EXI, v, LP] + body + [RP]
def imp(p, q): return [LP] + p + [IMP] + q + [RP]
def neg(p): return [NEG] + p

def is_minus(P): return T.TH not in P

def vars_of(P): return sorted({t[2] for t in P if TS.is_var(t)})

_STR, _M = {}, {}
def decode_sigma(sg):
    d = {}
    for q in sg:
        p = unpair(q)
        if p is None: return None
        k = to_nat(p[0])
        if k is None: return None
        d[k] = p[1]
    return d

def sat_oracle(s, dom, E, Cn, Fn, Rel, sg):
    P = _STR[s]; M = _M[(dom, E)]
    d = decode_sigma(sg)
    if d is None or not all(k in d for k in vars_of(P)): return False
    return TS.ev_form(TS.parse_whole(P, "F"), M, d)

def ref_sat(P, M, d): return TS.ev_form(TS.parse_whole(P, "F"), M, d)

def base_orc(codes):
    """codes：番号 → 記号列。"""
    o = dict(TS.ORC)
    sets = {T.sset(P): P for P in codes.values()}
    _STR.update(sets)
    o["sat"] = raw(sat_oracle); o["sat_ext"] = raw(sat_oracle)
    o["formula"] = raw(lambda s: s in sets)
    o["formula_minus"] = raw(lambda s: s in sets and is_minus(sets[s]))
    o["metacode"] = raw(lambda n, s: to_nat(n) in codes and T.sset(codes[to_nat(n)]) == s)
    o["formula_code_minus"] = raw(lambda n: to_nat(n) in codes and is_minus(codes[to_nat(n)]))
    return o
LOW23 = TS.LOW | {"sat", "formula", "metacode", "formula_code"}

def mstruct(X):
    M = TS.Struct(list(X), {(a, b) for b in X for a in b}, {T.C0: frozenset()}, {}, set())
    Eset = frozenset(pair(a, b) for b in X for a in b)
    _M[(frozenset(X), Eset)] = M
    return M, Eset

# ================= 層 2 =================
PURE = [el(x0, x1), el(x1, x0), neg(el(x0, x0)), ex(x2, el(x2, x0) + []) , imp(el(x0, x1), el(x0, x2))]
IMPURE = [el(x0, T.C0), [LP, T.TH, LP, x0, RP, ELEM, x1, RP]]

def test_defines():
    codes = {k: P for k, P in enumerate(PURE + IMPURE)}
    orc = base_orc(codes)
    bad, total = 0, 0
    V2 = [nat(0), nat(1)]; V3 = V2 + [nat(2), frozenset({nat(1)})]
    for X in (frozenset(V2), frozenset(V3)):
        M, Eset = mstruct(X)
        ctx = Ctx(oracles=LOW23, start=1); vn, vt, vX, vy = ctx.fresh(4)
        f = LO.defines(ctx, vn, vt, vX, vy)
        fc = LO.def_code(ctx, vn)
        for n, P in codes.items():
            pure = n < len(PURE)
            Ns = vars_of(P); K = [k for k in Ns if k != 0]
            taus = [dict(zip(K, vals)) for vals in itertools.product(list(X), repeat=len(K))]
            wrong = [dict(list(taus[0].items())[:-1])] if K else [{1: nat(0)}]   # 定義域の違うパラメータ
            ys = powerset(X)
            sigmas = [fun({**d, 0: z}) for d in taus for z in X]
            hset = nat(len(P))
            udom = ({T.sset(P), hset, frozenset(nat(k) for k in Ns), frozenset(nat(k) for k in K), Eset, frozenset()}
                    | {nat(k) for k in range(max(len(P), 6) + 1)} | set(sigmas))
            D = transitive_closure(udom | set(ys) | {fun(d) for d in taus + wrong} | {X})
            ev = Evaluator(D, orc, udom)
            total += 1
            if ev.ev(fc, {vn: nat(n)}) != pure: bad += 1; print("  NG def_code", n)
            for d in taus + wrong:
                ok_tau = set(d) == set(K)
                want_y = frozenset(z for z in X if ref_sat(P, M, {**d, 0: z})) if (ok_tau and pure) else None
                for y in ys:
                    want = pure and ok_tau and y == want_y
                    total += 1
                    if ev.ev(f, {vn: nat(n), vt: fun(d), vX: X, vy: y}) != want:
                        bad += 1; print("  NG defines", n, d, y)
    return bad, total

# ================= 層 3 =================
def ref_theta(codes, M, D, lst):
    out = {}
    for m in D:
        k = to_nat(m)
        if k is None or k not in codes or not is_minus(codes[k]):
            out[m] = frozenset(); continue
        P = codes[k]; Ns = vars_of(P)
        assigns = [dict(zip(Ns, vals)) for vals in itertools.product(list(D), repeat=len(Ns))]
        Z = [a for a in assigns if ref_sat(P, M, a)]
        def good(a):
            for i in Ns:
                dep = all(ref_sat(P, M, s2) == ref_sat(P, M, s1) for s1 in assigns for s2 in assigns if s1[i] == s2[i])
                if dep and Z and not all(ref_sat(P, M, {**s, i: a}) for s in assigns): return False
            return True
        out[m] = next(a for a in lst if good(a))
    return out

CONFIGS = {
    "A": {0: el(x0, x1), 1: ex(x1, el(x1, x0)), 2: neg(ex(x0, el(x0, x2)))},
    "B": {0: neg(ex(x0, el(x0, x0))), 1: el(x1, x1), 2: el(T.C0, x0)},
    "C": {0: [LP, T.TH, LP, x0, RP, ELEM, x1, RP], 1: neg(el(x2, x0) ), 2: imp(el(x1, x1), el(x0, x0))},
}

def test_theta(name, codes, mutate_least=False, mod=LO):
    orc = base_orc(codes)
    D = [nat(0), nat(1), nat(2), frozenset({nat(1)})]
    lst = [frozenset({nat(1)}), nat(2), nat(0), nat(1)]          # ∅ が最小でない整列順序
    M, Eset = mstruct(D)
    Dset = frozenset(D)
    th = ref_theta(codes, M, D, lst)
    one = nat(1)
    def mkFn(vals):
        return frozenset(pair(pair(T.tset(T.TH), frozenset({pair(nat(0), m)})), v) for m, v in vals.items())
    cands = [(mkFn(th), True)]
    for m in D:
        for v in D:
            if v != th[m]: cands.append((mkFn({**th, m: v}), False))
    WL = order_set(lst)
    udom = {nat(k) for k in range(8)} | {Dset, frozenset()}
    for P in codes.values():
        if not is_minus(P):
            udom |= {T.sset(P)}; continue
        Ns = vars_of(P)
        assigns = [dict(zip(Ns, vals)) for vals in itertools.product(D, repeat=len(Ns))]
        Z = frozenset(fun(a) for a in assigns if ref_sat(P, M, a))
        udom |= {T.sset(P), nat(len(P)), frozenset(nat(k) for k in Ns), Z, Z | {fun(assigns[0])}} | {fun(a) for a in assigns}
    Cn = frozenset({pair(T.tset(T.C0), frozenset())})
    Wbad = order_set(lst[::-1])
    allD = transitive_closure(udom | {c[0] for c in cands} | {WL, Cn, Eset} | {frozenset({pair(nat(0), m)}) for m in D})
    ctx = Ctx(oracles=LOW23 | {"sat"}, start=1); vD, vE, vC, vF, vR, vW = ctx.fresh(6)
    f = mod.theta_L(ctx, vD, vE, vC, vF, vR, vW)
    bad = 0
    for Fn, want in cands:
        got = Evaluator(allD, orc, udom).ev(f, {vD: Dset, vE: Eset, vC: Cn, vF: Fn, vR: frozenset(), vW: WL})
        if got != want: bad += 1; print("  NG theta", name, want, got)
    return bad, len(cands), {to_nat(m) if to_nat(m) is not None else "{1}": (to_nat(v) if to_nat(v) is not None else "{1}") for m, v in th.items()}

def main():
    b1, t1 = test_step(); print(f"層 1a step：{t1} 件で {'すべて一致' if b1 == 0 else str(b1) + ' 件の不一致'}")
    b2, t2, sizes = test_lorder(); print(f"層 1b l_order：λ = 0〜4（|L_λ| = {sizes}）、{t2} 件で {'すべて一致' if b2 == 0 else str(b2) + ' 件の不一致'}")
    b3, t3 = test_defines(); print(f"層 2 defines・def_code：{t3} 件で {'すべて一致' if b3 == 0 else str(b3) + ' 件の不一致'}")
    b4 = 0
    for name, codes in CONFIGS.items():
        b, t, th = test_theta(name, codes); b4 += b
        print(f"層 3 theta_L 構成 {name}：Θ = {th}、{t} 件で {'すべて一致' if b == 0 else str(b) + ' 件の不一致'}")
    return b1 + b2 + b3 + b4

def _mut(src, old, new):
    """変異版のソース。置換する箇所がちょうど一か所あることを確かめる（置換の空振りで変異テストが素通りしないように）。"""
    assert src.count(old) == 1, f"変異させる箇所が {src.count(old)} 個（1 個であるべき）: {old.strip()[:60]}"
    return src.replace(old, new)

def mutation():
    import types
    src = open(LO.__file__, encoding="utf-8").read()
    n_det = 0
    # 1. 新しい元の比較で、パラメータの辞書式比較を外す（式の番号だけで比べる）
    a = "    return Or(In(n, n2), And(Eq(n, n2), lex_less(ctx, tau, tau2, Wg)))"
    m1 = types.ModuleType("lo_bad1"); exec(compile(_mut(src, a, "    return In(n, n2)"), "b1", "exec"), m1.__dict__)
    g = LO.step; LO_step_bad = m1.step
    import lorder
    saved = lorder.step; lorder.step = LO_step_bad
    try:
        b, _ = test_step()
    finally:
        lorder.step = saved
    print(f"変異 1（辞書式比較を外す）：{b} 件の不一致を検出"); n_det += bool(b)
    # 2. Θ の good から dep_only を外す（二変数の式でも証人を選ぶ）
    a2 = "        return AllIn(i, Ns, Imp(And(dep_only(i), Ex(sg, In(sg, Z))),"
    m2 = types.ModuleType("lo_bad2"); exec(compile(_mut(src, a2, "        return AllIn(i, Ns, Imp(Ex(sg, In(sg, Z)),"), "b2", "exec"), m2.__dict__)
    b = sum(test_theta(nm, c, mod=m2)[0] for nm, c in CONFIGS.items())
    print(f"変異 2（依存の判定を外す）：{b} 件の不一致を検出"); n_det += bool(b)
    # 3. 最小性を外す
    a3 = "    least = AllIn(a, D, Imp(good(a), Or(Eq(a, v), _in_pair(ctx, WL, v, a))))"
    m3 = types.ModuleType("lo_bad3"); exec(compile(_mut(src, a3, "    least = Eq(v, v)"), "b3", "exec"), m3.__dict__)
    b = sum(test_theta(nm, c, mod=m3)[0] for nm, c in CONFIGS.items())
    print(f"変異 3（最小性を外す）：{b} 件の不一致を検出"); n_det += bool(b)
    return 0 if n_det == 3 else 1

if __name__ == "__main__":
    import resource; resource.setrlimit(resource.RLIMIT_AS, (6_000_000_000, 6_000_000_000))
    b = main()
    if "--mutation" in sys.argv: b += mutation()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)
