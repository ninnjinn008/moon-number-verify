"""
独立の答え合わせ役による照合（改訂34）。

indep/reference.py は、既存のコードを見ていない別のエージェントが、仕様書 indep/SPEC.md だけから書いた実装である。
ここでは、生成した判定式（下の層は検証済みの代用関係）の評価結果を、その独立の実装と照合する。
これまでのテストでは、判定式と答え合わせ役を同じ書き手（本書）が書いていたため、同じ思い込みを共有する恐れがあった。

照合するもの：
  F  整形判定 Formula・Formula₋（parse.py）            ↔ reference.is_formula
  S  充足関係 sat（semantics.py）                        ↔ reference.sat
  D  IsDefinition・Definable（definable.py）             ↔ reference.definable（sat の代用も reference.sat）
  P  定義可能な部分集合 defines（lorder.py）             ↔ reference.defines
  Θ  Θ の規則 theta_L（lorder.py）                       ↔ reference.theta、さらに reference.henkin_ok
既存のテストの宇宙の作り方（証人の候補と偽物）はそのまま使い、「期待値」と「sat の代用」だけを差し替える。
証人の候補は本書の実装から作るが、判定式は証人の正しさを自分で検査するので、候補が間違っていれば判定式は偽を返し、
独立の実装との不一致として現れる。
"""
import inspect, random, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "indep"))
import reference as REF
from fol import Ctx, Evaluator, transitive_closure, nat, to_nat
import parse as P
import test_parse as T
import test_sat as TS
import test_definable as TD
import test_lorder as TL

def patch(func, replacements, namespace):
    src = inspect.getsource(func)
    for a, b in replacements:
        assert src.count(a) == 1, (func.__name__, a)
        src = src.replace(a, b)
    exec(compile(src, f"<patched {func.__name__}>", "exec"), namespace)

# ---------- F ----------
def part_F(seed=11, n_pos=14, n_neg=20, maxlen=9):
    r = random.Random(seed)
    cases = []
    while sum(1 for c in cases if REF.is_formula(c)) < n_pos:
        s = T.gen_formula(r, 2)
        if len(s) <= maxlen and s not in cases: cases.append(s)
    k = 0
    while k < n_neg:
        s = T.mutate(r, r.choice(cases)) if r.random() < 0.6 else [r.choice(T.ALL_SYMS) for _ in range(r.randint(1, 7))]
        if 1 <= len(s) <= maxlen and s not in cases: cases.append(s); k += 1
    cases += [f for f, _ in T.FIXED]
    ctx = Ctx(oracles=T.LOW, start=1); vs = ctx.fresh()
    fm, fmm = P.formula(ctx, vs, False), P.formula(ctx, vs, True)
    bad = 0
    for s in cases:
        h = len(s)
        Mstar = {x for x in T.derive(s) if x[0] <= h + 1 and x[1] <= h + 1 and x[2] <= 4}
        liar = Mstar | {(0, h, 1)}
        D = transitive_closure({T.sset(s), T.cset(Mstar), T.cset(liar)} | {nat(k) for k in range(h + 3)})
        ev = Evaluator(D, T.ORC)
        for f, minus in ((fm, False), (fmm, True)):
            if ev.ev(f, {vs: T.sset(s)}) != REF.is_formula(s, minus=minus):
                bad += 1; print("  NG Formula", "₋" if minus else "", s)
    return bad, 2 * len(cases), sum(1 for c in cases if REF.is_formula(c))

# ---------- S ----------
patch(TS.run_case, [("want = ev_form(whole, M, sg)", "want = REF.sat(s, M, sg)")], TS.__dict__)
TS.REF = REF
def part_S(seed=7, n_rand=8, maxlen=11):
    TS.LIGHT = True
    import semantics
    TS.build(semantics)
    r = random.Random(seed)
    cases = list(TS.FIXED)
    while len(cases) < len(TS.FIXED) + n_rand:
        s = T.gen_formula(r, 2)
        if len(s) <= maxlen and s not in cases: cases.append(s)
    bad = total = 0
    import multiprocessing as mp
    ctxm = mp.get_context("fork")
    for s in cases:
        M = TS.random_struct(r, 2)
        with ctxm.Pool(1) as pool:
            b, n, _ = pool.apply(TS._case_worker, (s, M, r.randrange(10 ** 9), False))
        bad += b; total += n
    M = TS.random_struct(r, 2); M.E = {(M.dom[0], M.dom[0])}
    with ctxm.Pool(1) as pool:
        b, n, _ = pool.apply(TS._case_worker, (TS.FIXED[0], M, r.randrange(10 ** 9), False))
    return bad + b, total + n, len(cases) + 1

# ---------- D ----------
patch(TD.sat_oracle, [("return TS.ev_form(TS.parse_whole(P, \"F\"), M, d)", "return REF.sat(P, M, d)")], TD.__dict__)
patch(TD.run, [("want = ref_definable(TS.parse_whole(P, \"F\"), M, m)", "want = REF.definable(m, M, P)")], TD.__dict__)
TD.ORC["sat_ext"] = TD.raw(TD.sat_oracle)
TD.REF = REF
def part_D(seed=5, n_rand=6):
    r = random.Random(seed)
    Ms = TD.structures(r)
    cases = list(TD.FIXED.values())
    while len(cases) < len(TD.FIXED) + n_rand:
        Pf = T.gen_formula(r, 2)
        if len(Pf) <= 10 and Pf not in cases: cases.append(Pf)
    bad = total = 0
    for Pf in cases:
        for M in Ms:
            b, n = TD.run(Pf, M); bad += b; total += n
    return bad, total, len(cases)

# ---------- P と Θ ----------
TL.ref_sat = lambda Pf, M, d: REF.sat(Pf, M, d)       # sat の代用を独立の実装に
patch(TL.sat_oracle, [("return TS.ev_form(TS.parse_whole(P, \"F\"), M, d)", "return REF.sat(P, M, d)")], TL.__dict__)
patch(TL.test_defines, [
    ("want_y = frozenset(z for z in X if ref_sat(P, M, {**d, 0: z})) if (ok_tau and pure) else None",
     "want_y = REF.defines(P, d, X) if pure else None"),
    ("want = pure and ok_tau and y == want_y", "want = pure and want_y is not None and y == want_y")], TL.__dict__)
TL.REF = REF
HENKIN = []
def ref_theta_indep(codes, M, D, lst):
    out = {}
    for m in D:
        k = to_nat(m)
        if k is None or k not in codes:
            out[m] = frozenset(); continue
        out[m] = REF.theta(codes[k], M, lst)
        HENKIN.append(REF.henkin_ok(codes[k], M, out[m]))
    return out
TL.ref_theta = ref_theta_indep
def part_P():
    b, t = TL.test_defines(); return b, t
def part_T():
    bad = total = 0
    for name, codes in TL.CONFIGS.items():
        b, t, _ = TL.test_theta(name, codes); bad += b; total += t
    return bad, total

# ---------- L の段階と ┌U┐ の値（SPEC2） ----------
import test_struct_rec as TR
def _ref_step(X, lst):
    return REF.next_level(X, list(lst), [(n, d, y) for n, d, y in TL.toy_defs(X)])
def part_L():
    TL.ref_step = _ref_step
    b1, t1 = TL.test_step()
    b2, t2, sizes = TL.test_lorder()
    return b1 + b2, t1 + t2, sizes
patch(TR.test_fn_su, [("e[(T4(U_), seq([x]))] = uval(x, d)", "e[(T4(U_), seq([x]))] = REF.u_values(Dm, 2, d)[x]")], TR.__dict__)
patch(TR.toyFn, [("out.add(pair(seq([x]), sud[k] if (k is not None and k < g) else frozenset()))",
                  "out.add(pair(seq([x]), REF.u_values(Dlev(g), g, sud)[x] if all(j in sud for j in range(g)) else nat(99)))")], TR.__dict__)
TR.REF = REF
def part_U():
    b1, t1 = TR.test_fn_su()
    b2, t2 = TR.test_rec()
    return b1 + b2, t1 + t2

def main():
    out = 0
    b, t, npos = part_F(); out += b
    print(f"F  Formula・Formula₋：列 {t // 2} 個（うち論理式 {npos} 個）、判定 {t} 回で {'すべて一致' if b == 0 else str(b) + ' 件の不一致'}", flush=True)
    b, t, nc = part_S(); out += b
    print(f"S  充足関係：論理式 {nc} 個、判定 {t} 回で {'すべて一致' if b == 0 else str(b) + ' 件の不一致'}", flush=True)
    b, t, nc = part_D(); out += b
    print(f"D  Definable：式 {nc} 個、判定 {t} 回で {'すべて一致' if b == 0 else str(b) + ' 件の不一致'}", flush=True)
    b, t = part_P(); out += b
    print(f"P  defines・def_code：判定 {t} 回で {'すべて一致' if b == 0 else str(b) + ' 件の不一致'}", flush=True)
    b, t = part_T(); out += b
    hk = all(HENKIN)
    print(f"Θ  theta_L：判定 {t} 回で {'すべて一致' if b == 0 else str(b) + ' 件の不一致'}。独立の実装による Henkin 公理の検査：{len(HENKIN)} 件中 {sum(HENKIN)} 件成立", flush=True)
    out += 0 if hk else 1
    if hasattr(REF, "next_level"):
        b, t, sizes = part_L(); out += b
        print(f"L  step・l_order：|L_λ| = {sizes}、判定 {t} 回で {'すべて一致' if b == 0 else str(b) + ' 件の不一致'}", flush=True)
    if hasattr(REF, "u_values"):
        b, t = part_U(); out += b
        print(f"U  ┌U┐ の値（fn_ok の SU 版・struct_rec）：判定 {t} 回で {'すべて一致' if b == 0 else str(b) + ' 件の不一致'}", flush=True)
    return out

if __name__ == "__main__":
    import resource; resource.setrlimit(resource.RLIMIT_AS, (6_000_000_000, 6_000_000_000))
    b = main()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)
