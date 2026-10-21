"""
semantics.sat（充足関係）の検証。

答え合わせ役は、test_parse.py の区間 DP とは別に書いた再帰下降の構文解析と評価器である
（判定式と答え合わせ役が同じ誤りを共有しにくいように）。

- ランダムな有限構造（領域 2〜3 元、∈・定数・関数 U, Θ, f_{0,0}, f_{2,0}・関係 r_{1,0}, r_{0,1} の解釈）と、
  文法から生成した論理式について、すべての割当てで sat の値を答え合わせ役と照合する。
- 宇宙には正しい証人（Ns, C, TV, S）のほか、S の項目を一つ反転させた偽物と、TV の値を一つ変えた偽物を入れる。
  判定式が Tarski の条件を正しく課していなければ、偽物が選ばれて値が狂う。
- 下位の部品（順序対・数・記号の判定・証明書）は代用関係に差し替える（それぞれ別に検証済み）。
"""
import random, sys, itertools
from fol import Ctx, Evaluator, transitive_closure, nat, pair
import semantics as SM
import test_parse as T

# ---------- 再帰下降の構文解析（答え合わせ役） ----------
def is_var(t): return t[0] == 7 and t[1] == 1 and t[3] == 0
def is_const(t): return t[0] == 6 and t[1] == 0 and t[3] == 0
def is_func(t): return t in (T.U_, T.TH) or (t[0] == 8 and t[1] == 4)
def is_rel(t): return t[0] == 9 and t[1] == 6

def p_term(s, i):
    if i >= len(s): return None
    t = s[i]
    if is_var(t): return ("var", t[2]), i + 1
    if is_const(t): return ("const", t), i + 1
    if is_func(t):
        if i + 1 >= len(s) or s[i + 1] != T.LP: return None
        args, k = [], i + 2
        for _ in range(t[3]):
            r = p_term(s, k)
            if r is None: return None
            a, k = r; args.append(a)
        if k >= len(s) or s[k] != T.RP: return None
        return ("app", t, args), k + 1
    return None

def p_formula(s, i):
    if i >= len(s): return None
    t = s[i]
    if t == T.BOT: return ("bot",), i + 1
    if t == T.NEG:
        r = p_formula(s, i + 1)
        return None if r is None else (("neg", r[0]), r[1])
    if t == T.EXI:
        if i + 2 >= len(s) or not is_var(s[i + 1]) or s[i + 2] != T.LP: return None
        r = p_formula(s, i + 3)
        if r is None or r[1] >= len(s) or s[r[1]] != T.RP: return None
        return ("exists", s[i + 1][2], r[0]), r[1] + 1
    if is_rel(t):
        if i + 1 >= len(s) or s[i + 1] != T.LP: return None
        args, k = [], i + 2
        for _ in range(t[3]):
            r = p_term(s, k)
            if r is None: return None
            a, k = r; args.append(a)
        if k >= len(s) or s[k] != T.RP: return None
        return ("rel", t, args), k + 1
    if t == T.LP:
        nt = s[i + 1] if i + 1 < len(s) else None
        if nt is not None and (is_var(nt) or is_const(nt) or is_func(nt)):     # 項で始まる → ∈
            r1 = p_term(s, i + 1)
            if r1 is None or r1[1] >= len(s) or s[r1[1]] != T.ELEM: return None
            r2 = p_term(s, r1[1] + 1)
            if r2 is None or r2[1] >= len(s) or s[r2[1]] != T.RP: return None
            return ("elem", r1[0], r2[0]), r2[1] + 1
        r1 = p_formula(s, i + 1)                                                 # 論理式で始まる → →
        if r1 is None or r1[1] >= len(s) or s[r1[1]] != T.IMP: return None
        r2 = p_formula(s, r1[1] + 1)
        if r2 is None or r2[1] >= len(s) or s[r2[1]] != T.RP: return None
        return ("imp", r1[0], r2[0]), r2[1] + 1
    return None

def parse_whole(s, kind):
    r = (p_formula if kind == "F" else p_term)(s, 0)
    return r[0] if r is not None and r[1] == len(s) else None

def parse_list(s, n):
    args, k = [], 0
    for _ in range(n):
        r = p_term(s, k)
        if r is None: return None
        a, k = r; args.append(a)
    return args if k == len(s) else None

# ---------- 評価 ----------
class Struct:
    def __init__(self, dom, E, Cn, Fn, Rel): self.dom, self.E, self.Cn, self.Fn, self.Rel = dom, E, Cn, Fn, Rel

def ev_term(a, M, sg):
    if a[0] == "var": return sg[a[1]]
    if a[0] == "const": return M.Cn[a[1]]
    return M.Fn[(a[1], tuple(ev_term(x, M, sg) for x in a[2]))]

def ev_form(f, M, sg):
    k = f[0]
    if k == "bot": return False
    if k == "neg": return not ev_form(f[1], M, sg)
    if k == "imp": return (not ev_form(f[1], M, sg)) or ev_form(f[2], M, sg)
    if k == "elem": return (ev_term(f[1], M, sg), ev_term(f[2], M, sg)) in M.E
    if k == "rel": return (f[1], tuple(ev_term(x, M, sg) for x in f[2])) in M.Rel
    if k == "exists":
        return any(ev_form(f[2], M, {**sg, f[1]: a}) for a in M.dom)

# ---------- 集合への変換 ----------
def vseq(vals): return frozenset(pair(nat(i), v) for i, v in enumerate(vals))
def sigset(sg): return frozenset(pair(nat(k), a) for k, a in sg.items())

def random_struct(r, ndom):
    dom = [nat(10 + k) for k in range(ndom)]            # 領域の元（自然数とは別の値にする）
    E = {(a, b) for a in dom for b in dom if r.random() < 0.5}
    Cn = {T.C0: r.choice(dom)}
    Fn = {}
    for f in (T.U_, T.TH, T.F0, T.F2):
        for args in itertools.product(dom, repeat=f[3]):
            Fn[(f, args)] = r.choice(dom)
    Rel = {(T.R1, (a,)) for a in dom if r.random() < 0.5}
    if r.random() < 0.5: Rel.add((T.R0, ()))
    return Struct(dom, E, Cn, Fn, Rel)

def struct_sets(M):
    E = frozenset(pair(a, b) for a, b in M.E)
    Cn = frozenset(pair(T.tset(t), v) for t, v in M.Cn.items())
    Fn = frozenset(pair(pair(T.tset(t), vseq(args)), v) for (t, args), v in M.Fn.items())
    Rel = frozenset(pair(T.tset(t), vseq(args)) for t, args in M.Rel)
    return frozenset(M.dom), E, Cn, Fn, Rel

# ---------- 代用関係 ----------
def raw(f): f.raw = True; return f
ORC = dict(T.ORC)
LOW = T.LOW | {"certificate"}

LIGHT = False   # True なら有界でない量化子の範囲を「関係しうる集合」に絞る（軽量モード）

def run_case(s, M, r, n_decoy=12, verbose=False):
    h = len(s)
    whole = parse_whole(s, "F")
    assert whole is not None, s
    Mstar = {x for x in T.derive(s) if x[0] <= h and x[1] <= h and x[2] <= 4}
    Ns = sorted({t[2] for t in s if is_var(t)})
    assigns = [dict(zip(Ns, vals)) for vals in itertools.product(M.dom, repeat=len(Ns))]
    # 正しい証人
    TV, S = set(), set()
    tv_rows = []                                            # (i, j, k, sg, 値の集合, 値の種類)
    for (i, j, k) in Mstar:
        for sg in assigns:
            if k == 0:
                v = ev_term(parse_whole(s[i:j], "T"), M, sg)
                tv_rows.append((i, j, k, sg, v, "term", v))
            elif k >= 2:
                lst = parse_list(s[i:j], k - 2)
                assert lst is not None, (s, i, j, k)
                vals = [ev_term(a, M, sg) for a in lst]
                tv_rows.append((i, j, k, sg, vseq(vals), "list", vals))
            else:
                if ev_form(parse_whole(s[i:j], "F"), M, sg):
                    S.add(pair(pair(nat(i), nat(j)), sigset(sg)))
    tv_elem = lambda i, j, k, sg, v: pair(pair(pair(nat(i), nat(j)), nat(k)), pair(sigset(sg), v))
    TV = {tv_elem(i, j, k, sg, v) for (i, j, k, sg, v, _, _) in tv_rows}
    # 偽物
    decoys = []
    formula_items = [(i, j) for (i, j, k) in Mstar if k == 1]
    for _ in range(n_decoy):
        i, j = r.choice(formula_items); sg = r.choice(assigns)
        decoys.append(frozenset(S ^ {pair(pair(nat(i), nat(j)), sigset(sg))}))
    for sg in assigns:                                      # 頂点だけ反転した偽物は全割当てぶん入れる
        decoys.append(frozenset(S ^ {pair(pair(nat(0), nat(h)), sigset(sg))}))
    for _ in range(n_decoy):                                # TV の値を一つ変えた偽物
        i, j, k, sg, v, kind, raw_v = r.choice(tv_rows)
        if kind == "term":
            others = [a for a in M.dom if a != v]
            if not others: continue
            v2 = r.choice(others)
        else:
            v2 = vseq(raw_v + [M.dom[0]])                      # 列を一つ伸ばした値
        decoys.append(frozenset((TV - {tv_elem(i, j, k, sg, v)}) | {tv_elem(i, j, k, sg, v2)}))
    dom, E, Cn, Fn, Rel = struct_sets(M)
    witnesses = {T.sset(s), dom, E, Cn, Fn, Rel, frozenset(nat(k) for k in Ns), T.cset(Mstar),
                 frozenset(TV), frozenset(S)} | {sigset(sg) for sg in assigns} | set(decoys) | {nat(k) for k in range(h + 3)}
    D = transitive_closure(witnesses)
    orc = dict(ORC)
    orc["certificate"] = raw(lambda s_, C_, K0_, K1_: s_ == T.sset(s) and C_ == T.cset(Mstar) and K0_ == nat(0) and K1_ == nat(1))
    bad = 0
    for sg in assigns:
        udom = None
        if LIGHT:   # 数・割当て・証人の候補（正しいものと偽物）だけ
            udom = {nat(k) for k in range(max(h + 3, 13))} | {sigset(x) for x in assigns} | \
                   {frozenset(nat(k) for k in Ns), T.cset(Mstar), frozenset(TV), frozenset(S)} | set(decoys)
        ev = Evaluator(D, orc, udom)            # 割当てごとに評価器を作り直す（キャッシュを解放してメモリを抑える）
        got = ev.ev(F_SAT, {V_s: T.sset(s), V_dom: dom, V_E: E, V_Cn: Cn, V_Fn: Fn, V_Rel: Rel, V_sg: sigset(sg)})
        want = ev_form(whole, M, sg)
        if got != want:
            bad += 1
            if verbose: print("NG", s, sg, got, want)
    return bad, len(assigns), len(D)

def build(sat_module):
    global F_SAT, V_s, V_dom, V_E, V_Cn, V_Fn, V_Rel, V_sg
    ctx = Ctx(oracles=LOW, start=1)
    V_s, V_dom, V_E, V_Cn, V_Fn, V_Rel, V_sg = ctx.fresh(7)
    F_SAT = sat_module.sat(ctx, V_s, V_dom, V_E, V_Cn, V_Fn, V_Rel, V_sg)

FIXED = [
    [T.EXI, T.X[0], T.LP, T.LP, T.X[0], T.ELEM, T.X[1], T.RP, T.RP],              # ∃x0 ( (x0 ∈ x1) )
    [T.NEG, T.EXI, T.X[0], T.LP, T.R1, T.LP, T.X[0], T.RP, T.RP],                # ¬∃x0 ( r1(x0) )
    [T.LP, T.LP, T.F2, T.LP, T.X[0], T.C0, T.RP, T.ELEM, T.X[1], T.RP, T.IMP, T.BOT, T.RP],   # ((f2(x0 c0) ∈ x1) → ⊥)
    [T.EXI, T.X[1], T.LP, T.EXI, T.X[1], T.LP, T.LP, T.X[1], T.ELEM, T.X[0], T.RP, T.RP, T.RP],  # ∃x1(∃x1((x1 ∈ x0)))：同じ変数の束縛の入れ子
    [T.LP, T.U_, T.LP, T.X[0], T.RP, T.ELEM, T.X[0], T.RP],                      # (U(x0) ∈ x0)
    [T.R0, T.LP, T.RP],
    [T.LP, T.F0, T.LP, T.RP, T.ELEM, T.TH, T.LP, T.C0, T.RP, T.RP],              # (f0() ∈ Θ(c0))
]

def _case_worker(s, M, seed_case, verbose):
    import semantics
    build(semantics)
    return run_case(s, M, random.Random(seed_case), verbose=verbose)

def main(n_rand=8, maxlen=11, seed=7, quick=False, verbose=True):
    import semantics
    build(semantics)
    r = random.Random(seed)
    cases = list(FIXED)
    while len(cases) < len(FIXED) + n_rand:
        s = T.gen_formula(r, 2)
        if len(s) <= maxlen and s not in cases:
            cases.append(s)
    if quick: cases = cases[:6]
    total_bad = total = 0
    import multiprocessing as mp
    ctx_mp = mp.get_context("fork")
    for idx, s in enumerate(cases):
        M = random_struct(r, 2 if len(s) > 8 else r.choice([2, 3]))
        seed_case = r.randrange(10 ** 9)
        # 各例を別のプロセスで評価する（評価器のキャッシュを例ごとに解放するため）
        with ctx_mp.Pool(1) as pool:
            bad, n, nd = pool.apply(_case_worker, (s, M, seed_case, verbose))
        total_bad += bad; total += n
        print(f"  [{idx + 1}/{len(cases)}] 長さ {len(s)}、領域 {len(M.dom)} 元、割当て {n} 通り、宇宙 {nd} 元、不一致 {bad}", flush=True)
    # 狙い撃ちの構造：∈ の解釈を {(a, a)} だけにして、∃ の割当ての取り替えが結果を左右するようにする
    M = random_struct(r, 2); M.E = {(M.dom[0], M.dom[0])}
    with ctx_mp.Pool(1) as pool:
        bad, n, nd = pool.apply(_case_worker, (FIXED[0], M, r.randrange(10 ** 9), verbose))
    total_bad += bad; total += n
    print(f"  [狙い撃ち] ∃x0((x0 ∈ x1))、∈ = {{(a, a)}}、割当て {n} 通り、不一致 {bad}", flush=True)
    print(f"充足関係: 論理式 {len(cases)} 個（＋狙い撃ちの構造 1 例）、判定 {total} 回 → {'すべて一致' if total_bad == 0 else str(total_bad) + ' 件の不一致'}")
    return total_bad


# 変異させる箇所（改訂45 で sat の部品を SatParts のメソッドにしたので、dom・update は self. つき）。
MUT_FROM = "ExIn(a_, self.dom, Ex(sg2, And(self.update(sg, k, a_, sg2), inS(i3, j1, sg2))"
MUT_TO = "ExIn(a_, self.dom, Ex(sg2, And(self.update(sg, k, a_, sg2), inS(i3, j1, sg))"

def bad_semantics():
    """∃ の条件で、取り替えた割当て sg2 ではなく元の sg を使う変異版の semantics。
    置換が一か所で確かに起きたこと、変異版の文字列が元と異なることを確かめる（置換の空振りで検査が素通りしないように）。"""
    import types, semantics
    src = open(semantics.__file__, encoding="utf-8").read()
    assert src.count(MUT_FROM) == 1, f"変異させる箇所が {src.count(MUT_FROM)} 個（1 個であるべき）"
    bad_src = src.replace(MUT_FROM, MUT_TO)
    assert bad_src != src and bad_src.count(MUT_TO) == 1
    mod = types.ModuleType("semantics_bad")
    exec(compile(bad_src, "semantics_bad", "exec"), mod.__dict__)
    return mod


def mutation():
    """変異テスト：∃ の条件で、取り替えた割当て sg2 ではなく元の sg を使う版で、不一致が出ることを確かめる。"""
    build(bad_semantics())
    r = random.Random(3)
    n = 0
    # 二つの読みが必ず食い違う構造を選ぶ：∈ の解釈を {(a, a)} だけにすると、
    # x1 = a のとき ∃x0 (x0 ∈ x1) は真だが、x0 = b の割当てでは (x0 ∈ x1) は偽。
    M = random_struct(r, 2)
    a0 = M.dom[0]
    M.E = {(a0, a0)}
    n += run_case(FIXED[0], M, r)[0]
    import semantics as good
    build(good)
    print(f"変異テスト（∃ で割当てを取り替えない版）: {n} 件の不一致を検出" + ("" if n else "　※検出できていない"))
    return 0 if n else 1


def targeted(n_decoy=4):
    """狙い撃ちの構造だけを、正しい版と壊した版で実行する軽量モード（偽の証人を減らしてメモリを抑える）。"""
    import types, semantics, resource
    M_seed = random.Random(11)
    M = random_struct(M_seed, 2); M.E = {(M.dom[0], M.dom[0])}
    build(semantics)
    good = run_case(FIXED[0], M, random.Random(1), n_decoy=n_decoy)
    build(bad_semantics())
    bad = run_case(FIXED[0], M, random.Random(1), n_decoy=n_decoy)
    build(semantics)
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024
    print(f"狙い撃ち：正しい版の不一致 {good[0]}、壊した版の不一致 {bad[0]}（割当て {good[1]} 通り、最大メモリ約 {peak} MB）")
    return 0 if good[0] == 0 and bad[0] > 0 else 1

if __name__ == "__main__":
    import resource; resource.setrlimit(resource.RLIMIT_AS, (6_000_000_000, 6_000_000_000))
    if "--targeted" in sys.argv:
        LIGHT = True
        b = targeted()
        print("総合:", "すべて一致" if b == 0 else "不一致あり"); sys.exit(b)
    if "--quick" in sys.argv:
        LIGHT = True
    b = main(quick="--quick" in sys.argv)
    if "--mutation" in sys.argv:
        b += mutation()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)
