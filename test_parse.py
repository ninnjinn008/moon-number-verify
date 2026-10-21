"""
parse.py の Formula / Formula₋ / 証明書の判定を総当たりで検証する。

1. 文法から論理式を生成し（正例）、記号の削除・置換・入れ替えで負例を作る。
   Python の参照実装（区間 DP）で正誤を判定し、生成器とも照合する。
2. 各列 s について、参照実装が導く「正当な項目の全体」M* を作る。
   - certificate_ok(s, M*) は真、
   - M* に正当でない項目 x を一つ足した M* ∪ {x} は、すべて偽、
   であることを確かめる（規則の書き間違いを一つずつ検出するための検査）。
3. Formula(s) と Formula₋(s) が参照実装と一致することを確かめる。
   宇宙には M* と M* ∪ {((0,h),1)} を入れておく（負例で偽の証明書が通らないか試す）。
"""
import random, sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair
import parse as P

# ---------- 記号 ----------
def S(*a): return tuple(a)
BOT, IMP, NEG, EXI, LP, RP = (S(k, 0, 0, 0) for k in range(6))
X = [S(7, 1, i, 0) for i in range(2)]
C0 = S(6, 0, 0, 0)
U_, TH = S(8, 2, 0, 1), S(8, 3, 0, 1)
F0, F2 = S(8, 4, 0, 0), S(8, 4, 0, 2)          # 引数 0 個・2 個の関数記号
ELEM = S(9, 5, 0, 2)
R1, R0 = S(9, 6, 0, 1), S(9, 6, 1, 0)          # 引数 1 個・0 個の関係記号
JUNK = S(9, 9, 0, 0)                            # どの規則にも当てはまらない 4 つ組
FAKE_UT = [S(8, 2, 0, 0), S(8, 2, 5, 1), S(8, 3, 9, 7), S(8, 3, 0, 0), S(8, 2, 0, 2)]   # 存在しない U・Θ の符号
# 回帰テスト：期待値を参照実装から取らず、手で固定する（参照実装と判定式が同じ誤りを共有しても検出できるように）
FIXED = [
    ([LP, S(8, 2, 0, 0), LP, RP, ELEM, X[0], RP], False),        # ( U_fake ( ) ∈ x_0 )
    ([LP, S(8, 3, 0, 0), LP, RP, ELEM, X[0], RP], False),        # ( Θ_fake ( ) ∈ x_0 )
    ([LP, S(8, 2, 5, 1), LP, X[0], RP, ELEM, X[1], RP], False),  # ( U_fake ( x_0 ) ∈ x_1 )
    ([LP, U_, LP, X[0], RP, ELEM, X[1], RP], True),              # ( U ( x_0 ) ∈ x_1 )
    ([LP, F0, LP, RP, ELEM, X[0], RP], True),                    # ( f_{0,0} ( ) ∈ x_0 )
    ([NEG, LP, F2, LP, X[0], C0, RP, ELEM, X[1], RP], True),     # ¬ ( f_{2,0} ( x_0 c_0 ) ∈ x_1 )
    ([LP, F2, LP, X[0], RP, ELEM, X[1], RP], False),             # 引数の個数が足りない
]
ALL_SYMS = [BOT, IMP, NEG, EXI, LP, RP, X[0], X[1], C0, U_, TH, F0, F2, ELEM, R1, R0]

def arity(t): return t[3]
def kind(t):
    if t in (BOT, IMP, NEG, EXI, LP, RP): return "punct"
    if t[0] == 7 and t[1] == 1 and t[3] == 0: return "var"
    if t[0] == 6 and t[1] == 0 and t[3] == 0: return "const"
    if t in (U_, TH) or (t[0] == 8 and t[1] == 4): return "func"   # U・Θ は符号が固定、f_{a,i} は (8,4,i,a)
    if t == ELEM: return "elem"
    if t[0] == 9 and t[1] == 6: return "rel"
    return "junk"

# ---------- 参照実装：区間 DP ----------
def derive(s, maxlist=3):
    """正当な項目 (i, j, k) の全体。k: 0=項, 1=論理式, n+2=項 n 個の列。"""
    h = len(s)
    D = set()
    for i in range(h + 3):
        D.add((i, i, 2))                               # 空の列（区間が空なら項 0 個の列。位置は列の外でもよい）
    for length in range(0, h + 1):
        for i in range(0, h - length + 1):
            j = i + length
            changed = True
            while changed:                              # 同じ区間で列の個数を増やす
                changed = False
                # 列
                for n in range(1, maxlist + 1):
                    if (i, j, n + 2) in D: continue
                    for m in range(i + 1, j + 1):
                        if (i, m, 0) in D and (m, j, n + 1) in D:
                            D.add((i, j, n + 2)); changed = True; break
            if length == 0:
                continue
            # 項
            if length == 1 and kind(s[i]) in ("var", "const"):
                D.add((i, j, 0))
            if length >= 3 and kind(s[i]) == "func" and s[i + 1] == LP and s[j - 1] == RP \
                    and (i + 2, j - 1, arity(s[i]) + 2) in D:
                D.add((i, j, 0))
            # 論理式
            if length == 1 and s[i] == BOT:
                D.add((i, j, 1))
            if length >= 3 and kind(s[i]) == "rel" and s[i + 1] == LP and s[j - 1] == RP \
                    and (i + 2, j - 1, arity(s[i]) + 2) in D:
                D.add((i, j, 1))
            if s[i] == LP and s[j - 1] == RP:
                for m in range(i + 1, j - 1):
                    if s[m] == ELEM and (i + 1, m, 0) in D and (m + 1, j - 1, 0) in D:
                        D.add((i, j, 1))
                    if s[m] == IMP and (i + 1, m, 1) in D and (m + 1, j - 1, 1) in D:
                        D.add((i, j, 1))
            if s[i] == NEG and (i + 1, j, 1) in D:
                D.add((i, j, 1))
            if length >= 4 and s[i] == EXI and kind(s[i + 1]) == "var" and s[i + 2] == LP \
                    and s[j - 1] == RP and (i + 3, j - 1, 1) in D:
                D.add((i, j, 1))
            # 新しい項目で列が伸びる可能性があるので、もう一度列を見る
            for n in range(1, maxlist + 1):
                for m in range(i + 1, j + 1):
                    if (i, m, 0) in D and (m, j, n + 1) in D:
                        D.add((i, j, n + 2))
    return D

def is_formula(s): return (0, len(s), 1) in derive(s)

# ---------- 生成器 ----------
def gen_term(r, d):
    c = r.random()
    if d <= 0 or c < 0.5: return [r.choice([X[0], X[1], C0])]
    f = r.choice([U_, TH, F0, F2])
    args = sum((gen_term(r, d - 1) for _ in range(arity(f))), [])
    return [f, LP] + args + [RP]

def gen_formula(r, d):
    c = r.random()
    if d <= 0 or c < 0.25:
        return r.choice([[BOT], [LP] + gen_term(r, 1) + [ELEM] + gen_term(r, 1) + [RP],
                         [R1, LP] + gen_term(r, 1) + [RP], [R0, LP, RP]])
    if c < 0.5: return [NEG] + gen_formula(r, d - 1)
    if c < 0.75: return [LP] + gen_formula(r, d - 1) + [IMP] + gen_formula(r, d - 1) + [RP]
    return [EXI, r.choice(X), LP] + gen_formula(r, d - 1) + [RP]

def mutate(r, s):
    s = list(s); op = r.randrange(4)
    if op == 0 and len(s) > 1: del s[r.randrange(len(s))]
    elif op == 1: s[r.randrange(len(s))] = r.choice(ALL_SYMS + [JUNK])
    elif op == 2 and len(s) > 1:
        a, b = r.sample(range(len(s)), 2); s[a], s[b] = s[b], s[a]
    else: s.insert(r.randrange(len(s) + 1), r.choice(ALL_SYMS))
    return s

# ---------- 集合への変換 ----------
def tset(t): return frozenset(pair(nat(k), nat(a)) for k, a in enumerate(t))
def sset(s): return frozenset(pair(nat(i), tset(t)) for i, t in enumerate(s))
def cset(items): return frozenset(pair(pair(nat(i), nat(j)), nat(k)) for i, j, k in items)

# ---------- 代用関係（下位の層。各部品は別に検証済み） ----------
from fol import to_nat
def raw(f): f.raw = True; return f
def decode_tuple(t):
    if not isinstance(t, frozenset): return None
    d = {}
    for q in t:
        ok = False
        for i in range(4):
            for a in range(12):
                if q == pair(nat(i), nat(a)):
                    if i in d: return None
                    d[i] = a; ok = True
        if not ok: return None
    if set(d) != {0, 1, 2, 3}: return None
    return tuple(d[k] for k in range(4))
def symk(pred): return raw(lambda t: (lambda d: d is not None and pred(d))(decode_tuple(t)))
ORC = {
    "pair": raw(lambda p, a, b: p == pair(a, b)),
    "triple": raw(lambda p, n, b, v: p == pair(pair(n, b), v)),
    "empty": raw(lambda a: a == frozenset()),
    "succ": raw(lambda b, c: c == (b | {b})),
    "numeral": raw(lambda k, v: v == nat(int(k))),
    "nat": lambda a: True,
    "tuple4": raw(lambda t: decode_tuple(t) is not None),
    "punct": raw(lambda k, t: decode_tuple(t) == (int(k), 0, 0, 0)),
    "var": symk(lambda d: kind(d) == "var"),
    "const": symk(lambda d: kind(d) == "const"),
    "func": symk(lambda d: kind(d) == "func"),
    "rel": symk(lambda d: kind(d) == "rel"),
    "elem": symk(lambda d: d == ELEM),
    "theta": symk(lambda d: d == TH),
}
LOW = {"pair", "triple", "empty", "succ", "numeral", "nat", "tuple4", "sym"}

def layer_a():
    """記号の判定（is_var など）と tuple4 を、代用なしの本物の式で検証する。"""
    import arith as A
    syms = ALL_SYMS + [JUNK, S(7, 1, 0, 1), S(8, 5, 0, 1), S(9, 5, 0, 1), S(4, 0, 0, 1)] + FAKE_UT
    others = [frozenset(), nat(3), frozenset({pair(nat(0), nat(4))}),
              frozenset({pair(nat(k), nat(0)) for k in range(5)}),
              frozenset({pair(nat(0), nat(1)), pair(nat(0), nat(2)), pair(nat(1), nat(0)), pair(nat(2), nat(0)), pair(nat(3), nat(0))})]
    objs = [tset(t) for t in syms] + others
    D = transitive_closure(set(objs) | {nat(k) for k in range(12)})
    ctx = Ctx(start=1); vt = ctx.fresh()
    preds = {
        "var": (P.is_var(ctx, vt), lambda d: kind(d) == "var"),
        "const": (P.is_const(ctx, vt), lambda d: kind(d) == "const"),
        "func": (P.is_func(ctx, vt), lambda d: kind(d) == "func"),
        "rel": (P.is_rel(ctx, vt), lambda d: kind(d) == "rel"),
        "elem": (P.is_elem(ctx, vt), lambda d: d == ELEM),
        "theta": (P.is_theta(ctx, vt), lambda d: d == TH),
        "tuple4": (P.tuple4(ctx, vt), lambda d: True),
    }
    for k in range(6):
        preds[f"punct{k}"] = (P.is_punct(ctx, vt, k), (lambda kk: lambda d: d == (kk, 0, 0, 0))(k))
    ev = Evaluator(D)
    bad = 0
    for o in objs:
        d = decode_tuple(o)
        for name, (f, ref) in preds.items():
            # 記号の判定は、tuple4 で 4 つ組と確認された値にだけ適用される（Formula の中では
            # 列の値はまず tuple4 で検査される）。よって 4 つ組でない対象では tuple4 だけを検査する。
            if name != "tuple4" and d is None:
                continue
            want = d is not None and ref(d)
            if ev.ev(f, {vt: o}) != want:
                bad += 1; print("NG 層A", name, d, o if d is None else "")
    print(f"層A（記号の判定・tuple4、本物の式）: {'すべて一致' if bad == 0 else str(bad) + ' 件の不一致'}（対象 {len(objs)} 個 × 判定 {len(preds)} 種）")
    return bad

def main(n_pos=14, n_neg=14, maxlen=9, seed=1):
    r = random.Random(seed)
    pos, neg = [], []
    while len(pos) < n_pos:
        s = gen_formula(r, 2)
        if len(s) <= maxlen and s not in pos:
            assert is_formula(s), s            # 生成器と参照実装の照合
            pos.append(s)
    while len(neg) < n_neg:
        s = mutate(r, r.choice(pos))
        if 1 <= len(s) <= maxlen and not is_formula(s) and s not in neg:
            neg.append(s)
    neg.append([JUNK]); neg.append([LP, RP]); neg.append([NEG])
    for fs, expected in FIXED:                         # 手で固定した期待値と参照実装を照合
        assert is_formula(fs) == expected, ("参照実装が固定の期待値と食い違う", fs, expected)
        (pos if expected else neg).append(fs)
    pos.append([LP, TH, LP, X[0], RP, ELEM, X[1], RP])  # Θ を含む正例（Formula₋ では偽）

    ctx = Ctx(oracles=LOW, start=1)
    vs, vC, vK0, vK1 = ctx.fresh(4)
    cert = P.certificate_ok(ctx, vs, vC, vK0, vK1)
    fm = P.formula(ctx, vs, False)
    fm_minus = P.formula(ctx, vs, True)

    bad_cert = bad_form = n_liars = 0
    for idx, s in enumerate(pos + neg):
        h = len(s)
        Mstar = derive(s)
        Mstar_in = {x for x in Mstar if x[0] <= h + 1 and x[1] <= h + 1 and x[2] <= 4}
        liars = []
        for i in range(h + 2):
            for j in range(h + 2):
                for k in range(5):
                    if (i, j, k) not in Mstar:
                        liars.append(Mstar_in | {(i, j, k)})
        top_liar = Mstar_in | {(0, h, 1)}
        nats = {nat(k) for k in range(h + 3)}
        env0 = {vs: sset(s), vK0: nat(0), vK1: nat(1)}
        def cert_holds(items):
            # 証明書ごとに小さな宇宙と新しい評価器を使う（キャッシュの肥大を防ぐ）
            D = transitive_closure({sset(s), cset(items)} | nats)
            e = dict(env0); e[vC] = cset(items)
            return Evaluator(D, ORC).ev(cert, e)
        if not cert_holds(Mstar_in):
            bad_cert += 1; print("NG: M* が証明書として拒否された", s)
        for L in liars:
            n_liars += 1
            if cert_holds(L):
                bad_cert += 1; print("NG: 偽の項目が通った", s, sorted(L - Mstar_in))
        # Formula / Formula₋（宇宙には正しい証明書と、頂点だけ偽った証明書を入れる）
        D = transitive_closure({sset(s), cset(Mstar_in), cset(top_liar)} | nats)
        ev = Evaluator(D, ORC)
        want = is_formula(s)
        want_minus = want and TH not in s
        if ev.ev(fm, {vs: sset(s)}) != want:
            bad_form += 1; print("NG Formula", s, want)
        if ev.ev(fm_minus, {vs: sset(s)}) != want_minus:
            bad_form += 1; print("NG Formula₋", s, want_minus)
        print(f"  [{idx + 1}/{len(pos) + len(neg)}] 長さ {h}、{'正例' if want else '負例'}、偽の証明書 {len(liars)} 個", flush=True)
    print(f"正例 {len(pos)}、負例 {len(neg)}、偽の証明書 {n_liars} 個を検査")
    print("証明書の検査:", "すべて一致" if bad_cert == 0 else f"{bad_cert} 件の不一致")
    print("Formula / Formula₋:", "すべて一致" if bad_form == 0 else f"{bad_form} 件の不一致")
    return bad_cert + bad_form


def mutation():
    """変異テスト：¬ の記号の検査を外した版で、偽の証明書が通ることを確かめる。"""
    import types
    src = open(P.__file__, encoding="utf-8").read()
    a = "neg = And(at(i, lambda t: is_punct(ctx, t, NEG)), nxt(i, lambda i1: in_cert(ctx, C, i1, j, isF)))"
    assert src.count(a) == 1, "変異させる箇所が見つからない"
    bad = types.ModuleType("parse_bad")
    exec(compile(src.replace(a, "neg = nxt(i, lambda i1: in_cert(ctx, C, i1, j, isF))"), "parse_bad", "exec"), bad.__dict__)
    s = [LP, BOT]; h = 2
    M = {x for x in derive(s) if x[0] <= h + 1 and x[1] <= h + 1 and x[2] <= 4}
    nats = {nat(k) for k in range(h + 3)}
    result = {}
    for name, mod in (("正しい版", P), ("壊した版", bad)):
        ctx = Ctx(oracles=LOW, start=1); vs, vC, vK0, vK1 = ctx.fresh(4)
        cert = mod.certificate_ok(ctx, vs, vC, vK0, vK1)
        n = 0
        for i in range(h + 2):
            for j in range(h + 2):
                for k in range(5):
                    if (i, j, k) in M: continue
                    L = M | {(i, j, k)}
                    D = transitive_closure({sset(s), cset(L)} | nats)
                    if Evaluator(D, ORC).ev(cert, {vs: sset(s), vC: cset(L), vK0: nat(0), vK1: nat(1)}):
                        n += 1
        result[name] = n
    print(f"変異テスト（¬ の検査を外した版）: 正しい版で {result['正しい版']} 件、壊した版で {result['壊した版']} 件の偽の証明書が通った")
    return 0 if result["正しい版"] == 0 and result["壊した版"] > 0 else 1

if __name__ == "__main__":
    a = layer_a()
    # --quick：時間制限のある環境向け（固定の回帰テスト 7 例は常に含む）
    b = main(n_pos=3, n_neg=3, maxlen=7) if "--quick" in sys.argv else main()
    if "--mutation" in sys.argv:
        b += mutation()
    print("総合:", "すべて一致" if a + b == 0 else f"{a + b} 件の不一致")
    sys.exit(1 if a + b else 0)
