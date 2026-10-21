"""
metacode / formula_code の検証。

実際の MetaCode は天文学的に大きく（記号 1 つの番号でも 10^5 以上、列の番号はその指数）、
フォン・ノイマン自然数として作れない。そこで Encode を「代用の単射」に差し替えて、
metacode の組み立て（列の対応・添字・長さ・二段の Encode）を検証する。
本物の Encode は test_arith.py で小さい値について検証済みである。

  層 1：metacode（Encode を代用の単射に差し替え、その他は代用関係で検証済みの部品）
  層 2：formula_code / formula_code₋（metacode と Formula を代用に差し替え）
"""
import sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair, to_nat
import metacode as MC
import test_parse as T

# ---------- 代用の単射 E（有限列 → 小さい自然数） ----------
_ids = {}
def decode_seq(s):
    """自然数の有限列（順序対 (i, a) の集合、定義域が 0..h−1）なら tuple、そうでなければ None。"""
    if not isinstance(s, frozenset): return None
    d = {}
    for q in s:
        found = False
        for i in range(12):
            for a in range(60):
                if q == pair(nat(i), nat(a)):
                    if i in d: return None
                    d[i] = a; found = True
        if not found: return None
    if set(d) != set(range(len(d))): return None
    return tuple(d[k] for k in range(len(d)))
def E(seq):
    if seq not in _ids:
        _ids[seq] = len(_ids)
    return _ids[seq]
def seqset(seq): return frozenset(pair(nat(i), nat(a)) for i, a in enumerate(seq))

def raw(f): f.raw = True; return f
ORC = dict(T.ORC)
ORC["encode"] = raw(lambda s, c: (lambda d: d is not None and c == nat(E(d)))(decode_seq(s)))
ORC["formula"] = raw(lambda s: (lambda d: d is not None and T.is_formula(list(d)))(decode_str(s)))
ORC["formula_minus"] = raw(lambda s: (lambda d: d is not None and T.is_formula(list(d)) and T.TH not in d)(decode_str(s)))
def decode_str(s):
    """4 つ組の列なら tuple of tuple、そうでなければ None。"""
    if not isinstance(s, frozenset): return None
    d = {}
    for q in s:
        found = False
        for i in range(12):
            for t in T.ALL_SYMS + [T.JUNK]:
                if q == pair(nat(i), T.tset(t)):
                    if i in d: return None
                    d[i] = t; found = True
        if not found: return None
    if set(d) != set(range(len(d))): return None
    return tuple(d[k] for k in range(len(d)))

LOW = T.LOW | {"encode"}

def code_of(s):
    c = tuple(E(t) for t in s)
    return c, E(c)

def layer1():
    strings = [[T.BOT], [T.NEG, T.BOT], [T.LP, T.X[0], T.ELEM, T.X[1], T.RP], [T.LP, T.RP], [T.X[0], T.X[0]]]
    for s in strings:                      # 先に番号を割り当てておく
        code_of(s)
    ctx = Ctx(oracles=LOW, start=1); vn, vs = ctx.fresh(2)
    f = MC.metacode(ctx, vn, vs)
    bad = 0; checks = 0
    for s in strings:
        c, n = code_of(s)
        decoys = [c[:-1], c + (0,), tuple(x + 1 if k == 0 else x for k, x in enumerate(c))]
        decoy_sets = {seqset(d) for d in decoys if d} | {seqset(c) | {nat(0)}, seqset(c) | {pair(nat(len(c)), nat(0))}}
        for d in decoys:
            if d: E(d)
        top = len(_ids) + 2
        others = [T.sset(x) for x in strings] + [seqset(code_of(x)[0]) for x in strings]   # すべての列の証人を宇宙に入れる
        D = transitive_closure({seqset(c), T.sset(s)} | decoy_sets | set(others) | {T.tset(t) for t in s} | {nat(k) for k in range(top)})
        ev = Evaluator(D, ORC)
        for m in range(top):
            for x in strings:
                got = ev.ev(f, {vn: nat(m), vs: T.sset(x)})
                want = (code_of(x)[1] == m)
                checks += 1
                if got != want:
                    bad += 1; print("NG 層1", s, x, m, got, want)
    print(f"層1 metacode（代用の Encode）: {'すべて一致' if bad == 0 else str(bad) + ' 件の不一致'}（判定 {checks} 回）")
    return bad

def layer2():
    strings = [[T.BOT], [T.NEG, T.BOT], [T.LP, T.X[0], T.ELEM, T.X[1], T.RP], [T.LP, T.RP], [T.X[0], T.X[0]],
               [T.LP, T.TH, T.LP, T.X[0], T.RP, T.ELEM, T.X[1], T.RP]]
    for s in strings: code_of(s)
    ctx = Ctx(oracles=LOW | {"formula"}, start=1); vn = ctx.fresh()
    f = MC.formula_code(ctx, vn); fm = MC.formula_code(ctx, vn, True)
    top = len(_ids) + 2
    D = transitive_closure({T.sset(s) for s in strings} | {seqset(code_of(s)[0]) for s in strings} | {nat(k) for k in range(top)})
    ev = Evaluator(D, ORC)
    codes = {code_of(s)[1]: s for s in strings}
    bad = 0
    for m in range(top):
        s = codes.get(m)
        want = s is not None and T.is_formula(s)
        want_m = want and T.TH not in s
        if ev.ev(f, {vn: nat(m)}) != want: bad += 1; print("NG formula_code", m, s)
        if ev.ev(fm, {vn: nat(m)}) != want_m: bad += 1; print("NG formula_code₋", m, s)
    print(f"層2 formula_code / formula_code₋: {'すべて一致' if bad == 0 else str(bad) + ' 件の不一致'}（番号 0〜{top - 1}）")
    return bad


def mutation():
    """変異テスト：「各 i < h で c(i) = Encode(s(i))」の条件を外した版で、層 1 が不一致を出すことを確かめる。"""
    import types
    global MC
    src = open(MC.__file__, encoding="utf-8").read()
    a = """            AllIn(i, h, A.lookup(ctx, s, i, lambda t:            # 各 i < h で c(i) = Encode(s(i))
                         A.lookup(ctx, c, i, lambda v: A.encode(ctx, t, v))))))))"""
    assert src.count(a) == 1, "変異させる箇所が見つからない"
    bad = types.ModuleType("metacode_bad")
    exec(compile(src.replace(a, "            ))))  # 記号ごとの対応を外した"), "metacode_bad", "exec"), bad.__dict__)
    good, MC = MC, bad
    import io, contextlib
    with contextlib.redirect_stdout(io.StringIO()):
        n = layer1()
    MC = good
    print(f"変異テスト（記号ごとの対応を外した版）: {n} 件の不一致を検出" + ("" if n else "　※検出できていない"))
    return 0 if n else 1

if __name__ == "__main__":
    import resource; resource.setrlimit(resource.RLIMIT_AS, (5_000_000_000, 5_000_000_000))
    b = layer1() + layer2()
    if "--mutation" in sys.argv:
        b += mutation()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)
