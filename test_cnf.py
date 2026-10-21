"""
cnf.py の検証。

答え合わせ役：ε0 未満の順序数を、教科書どおりのカントール標準形（指数の非増加列）で表し、
順序数の足し算・ω の冪・比較を実装する。原文の CNF をそのまま計算し、得られた順序数を比べる。
判定式の方式（名前と計算表）とは独立である。

  層 1：dec（CNF の分解）。下位の算術は代用関係（test_arith.py で検証済み）。
  層 2：row_is（長さ 4 の自然数の列）。代用なしの本物の式。
  層 3：cnf_cmp。dec と row を代用関係に差し替え、正しい計算表と、1 行だけ値を変えた偽の表を宇宙に入れる。
"""
import sys, itertools, random
from fol import Ctx, Evaluator, transitive_closure, nat, pair, to_nat
import cnf as CN

# ---------- 答え合わせ役：カントール標準形 ----------
def o_cmp(A, B):
    for x, y in zip(A, B):
        c = o_cmp(x, y)
        if c: return c
    return (len(A) > len(B)) - (len(A) < len(B))

def o_add(A, B):
    if not B: return A
    lead = B[0]
    keep = tuple(t for t in A if o_cmp(t, lead) >= 0)   # A は非増加なので、lead 以上の項は先頭に並ぶ
    return keep + B

def o_wpow(X): return (X,)

def smallest_prime_factor(n):
    d = 2
    while n % d: d += 1
    return d

def dec_ref(i):
    n = i + 1; p = smallest_prime_factor(n); v = 0
    while n % p == 0: n //= p; v += 1
    return v - 1, n - 1          # a = v−1, b = j−1

_memo = {0: ()}
def CNF(i):
    if i not in _memo:
        a, b = dec_ref(i)
        _memo[i] = o_add(o_wpow(CNF(a)), CNF(b))
    return _memo[i]

def cmp_ref(i, k):
    return {-1: 0, 0: 1, 1: 2}[o_cmp(CNF(i), CNF(k))]

# ---------- 代用関係 ----------
def raw(f): f.raw = True; return f
def is_prime(n): return n >= 2 and all(n % d for d in range(2, n))
ORC = {
    "empty": raw(lambda a: a == frozenset()),
    "succ": raw(lambda b, c: c == (b | {b})),
    "numeral": raw(lambda k, v: v == nat(int(k))),
    "pair": raw(lambda p, a, b: p == pair(a, b)),
    "nat": lambda a: True,
    "prime": lambda p: is_prime(p),
    "mul": lambda a, b, c: c == a * b,
    "exp": lambda a, b, c: c == a ** b,
    "dec": lambda i, a, b: i > 0 and dec_ref(i) == (a, b),
}
def vseq(vals): return frozenset(pair(nat(i), nat(v)) for i, v in enumerate(vals))
def rowshape_oracle(k0, r):
    """r は長さ 4 の自然数の列で、第 0 成分が k0。"""
    if not isinstance(r, frozenset) or len(r) != 4: return False
    vals = {}
    for q in r:
        hit = [(i, v) for i in range(4) for v in range(64) if q == pair(nat(i), nat(v))]
        if len(hit) != 1: return False
        vals[hit[0][0]] = hit[0][1]
    return set(vals) == {0, 1, 2, 3} and vals[0] == int(k0)
ORC["rowshape"] = raw(rowshape_oracle)

def layer1(N=60):
    ctx = Ctx(oracles={"prime", "mul", "exp", "empty", "succ"}, start=1)
    vi, va, vb = ctx.fresh(3)
    f = CN.dec(ctx, vi, va, vb)
    D = transitive_closure({nat(k) for k in range(2 * N + 2)})
    udom = [nat(k) for k in range(2 * N + 2)]
    bad = 0
    for i in range(N):
        ev = Evaluator(D, ORC, udom)            # i ごとに作り直してキャッシュを解放する
        want = dec_ref(i) if i > 0 else None
        for a in range(8):
            for b in range(N):
                got = ev.ev(f, {vi: nat(i), va: nat(a), vb: nat(b)})
                if got != (want == (a, b)): bad += 1
    print(f"層1 dec（CNF の分解）: {'すべて一致' if bad == 0 else str(bad) + ' 件の不一致'}（i = 0〜{N - 1}）")
    return bad

def layer2():
    ctx = Ctx(start=1); vr, vx, vy, vz = ctx.fresh(4)
    fs = {k0: CN.row_is(ctx, vr, k0, vx, vy, vz) for k0 in (0, 1)}
    rows = [vseq(t) for t in [(0, 1, 2, 3), (1, 0, 0, 2), (0, 2, 1, 0), (1, 3, 3, 1)]]
    junk = [vseq((0, 1, 2)), vseq((0, 1, 2, 3, 4)), frozenset({pair(nat(0), nat(0)), pair(nat(0), nat(1)),
             pair(nat(1), nat(1)), pair(nat(2), nat(2)), pair(nat(3), nat(3))})]
    D = transitive_closure(set(rows) | set(junk) | {nat(k) for k in range(6)})
    ev = Evaluator(D)
    bad = 0
    for r in rows + junk:
        for k0 in (0, 1):
            for x, y, z in itertools.product(range(4), repeat=3):
                want = r == vseq((k0, x, y, z))
                if ev.ev(fs[k0], {vr: r, vx: nat(x), vy: nat(y), vz: nat(z)}) != want: bad += 1
    print(f"層2 row_is（長さ 4 の列、本物の式）: {'すべて一致' if bad == 0 else str(bad) + ' 件の不一致'}")
    return bad

def full_table(N):
    rows = []
    for i in range(1, N):
        a, b = dec_ref(i)
        # 正規化した先頭 (H, R)：表の値は答え合わせ役から（H, R の「名前」は判定式の規則で決まるので、規則どおりに計算）
    H = {}
    for i in range(1, N):
        a, b = dec_ref(i)
        if b == 0: H[i] = (a, 0)
        else:
            hb, rb = H[b]
            H[i] = (hb, rb) if cmp_ref(hb, a) == 2 else (a, b)
        rows.append((0, i, *H[i]))
    for i in range(N):
        for k in range(N):
            rows.append((1, i, k, cmp_ref(i, k)))
    absorbed = [i for i in range(1, N) if dec_ref(i)[1] != 0 and H[i] != dec_ref(i)]
    assert absorbed, "この範囲では吸収が一度も起きない（テストが吸収の規則を検査できない）"
    return rows, H

def layer3(N=20, n_decoy=25, seed=3, mutate_src=None):
    mod = CN
    if mutate_src is not None:
        import types
        mod = types.ModuleType("cnf_bad"); exec(compile(mutate_src, "cnf_bad", "exec"), mod.__dict__)
    rows, H = full_table(N)
    # 正規化した先頭が順序数として正しいことを答え合わせ役で確認（判定式の規則の正しさの確認）
    for i, (h, r) in H.items():
        assert o_add(o_wpow(CNF(h)), CNF(r)) == CNF(i), ("先頭の分解が正しくない", i)
        assert not CNF(r) or o_cmp(CNF(r)[0], CNF(h)) <= 0, ("残りの先頭が大きすぎる", i)
    T = frozenset(vseq(t) for t in rows)
    rnd = random.Random(seed)
    decoys = []
    for _ in range(n_decoy):
        t = rnd.choice(rows)
        if t[0] == 1:
            t2 = (1, t[1], t[2], (t[3] + rnd.choice([1, 2])) % 3)
        else:
            t2 = (0, t[1], (t[2] + 1) % N, t[3])
        decoys.append(frozenset((T - {vseq(t)}) | {vseq(t2)}))
    ctx = Ctx(oracles={"dec", "row", "empty", "succ", "numeral", "pair", "nat"}, start=1)
    vi, vk, vc = ctx.fresh(3)
    f = mod.cnf_cmp(ctx, vi, vk, vc)
    D = transitive_closure({T} | set(decoys) | {nat(k) for k in range(N + 3)})
    udom = [nat(k) for k in range(N + 3)] + [T] + decoys
    ev = Evaluator(D, ORC, udom)
    bad = 0
    for i in range(N):
        for k in range(N):
            for c in range(3):
                if ev.ev(f, {vi: nat(i), vk: nat(k), vc: nat(c)}) != (cmp_ref(i, k) == c): bad += 1
    if mutate_src is None:
        absorbed = [i for i in range(1, N) if dec_ref(i)[1] != 0 and H[i] != dec_ref(i)]
        print(f"  （吸収が起きる名前：{absorbed}）")
        print(f"層3 cnf_cmp（偽の表 {n_decoy} 個を含む）: {'すべて一致' if bad == 0 else str(bad) + ' 件の不一致'}（i, k = 0〜{N - 1}、判定 {N * N * 3} 回）")
    return bad

def mutation():
    """変異テスト：吸収の規則（CNF(H(b)) > CNF(a) なら ω^{CNF(a)} を捨てる）を外した版。"""
    src = open(CN.__file__, encoding="utf-8").read()
    a = "Or(conj(num(c, 2), Eq(h, hb), Eq(rr, rb)),"
    assert src.count(a) == 1
    bad_src = src.replace(a, "Or(conj(num(c, 9), Eq(h, hb), Eq(rr, rb)),")   # 吸収が起きないようにする
    n = layer3(mutate_src=bad_src)
    print(f"変異テスト（吸収の規則を外した版）: {n} 件の不一致を検出" + ("" if n else "　※検出できていない"))
    return 0 if n else 1

if __name__ == "__main__":
    import resource; resource.setrlimit(resource.RLIMIT_AS, (6_000_000_000, 6_000_000_000))
    b = layer1() + layer2() + layer3()
    if "--mutation" in sys.argv:
        b += mutation()
    print("総合:", "すべて一致" if b == 0 else f"{b} 件の不一致")
    sys.exit(1 if b else 0)
