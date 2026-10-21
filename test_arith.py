"""
算術の層を層ごとに総当たりで検証する。下位の層は Oracle（Python の関数）に差し替える。

  L1  hyper（a も変数）            … 本物の式、計算表を宇宙に入れて検証
  L2  add / mul / exp              … hyper を Oracle にして、数詞との組み合わせを検証
  L3  prime                        … mul を Oracle
  L4  nth_prime                    … prime を Oracle、正しい表・壊した表を宇宙に入れる
  L5  encode                       … nat, exp, mul, nth_prime を Oracle、列と積の表を宇宙に入れる
"""
import sys
from fol import Ctx, Evaluator, transitive_closure, nat, pair, free
import arith as A

def H(n, a, b):
    if n == 0: return b + 1
    if b == 0: return a if n == 1 else (0 if n == 2 else 1)
    return H(n - 1, a, H(n, a, b - 1))

def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, p))

PRIMES = [p for p in range(2, 200) if is_prime(p)]

def encode_int(seq):
    v = 2 ** len(seq)
    for i, a in enumerate(seq):
        v *= PRIMES[i + 1] ** a
    return v - 1

ORC = {
    "hyper": lambda n, a, b, c: c == H(n, a, b),
    "add": lambda a, b, c: c == a + b,
    "mul": lambda a, b, c: c == a * b,
    "exp": lambda a, b, c: c == a ** b,
    "prime": is_prime,
    "nth_prime": lambda i, p: i < len(PRIMES) and p == PRIMES[i],
    "nat": lambda a: True,
}

fails = 0
def report(name, bad, extra=""):
    global fails
    fails += bad
    print(f"{name}: {'すべて一致' if bad == 0 else str(bad) + ' 件の不一致'} {extra}")

# ---------- L1 hyper（a は変数） ----------
def triple(n, b, v): return pair(pair(nat(n), nat(b)), nat(v))
def needed(n, a, b, acc):
    acc.add((n, b, H(n, a, b)))
    if n > 0 and b > 0:
        needed(n, a, b - 1, acc); needed(n - 1, a, H(n, a, b - 1), acc)
    return acc

bad = 0
for (n, a, b) in [(1, 2, 2), (2, 2, 2), (3, 2, 2), (2, 3, 0), (3, 3, 0), (1, 3, 0)]:
    rows = sorted(needed(n, a, b, set()))
    tables = [frozenset(triple(*r) for r in rows)]
    for i, (rn, rb, rv) in enumerate(rows):
        tables.append(frozenset(triple(*r) for j, r in enumerate(rows) if j != i) | {triple(rn, rb, rv + 1)})
    top = max(max(r) for r in rows) + 2
    D = transitive_closure(set(tables) | {nat(k) for k in range(top + 1)})
    ctx = Ctx()
    vn, va, vb, vc = ctx.fresh(4)
    f = A.hyper(ctx, vn, va, vb, vc)
    ev = Evaluator(D)
    for c in range(top + 1):
        got = ev.ev(f, {vn: nat(n), va: nat(a), vb: nat(b), vc: nat(c)})
        bad += got != (c == H(n, a, b))
report("L1 hyper", bad)

# ---------- L2 add / mul / exp ----------
bad = 0
D = transitive_closure({nat(k) for k in range(30)})
ctx = Ctx(oracles={"hyper"})
va, vb, vc = ctx.fresh(3)
fs = {"add": A.add(ctx, va, vb, vc), "mul": A.mul(ctx, va, vb, vc), "exp": A.exp(ctx, va, vb, vc)}
ref = {"add": lambda a, b: a + b, "mul": lambda a, b: a * b, "exp": lambda a, b: a ** b}
ev = Evaluator(D, ORC)
for name, f in fs.items():
    for a in range(5):
        for b in range(4):
            for c in range(30):
                got = ev.ev(f, {va: nat(a), vb: nat(b), vc: nat(c)})
                bad += got != (c == ref[name](a, b))
report("L2 add/mul/exp", bad)

# ---------- L3 prime ----------
bad = 0
D = transitive_closure({nat(k) for k in range(40)} | {frozenset({nat(3)}), frozenset({nat(0), nat(2)})})
ctx = Ctx(oracles={"mul"})
vp = ctx.fresh()
f = A.prime(ctx, vp)
ev = Evaluator(D, ORC)
for d in D:
    k = None
    from fol import to_nat
    k = to_nat(d)
    want = (k is not None and is_prime(k))
    bad += ev.ev(f, {vp: d}) != want
report("L3 prime", bad, f"(宇宙 {len(D)} 元、非自然数を含む)")

# ---------- L4 nth_prime ----------
bad = 0
def ptab(rows): return frozenset(pair(nat(i), nat(p)) for i, p in rows)
good_rows = [(i, PRIMES[i]) for i in range(5)]
tables = [ptab(good_rows),
          ptab(good_rows[:3] + [(3, 9)]),                 # 合成数を混ぜる
          ptab(good_rows[:2] + [(2, 7)]),                 # 素数を飛ばす
          ptab([(0, 3)]),                                 # 初項が違う
          ptab([(1, 3)])]                                 # 前の行がない
D = transitive_closure(set(tables) | {nat(k) for k in range(15)})
ctx = Ctx(oracles={"prime"})
vi, vp = ctx.fresh(2)
f = A.nth_prime(ctx, vi, vp)
ev = Evaluator(D, ORC)
for i in range(6):
    for p in range(15):
        got = ev.ev(f, {vi: nat(i), vp: nat(p)})
        want = (i < 5 and p == PRIMES[i])   # 宇宙に入れた正しい表は i < 5 まで
        bad += got != want
report("L4 nth_prime", bad)

# ---------- L5 encode ----------
bad = 0
seqs = [(), (0,), (1,), (0, 0), (1, 0), (0, 1)]
def seqset(sq): return frozenset(pair(nat(i), nat(a)) for i, a in enumerate(sq))
def prods(sq):
    rows, P = [(0, 1)], 1
    for k, a in enumerate(sq):
        P *= PRIMES[k + 1] ** a
        rows.append((k + 1, P))
    return rows
tables = []
for sq in seqs:
    r = prods(sq)
    tables.append(frozenset(pair(nat(k), nat(P)) for k, P in r))
    if len(r) > 1:                                             # 最後の積をずらした表
        r2 = r[:-1] + [(r[-1][0], r[-1][1] + 1)]
        tables.append(frozenset(pair(nat(k), nat(P)) for k, P in r2))
bogus = [frozenset({pair(nat(0), nat(1)), pair(nat(0), nat(0))}),   # 関数でない
         frozenset({pair(nat(1), nat(1))}),                         # 定義域が自然数でない
         frozenset({pair(nat(0), nat(0)), nat(0)}),                 # 回帰テスト：順序対でない元 ∅ を含む
         frozenset({pair(nat(0), nat(0)), nat(1)})]                 # 回帰テスト：順序対でない元 {∅} を含む
top = max(encode_int(sq) for sq in seqs) + 2
D = transitive_closure({seqset(sq) for sq in seqs} | set(bogus) | set(tables) | {nat(k) for k in range(top + 1)})
ctx = Ctx(oracles={"nat", "exp", "mul", "nth_prime"})
vs, vc = ctx.fresh(2)
f = A.encode(ctx, vs, vc)
ev = Evaluator(D, ORC)
for sq in seqs:
    for c in range(top + 1):
        got = ev.ev(f, {vs: seqset(sq), vc: nat(c)})
        bad += got != (c == encode_int(sq))
for b in bogus:
    for c in range(top + 1):
        bad += ev.ev(f, {vs: b, vc: nat(c)})
report("L5 encode", bad, f"(列 {len(seqs)} 個、宇宙 {len(D)} 元、値は {[encode_int(s) for s in seqs]})")

print()
print("総合:", "すべて一致" if fails == 0 else f"{fails} 件の不一致")
sys.exit(1 if fails else 0)
