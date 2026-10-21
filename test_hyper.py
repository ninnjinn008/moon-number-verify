"""
hyper_formula.Hyper(x, n, a, b) を小さい値で総当たり検証する。

宇宙 D には、正しい再帰表に加えて「値を 1 つずらした表」「途中の行が欠けた表」も入れる。
式が正しければ、偽の表はすべて Table の条件で弾かれ、x = H(n,a,b) のときだけ真になる。
"""
import num_formula as nf
import hyper_formula as hf
from eval_fast import Evaluator, transitive_closure

from fol import nat   # 同じ k に同じオブジェクトを返す版（深い集合の等号判定を速くする）

def pair(a, b):
    return frozenset({frozenset({a}), frozenset({a, b})})

def triple(n, b, v):
    return pair(pair(nat(n), nat(b)), nat(v))

def H(n, a, b):
    if n == 0: return b + 1
    if b == 0: return a if n == 1 else (0 if n == 2 else 1)
    return H(n - 1, a, H(n, a, b - 1))

def needed(n, a, b, acc):
    """H(n,a,b) の計算に必要な行 (n, b, 値) をすべて集める。"""
    acc.add((n, b, H(n, a, b)))
    if n > 0 and b > 0:
        w = H(n, a, b - 1)
        needed(n, a, b - 1, acc)
        needed(n - 1, a, w, acc)
    return acc

cases = [(0, 2, 3), (1, 2, 3), (2, 2, 3), (3, 2, 2), (4, 2, 1), (4, 2, 2), (2, 3, 0), (4, 2, 0), (1, 3, 0)]
bad = 0
for (n, a, b) in cases:
    rows = needed(n, a, b, set())
    good = frozenset(triple(*r) for r in rows)
    tables = [good]
    rows_l = sorted(rows)
    for i, (rn, rb, rv) in enumerate(rows_l):                       # 値を 1 ずらした表
        tables.append(frozenset(triple(*r) for j, r in enumerate(rows_l) if j != i) | {triple(rn, rb, rv + 1)})
    final = (n, b, H(n, a, b))
    for r in rows_l:                                               # 途中の行が欠けた表
        if r != final:
            tables.append(frozenset(triple(*q) for q in rows_l if q != r))
    maxv = max(max(r) for r in rows) + 3
    seeds = set(tables) | {nat(k) for k in range(maxv + 1)}
    D = transitive_closure(seeds)
    ev = Evaluator(D)
    f = hf.Hyper(nf.X, n, a, b)
    want = H(n, a, b)
    for xv in range(maxv + 1):
        got = ev.ev(f, {nf.X: nat(xv)})
        if got != (xv == want):
            bad += 1
            print("NG", (n, a, b), "x =", xv, got)
    print(f"H{(n, a, b)} = {want}：表 {len(tables)} 個、宇宙 {len(D)} 元で検証")
print("Hyper テスト:", "すべて一致" if bad == 0 else f"{bad} 件の不一致")
