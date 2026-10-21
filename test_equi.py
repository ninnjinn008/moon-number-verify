"""
Equi(x, b) を総当たりで検証する。
x ∈ {0,1,2,3}、b ∈ {∅, {∅}, {∅,{∅}}, {{∅}}} について、
「x と b の間に全単射がある」⇔「x = |b|」を確かめる。
宇宙 D は、x × b の順序対の集合（全部分集合）を含む推移的集合とする。
"""
from itertools import combinations
import num_formula as nf
from eval_fast import Evaluator, transitive_closure

def nat(n):
    s = frozenset()
    for _ in range(n):
        s = s | {s}
    return s

def pair(a, b):
    return frozenset({frozenset({a}), frozenset({a, b})})

def subsets(xs):
    xs = list(xs)
    return [frozenset(c) for r in range(len(xs) + 1) for c in combinations(xs, r)]

e = frozenset()
B = [e, frozenset({e}), frozenset({e, frozenset({e})}), frozenset({frozenset({e})})]
X = [nat(k) for k in range(4)]

seeds = set(X) | set(B)
for x in X:
    for b in B:
        prs = [pair(a, c) for a in x for c in b]
        seeds |= set(subsets(prs))
D = transitive_closure(seeds)
print("宇宙 D の大きさ:", len(D))

ev = Evaluator(D)
x_, b_ = 20, 21
f = nf.Equi(x_, b_)
bad = 0
for x in X:
    for b in B:
        got = ev.ev(f, {x_: x, b_: b})
        want = (len(x) == len(b))
        if got != want:
            bad += 1
            print("NG", len(x), b, got, want)
print("Equi テスト:", "すべて一致" if bad == 0 else f"{bad} 件の不一致")
