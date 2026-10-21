"""
num_formula.py の部品を、有限の推移的集合 V_4（16元）の上で総当たり評価して、
意図どおりの意味をもつか確認する。集合は frozenset で表す。
"""
from itertools import combinations
import num_formula as nf

def powerset(s):
    s = list(s)
    return {frozenset(c) for r in range(len(s) + 1) for c in combinations(s, r)}

def V(n):
    v = set()
    for _ in range(n):
        v = powerset(v)
    return v

def nat(n):
    s = frozenset()
    for _ in range(n):
        s = s | {s}
    return s

def pair(a, b):
    return frozenset({frozenset({a}), frozenset({a, b})})

def ev(f, env, D):
    if isinstance(f, nf.Atom):
        a, b = env[f.a], env[f.b]
        return (a in b) if f.op == '∈' else (a == b)
    if isinstance(f, nf.Not):
        return not ev(f.p, env, D)
    if isinstance(f, nf.And):
        return ev(f.p, env, D) and ev(f.q, env, D)
    if isinstance(f, nf.All):
        for d in D:
            env2 = dict(env); env2[f.v] = d
            if not ev(f.p, env2, D):
                return False
        return True
    raise TypeError

D = V(4)                      # 16 元、推移的
N = [nat(k) for k in range(4)]  # 0,1,2,3 は V_4 に含まれる
assert all(n in D for n in N)
x, y, z = 20, 21, 22          # テスト用の自由変数番号（部品の内部変数と重ならない）

errors = 0
def check(name, got, want):
    global errors
    if got != want:
        errors += 1
        print("NG", name, got, want)

for a in D:
    check("Empty", ev(nf.Empty(x), {x: a}, D), a == frozenset())
    trans = all(u in a for zz in a for u in zz)
    check("Trans", ev(nf.Trans(x), {x: a}, D), trans)
    succ = any(a == w | {w} for w in a)
    check("Succ", ev(nf.Succ(x), {x: a}, D), succ)
    check("Nat", ev(nf.Nat(x), {x: a}, D), a in N)

V3 = V(3)
for a in D:
    for b in V3:                       # P(b) が V_4 に収まる範囲
        check("PowerOf", ev(nf.PowerOf(x, y), {x: a, y: b}, D), a == frozenset(powerset(b)))

V2 = V(2)
for p in D:
    for a in V2:
        for b in V2:
            check("Pair", ev(nf.Pair(x, y, z), {x: p, y: a, z: b}, D), p == pair(a, b))

print("部品テスト:", "すべて一致" if errors == 0 else f"{errors} 件の不一致")
