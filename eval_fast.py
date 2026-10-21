"""
有限の宇宙 D 上で式を評価する評価器（総当たりの高速版）。

- 有界量化 ∀v (v∈a → φ) ＝ All(v, Not(And(In(v,a), Not φ))) を検出し、
  v を a の元だけに走らせる（D が推移的なら意味は変わらない）。
- 部分式の値を (部分式, 自由変数の値) でメモ化する。
"""
import num_formula as nf

class Evaluator:
    def __init__(self, D):
        self.D = list(D)
        self.Dset = set(D)
        self.memo = {}
        self.fv = {}

    def free(self, f):
        k = id(f)
        if k not in self.fv:
            self.fv[k] = tuple(sorted(nf.free(f)))
        return self.fv[k]

    def ev(self, f, env):
        key = (id(f), tuple(env[v] for v in self.free(f)))
        if key in self.memo:
            return self.memo[key]
        r = self._ev(f, env)
        self.memo[key] = r
        return r

    def _ev(self, f, env):
        if isinstance(f, nf.Atom):
            a, b = env[f.a], env[f.b]
            return (a in b) if f.op == '∈' else (a == b)
        if isinstance(f, nf.Not):
            return not self.ev(f.p, env)
        if isinstance(f, nf.And):
            return self.ev(f.p, env) and self.ev(f.q, env)
        if isinstance(f, nf.All):
            v, body = f.v, f.p
            # 有界量化の形 ∀v ¬(v∈a ∧ ψ)
            if (isinstance(body, nf.Not) and isinstance(body.p, nf.And)
                    and isinstance(body.p.p, nf.Atom) and body.p.p.op == '∈'
                    and body.p.p.a == v and body.p.p.b != v):
                rng = env[body.p.p.b]
                psi = body.p.q
                for d in rng:
                    assert d in self.Dset, "宇宙 D が推移的でない"
                    env2 = dict(env); env2[v] = d
                    if self.ev(psi, env2):
                        return False
                return True
            for d in self.D:
                env2 = dict(env); env2[v] = d
                if not self.ev(body, env2):
                    return False
            return True
        raise TypeError

def transitive_closure(sets):
    out, stack = set(), list(sets)
    while stack:
        s = stack.pop()
        if s in out:
            continue
        out.add(s)
        stack.extend(s)
    return out
