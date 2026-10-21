"""
月絶天葬数：φ を組み立てるための基盤。

- 純粋な {∈,=} 一階式の構文木と、記号数の計数。
- 束縛変数は Ctx.fresh() で毎回新しい番号を割り当てる。部品どうしで変数が衝突しないので、
  変数捕獲は構造的に起こらない（番号が大きくなる分だけ記号数は増えるが、上限 10^100 に対しては無視できる）。
- テスト用の「代用関係」Oracle：下位の層を Python の関数に差し替えて、上位の層だけを検証できる。
  実際の φ には Oracle は現れない（render は Oracle を含む式を拒否する）。
- 有限の推移的集合上の評価器（有界量化の検出とメモ化つき）。
"""

# ---------------- 構文木 ----------------

class Atom:
    __slots__ = ("op", "a", "b")
    def __init__(s, op, a, b): s.op, s.a, s.b = op, a, b
class Not:
    __slots__ = ("p",)
    def __init__(s, p): s.p = p
class And:
    __slots__ = ("p", "q")
    def __init__(s, p, q): s.p, s.q = p, q
class All:
    __slots__ = ("v", "p")
    def __init__(s, v, p): s.v, s.p = v, p
class Oracle:
    """テスト専用：名前つきの関係を Python の関数で評価する。"""
    __slots__ = ("name", "args")
    def __init__(s, name, args): s.name, s.args = name, tuple(args)

def In(a, b): return Atom('∈', a, b)
def Eq(a, b): return Atom('=', a, b)
def Or(p, q):  return Not(And(Not(p), Not(q)))
def Imp(p, q): return Not(And(p, Not(q)))
def Iff(p, q): return And(Imp(p, q), Imp(q, p))
def Ex(v, p):  return Not(All(v, Not(p)))
def AllIn(v, a, p): return All(v, Imp(In(v, a), p))
def ExIn(v, a, p):  return Ex(v, And(In(v, a), p))
def conj(*ps):
    r = ps[0]
    for p in ps[1:]:
        r = And(r, p)
    return r
def disj(*ps):
    r = ps[0]
    for p in ps[1:]:
        r = Or(r, p)
    return r

def var(k): return "x" + "′" * k

def render(f):
    out = []
    def go(f):
        if isinstance(f, Atom): out.append("(" + var(f.a) + f.op + var(f.b) + ")")
        elif isinstance(f, Not): out.append("¬"); go(f.p)
        elif isinstance(f, And): out.append("("); go(f.p); out.append("∧"); go(f.q); out.append(")")
        elif isinstance(f, All): out.append("∀" + var(f.v)); go(f.p)
        elif isinstance(f, Oracle): raise ValueError("Oracle を含む式は描画できない（テスト専用）")
        else: raise TypeError
    go(f)
    return "".join(out)

def length(f, _memo=None):
    """記号数。共有された部分木はメモ化して数える（木として展開した長さ）。"""
    if _memo is None: _memo = {}
    k = id(f)
    if k in _memo: return _memo[k]
    if isinstance(f, Atom): r = 3 + (1 + f.a) + (1 + f.b)
    elif isinstance(f, Not): r = 1 + length(f.p, _memo)
    elif isinstance(f, And): r = 3 + length(f.p, _memo) + length(f.q, _memo)
    elif isinstance(f, All): r = 2 + f.v + length(f.p, _memo)
    elif isinstance(f, Oracle): raise ValueError("Oracle を含む式の記号数は数えない")
    else: raise TypeError
    _memo[k] = r
    return r

def free(f, _memo=None):
    if _memo is None: _memo = {}
    k = id(f)
    if k in _memo: return _memo[k]
    if isinstance(f, Atom): r = frozenset((f.a, f.b))
    elif isinstance(f, Not): r = free(f.p, _memo)
    elif isinstance(f, And): r = free(f.p, _memo) | free(f.q, _memo)
    elif isinstance(f, All): r = free(f.p, _memo) - {f.v}
    elif isinstance(f, Oracle): r = frozenset(f.args)
    else: raise TypeError
    _memo[k] = r
    return r

def has_oracle(f):
    stack = [f]
    while stack:
        g = stack.pop()
        if isinstance(g, Oracle): return True
        if isinstance(g, Not): stack.append(g.p)
        elif isinstance(g, And): stack += [g.p, g.q]
        elif isinstance(g, All): stack.append(g.p)
    return False

ALPHABET = set("x′¬∧∀∈=()")

# ---------------- 文脈（新変数と代用関係） ----------------

class Ctx:
    def __init__(self, oracles=(), start=1):
        self.n = start               # 0 番 (x) は定義される対象のために空けておく
        self.oracles = set(oracles)  # ここに名前がある関係は Oracle に差し替える
    def fresh(self, k=1):
        r = list(range(self.n, self.n + k))
        self.n += k
        return r[0] if k == 1 else r
    def use_oracle(self, name):
        return name in self.oracles

# ---------------- 有限集合上の評価器 ----------------

def to_nat(s):
    """フォン・ノイマン自然数なら int を、そうでなければ None を返す。"""
    n = len(s)
    for k in range(n):
        if nat(k) not in s:
            return None
    return n if nat(n) == s else None

class Evaluator:
    def __init__(self, D, oracle_funcs=None, udom=None):
        self.D = list(D)
        # udom を与えると、有界でない量化子はその範囲だけを動く（軽量モード用。既定は宇宙 D 全体）
        self.U = list(udom) if udom is not None else self.D
        self.Dset = set(D)
        self.memo = {}
        self.fvmemo = {}
        self.orc = oracle_funcs or {}

    def fv(self, f):
        k = id(f)
        if k not in self.fvmemo:
            self.fvmemo[k] = tuple(sorted(free(f)))
        return self.fvmemo[k]

    def ev(self, f, env):
        key = (id(f), tuple(env[v] for v in self.fv(f)))
        m = self.memo.get(key)
        if m is not None:
            return m
        r = self._ev(f, env)
        self.memo[key] = r
        return r

    def _ev(self, f, env):
        if isinstance(f, Atom):
            a, b = env[f.a], env[f.b]
            return (a in b) if f.op == '∈' else (a == b)
        if isinstance(f, Not):
            return not self.ev(f.p, env)
        if isinstance(f, And):
            return self.ev(f.p, env) and self.ev(f.q, env)
        if isinstance(f, Oracle):
            name, param = (f.name.split(":", 1) + [None])[:2]
            fn = self.orc[name]
            if getattr(fn, "raw", False):              # 集合をそのまま受け取る代用関係
                vals = [env[a] for a in f.args]
                return bool(fn(*vals) if param is None else fn(param, *vals))
            vals = [to_nat(env[a]) for a in f.args]
            if any(v is None for v in vals):
                return False
            return bool(fn(*vals) if param is None else fn(param, *vals))
        if isinstance(f, All):
            v, body = f.v, f.p
            if (isinstance(body, Not) and isinstance(body.p, And)
                    and isinstance(body.p.p, Atom) and body.p.p.op == '∈'
                    and body.p.p.a == v and body.p.p.b != v):
                psi = body.p.q
                for d in env[body.p.p.b]:
                    assert d in self.Dset, "宇宙 D が推移的でない"
                    env2 = dict(env); env2[v] = d
                    if self.ev(psi, env2):
                        return False
                return True
            for d in self.U:
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

# ---------------- 集合の構成（テスト用） ----------------

_NATS = [frozenset()]

def nat(k):
    """自然数 k。同じ k には常に同じオブジェクトを返す（深い集合どうしの等号判定が
    指数時間になるのを防ぐため。CPython の集合探索はまず同一性で比較する）。"""
    while len(_NATS) <= k:
        s = _NATS[-1]
        _NATS.append(s | {s})
    return _NATS[k]

def pair(a, b):
    return frozenset({frozenset({a}), frozenset({a, b})})
