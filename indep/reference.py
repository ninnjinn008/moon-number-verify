"""Independent reference implementation of SPEC.md (syntax, satisfaction,
substitution, IsDefinition / Definable, defines, Theta, henkin_ok).

Standard library only.  Brute force over finite structures.
"""
from itertools import product
from types import SimpleNamespace

# ---------------------------------------------------------------- symbols
BOT = (0, 0, 0, 0)
IMP = (1, 0, 0, 0)
NOT = (2, 0, 0, 0)
EX = (3, 0, 0, 0)
LP = (4, 0, 0, 0)
RP = (5, 0, 0, 0)
U = (8, 2, 0, 1)
THETA = (8, 3, 0, 1)
IN = (9, 5, 0, 2)


def c(i):
    return (6, 0, i, 0)


def x(i):
    return (7, 1, i, 0)


def f(a, i):
    return (8, 4, i, a)


def r(a, i):
    return (9, 6, i, a)


def _is_nat(n):
    return isinstance(n, int) and not isinstance(n, bool) and n >= 0


def _norm(s):
    """Return s as a 4-tuple of naturals, or None."""
    try:
        t = tuple(s)
    except TypeError:
        return None
    if len(t) != 4 or not all(_is_nat(v) for v in t):
        return None
    return t


def is_var(s):
    return s[0] == 7 and s[1] == 1 and s[3] == 0


def is_const(s):
    return s[0] == 6 and s[1] == 0 and s[3] == 0


def is_func(s):
    return s == U or s == THETA or (s[0] == 8 and s[1] == 4)


def is_rel(s):
    return s == IN or (s[0] == 9 and s[1] == 6)


def is_symbol(s):
    return (s in (BOT, IMP, NOT, EX, LP, RP) or is_var(s) or is_const(s)
            or is_func(s) or is_rel(s))


# ---------------------------------------------------------------- parser
# Terms:    ('var', i) | ('const', i) | ('fn', F, [terms])
# Formulas: ('bot',) | ('in', t1, t2) | ('rel', R, [terms])
#           | ('imp', A, B) | ('not', A) | ('ex', i, A)

class _ParseError(Exception):
    pass


def _parse_term(seq, p):
    if p >= len(seq):
        raise _ParseError
    s = seq[p]
    if is_var(s):
        return ('var', s[2]), p + 1
    if is_const(s):
        return ('const', s[2]), p + 1
    if is_func(s):
        if p + 1 >= len(seq) or seq[p + 1] != LP:
            raise _ParseError
        p += 2
        args = []
        for _ in range(s[3]):
            t, p = _parse_term(seq, p)
            args.append(t)
        if p >= len(seq) or seq[p] != RP:
            raise _ParseError
        return ('fn', s, args), p + 1
    raise _ParseError


def _parse_formula(seq, p):
    if p >= len(seq):
        raise _ParseError
    s = seq[p]
    if s == BOT:
        return ('bot',), p + 1
    if s == NOT:
        a, p = _parse_formula(seq, p + 1)
        return ('not', a), p
    if s == EX:
        if p + 1 >= len(seq) or not is_var(seq[p + 1]):
            raise _ParseError
        i = seq[p + 1][2]
        if p + 2 >= len(seq) or seq[p + 2] != LP:
            raise _ParseError
        a, q = _parse_formula(seq, p + 3)
        if q >= len(seq) or seq[q] != RP:
            raise _ParseError
        return ('ex', i, a), q + 1
    if is_rel(s) and s != IN:
        if p + 1 >= len(seq) or seq[p + 1] != LP:
            raise _ParseError
        p += 2
        args = []
        for _ in range(s[3]):
            t, p = _parse_term(seq, p)
            args.append(t)
        if p >= len(seq) or seq[p] != RP:
            raise _ParseError
        return ('rel', s, args), p + 1
    if s == LP:
        if p + 1 >= len(seq):
            raise _ParseError
        nxt = seq[p + 1]
        if is_var(nxt) or is_const(nxt) or is_func(nxt):
            # ( t1 ∈ t2 )
            t1, q = _parse_term(seq, p + 1)
            if q >= len(seq) or seq[q] != IN:
                raise _ParseError
            t2, q = _parse_term(seq, q + 1)
            if q >= len(seq) or seq[q] != RP:
                raise _ParseError
            return ('in', t1, t2), q + 1
        # ( φ → ψ )
        a, q = _parse_formula(seq, p + 1)
        if q >= len(seq) or seq[q] != IMP:
            raise _ParseError
        b, q = _parse_formula(seq, q + 1)
        if q >= len(seq) or seq[q] != RP:
            raise _ParseError
        return ('imp', a, b), q + 1
    raise _ParseError


def _prepare(seq):
    out = []
    for s in seq:
        t = _norm(s)
        if t is None or not is_symbol(t):
            return None
        out.append(t)
    return out


def parse(seq):
    """Parse a whole formula; return the tree or None."""
    toks = _prepare(seq)
    if toks is None:
        return None
    try:
        tree, p = _parse_formula(toks, 0)
    except _ParseError:
        return None
    if p != len(toks):
        return None
    return tree


def is_formula(seq, minus=False):
    toks = _prepare(seq)
    if toks is None or parse(toks) is None:
        return False
    if minus and THETA in toks:
        return False
    return True


# ---------------------------------------------------------------- unparse
def _unparse_term(t):
    if t[0] == 'var':
        return [x(t[1])]
    if t[0] == 'const':
        return [c(t[1])]
    out = [t[1], LP]
    for a in t[2]:
        out += _unparse_term(a)
    return out + [RP]


def unparse(tree):
    k = tree[0]
    if k == 'bot':
        return [BOT]
    if k == 'in':
        return [LP] + _unparse_term(tree[1]) + [IN] + _unparse_term(tree[2]) + [RP]
    if k == 'rel':
        out = [tree[1], LP]
        for a in tree[2]:
            out += _unparse_term(a)
        return out + [RP]
    if k == 'imp':
        return [LP] + unparse(tree[1]) + [IMP] + unparse(tree[2]) + [RP]
    if k == 'not':
        return [NOT] + unparse(tree[1])
    if k == 'ex':
        return [EX, x(tree[1]), LP] + unparse(tree[2]) + [RP]
    raise ValueError(tree)


# ---------------------------------------------------------------- variables
def _parse_or_raise(seq):
    tree = parse(seq)
    if tree is None:
        raise ValueError("not a formula")
    return tree


def _term_vars(t):
    if t[0] == 'var':
        return {t[1]}
    if t[0] == 'const':
        return set()
    out = set()
    for a in t[2]:
        out |= _term_vars(a)
    return out


def _fv(tree):
    k = tree[0]
    if k == 'bot':
        return set()
    if k == 'in':
        return _term_vars(tree[1]) | _term_vars(tree[2])
    if k == 'rel':
        out = set()
        for a in tree[2]:
            out |= _term_vars(a)
        return out
    if k == 'imp':
        return _fv(tree[1]) | _fv(tree[2])
    if k == 'not':
        return _fv(tree[1])
    if k == 'ex':
        return _fv(tree[2]) - {tree[1]}
    raise ValueError(tree)


def free_vars(seq):
    return _fv(_parse_or_raise(seq))


def all_var_indices(seq):
    """Indices of every variable symbol occurring in seq (free or bound)."""
    out = set()
    for s in seq:
        t = _norm(s)
        if t is not None and is_var(t):
            out.add(t[2])
    return out


# ---------------------------------------------------------------- semantics
def _eval(t, A, sigma):
    if t[0] == 'var':
        return sigma[t[1]]
    if t[0] == 'const':
        return A.Cn[c(t[1])]
    args = tuple(_eval(a, A, sigma) for a in t[2])
    return A.Fn[(t[1], args)]


def _sat(tree, A, sigma):
    k = tree[0]
    if k == 'bot':
        return False
    if k == 'in':
        return (_eval(tree[1], A, sigma), _eval(tree[2], A, sigma)) in A.E
    if k == 'rel':
        return (tree[1], tuple(_eval(a, A, sigma) for a in tree[2])) in A.Rel
    if k == 'imp':
        return (not _sat(tree[1], A, sigma)) or _sat(tree[2], A, sigma)
    if k == 'not':
        return not _sat(tree[1], A, sigma)
    if k == 'ex':
        i = tree[1]
        for a in A.dom:
            s2 = dict(sigma)
            s2[i] = a
            if _sat(tree[2], A, s2):
                return True
        return False
    raise ValueError(tree)


def sat(seq, A, sigma):
    return _sat(_parse_or_raise(seq), A, dict(sigma))


def _assignments(indices, dom, base=None):
    idx = sorted(indices)
    for vals in product(list(dom), repeat=len(idx)):
        s = dict(base or {})
        s.update(zip(idx, vals))
        yield s


def holds(seq, A):
    tree = _parse_or_raise(seq)
    return all(_sat(tree, A, s) for s in _assignments(_fv(tree), A.dom))


# ---------------------------------------------------------------- substitution
def _rename_term(t, i, j):
    if t[0] == 'var':
        return ('var', j) if t[1] == i else t
    if t[0] == 'const':
        return t
    return ('fn', t[1], [_rename_term(a, i, j) for a in t[2]])


def _tree_vars(tree):
    return all_var_indices(unparse(tree))


def _subst(tree, i, j):
    """tree[x_j / x_i] by the original rule.  The fresh index for renaming a
    bound y = x_j is the least index not occurring in the current subformula
    ∃y(Q), nor equal to i or j."""
    k = tree[0]
    if k == 'bot':
        return tree
    if k == 'in':
        return ('in', _rename_term(tree[1], i, j), _rename_term(tree[2], i, j))
    if k == 'rel':
        return ('rel', tree[1], [_rename_term(a, i, j) for a in tree[2]])
    if k == 'imp':
        return ('imp', _subst(tree[1], i, j), _subst(tree[2], i, j))
    if k == 'not':
        return ('not', _subst(tree[1], i, j))
    if k == 'ex':
        y, Q = tree[1], tree[2]
        if y == i:
            return tree
        if y == j:
            used = _tree_vars(tree) | {i, j}
            z = 0
            while z in used:
                z += 1
            Q = _subst(Q, y, z)  # z is fresh in Q, so this is a plain rename
            y = z
        return ('ex', y, _subst(Q, i, j))
    raise ValueError(tree)


def subst_var(seq, i, j):
    return unparse(_subst(_parse_or_raise(seq), i, j))


# ---------------------------------------------------------------- IsDefinition
def _isdef_body(P, P1, A, sigma):
    """σ ⊨ ∃x_0 ( P ∧ ∀x_1 ( P1 → x_1 = x_0 ) ) with P1 = P[x_1/x_0]."""
    for a in A.dom:
        s0 = dict(sigma)
        s0[0] = a
        if not _sat(P, A, s0):
            continue
        ok = True
        for b in A.dom:
            s1 = dict(s0)
            s1[1] = b  # the outer ∀x_1 captures any free x_1 here
            if _sat(P1, A, s1) and b != a:
                ok = False
                break
        if ok:
            return True
    return False


def is_definition(seq, A):
    P = _parse_or_raise(seq)
    P1 = _subst(P, 0, 1)
    # free vars of IsDefinition(P) = FV(P) \ {0}
    fv = _fv(P) - {0}
    return all(_isdef_body(P, P1, A, s) for s in _assignments(fv, A.dom))


def definable(m, A, seq):
    if m not in list(A.dom):
        return False
    if not is_definition(seq, A):
        return False
    P = _parse_or_raise(seq)
    fv = _fv(P) - {0}
    return all(_sat(P, A, s) for s in _assignments(fv, A.dom, {0: m}))


# ---------------------------------------------------------------- defines
def _is_pure(seq):
    toks = _prepare(seq)
    if toks is None:
        return False
    for s in toks:
        if not (s in (BOT, IMP, NOT, EX, LP, RP, IN) or is_var(s)):
            return False
    return parse(toks) is not None


def defines(seq, tau, X):
    if not _is_pure(seq):
        return None
    X = frozenset(X)
    need = all_var_indices(seq) - {0}
    if set(tau.keys()) != need:
        return None
    if any(v not in X for v in tau.values()):
        return None
    A = SimpleNamespace(dom=list(X), E={(a, b) for a in X for b in X if a in b},
                        Cn={}, Fn={}, Rel=set())
    P = _parse_or_raise(seq)
    out = set()
    for z in X:
        s = dict(tau)
        s[0] = z
        if _sat(P, A, s):
            out.add(z)
    return frozenset(out)


# ---------------------------------------------------------------- Theta
def theta(seq, A, order):
    if not is_formula(seq, minus=True):
        for a in A.dom:
            if a == frozenset():
                return a
        return None
    P = _parse_or_raise(seq)
    Ns = sorted(all_var_indices(seq))
    dom = list(A.dom)
    sigmas = [tuple(v) for v in product(dom, repeat=len(Ns))]
    Z = {sg for sg in sigmas if _sat(P, A, dict(zip(Ns, sg)))}

    def dep_only(pos):
        # membership in Z is a function of σ(i) alone
        seen = {}
        for sg in sigmas:
            key = sg[pos]
            val = sg in Z
            if key in seen and seen[key] != val:
                return False
            seen[key] = val
        return True

    dep = [dep_only(p) for p in range(len(Ns))]

    def good(a):
        if not Z:
            return True
        for p in range(len(Ns)):
            if dep[p]:
                for sg in sigmas:
                    sg2 = sg[:p] + (a,) + sg[p + 1:]
                    if sg2 not in Z:
                        return False
        return True

    for a in order:
        if good(a):
            return a
    return None


def henkin_ok(seq, A, value):
    if not is_formula(seq, minus=True):
        return True
    P = _parse_or_raise(seq)
    fv = _fv(P)
    if len(fv) > 1:
        return True
    if not fv:
        return True
    (i,) = fv
    if any(_sat(P, A, {i: a}) for a in A.dom):
        return _sat(P, A, {i: value})
    return True


# ---------------------------------------------------------------- next level
def next_level(X, order, defs):
    """Return (X1, order1) per SPEC2 §9."""
    X = frozenset(X)
    X1 = frozenset(y for (_, _, y) in defs)
    pos = {a: k for k, a in enumerate(order)}

    def def_key(n, tau):
        # (n, tau) ordered by n, then lexicographically by tau values in
        # increasing key order, each value compared by its position in `order`.
        return (n, tuple(pos[tau[k]] for k in sorted(tau)))

    least = {}
    for (n, tau, y) in defs:
        if y in X:
            continue
        key = def_key(n, tau)
        if y not in least or key < least[y]:
            least[y] = key

    old = [a for a in order if a in X1]
    new = sorted(least, key=lambda a: least[a])
    return X1, old + new


# ---------------------------------------------------------------- U values
def _vn(k):
    s = frozenset()
    for _ in range(k):
        s = s | {s}
    return s


def _ordinal_value(v):
    """Natural number k if v is the von Neumann ordinal k, else None."""
    if not isinstance(v, frozenset):
        return None
    k = len(v)
    return k if v == _vn(k) else None


def u_values(D, gamma, SU):
    out = {}
    for v in D:
        k = _ordinal_value(v)
        out[v] = SU[k] if (k is not None and k < gamma) else frozenset()
    return out


# ---------------------------------------------------------------- self-test
if __name__ == "__main__":
    def ELEM(t1, t2):
        return [LP, t1, IN, t2, RP]

    def IMPL(a, b):
        return [LP] + a + [IMP] + b + [RP]

    def EXISTS(i, a):
        return [EX, x(i), LP] + a + [RP]

    # --- syntax
    assert is_formula([BOT])
    assert is_formula(ELEM(x(0), x(1)))
    assert is_formula(IMPL([BOT], [NOT, BOT]))
    assert is_formula(EXISTS(3, ELEM(x(3), c(2))))
    assert is_formula([r(0, 4), LP, RP])
    assert is_formula([r(2, 1), LP, x(0), f(0, 7), LP, RP, RP])
    assert is_formula([LP, U, LP, x(0), RP, IN, THETA, LP, c(0), RP, RP])
    assert not is_formula([LP, U, LP, x(0), RP, IN, THETA, LP, c(0), RP, RP], minus=True)
    assert not is_formula([IN, LP, x(0), x(1), RP])           # ∈ only infix
    assert not is_formula([(8, 2, 0, 0), LP, RP])             # non-symbol
    assert not is_formula([(9, 5, 0, 1)])
    assert not is_formula(ELEM(x(0), x(1)) + [BOT])           # trailing junk
    assert not is_formula([EX, c(0), LP, BOT, RP])
    assert not is_formula([LP, BOT, RP])
    assert not is_formula([])

    # --- free vars
    phi = IMPL(ELEM(x(0), x(1)), EXISTS(1, ELEM(x(1), x(2))))
    assert free_vars(phi) == {0, 1, 2}
    assert free_vars(EXISTS(0, ELEM(x(0), x(0)))) == set()

    # --- substitution
    # (∃x1 (x1 ∈ x0))[x1/x0] -> least index not in {0,1} -> x2
    s = subst_var(EXISTS(1, ELEM(x(1), x(0))), 0, 1)
    assert s == EXISTS(2, ELEM(x(2), x(1))), s
    # bound x0: no substitution
    s = subst_var(EXISTS(0, ELEM(x(0), x(1))), 0, 1)
    assert s == EXISTS(0, ELEM(x(0), x(1)))
    # rename even when x_i is not free inside
    s = subst_var(EXISTS(1, ELEM(x(1), x(1))), 0, 1)
    assert s == EXISTS(2, ELEM(x(2), x(2))), s
    # fresh index skips indices that occur: ∃x1(x1∈x2 → x0∈x0) [x1/x0] -> x3
    s = subst_var(EXISTS(1, IMPL(ELEM(x(1), x(2)), ELEM(x(0), x(0)))), 0, 1)
    assert s == EXISTS(3, IMPL(ELEM(x(3), x(2)), ELEM(x(1), x(1)))), s
    # plain free replacement
    assert subst_var(ELEM(x(0), x(5)), 0, 1) == ELEM(x(1), x(5))

    # --- hereditarily finite structure V_3 = {0, 1, 2, {1}}
    e0 = frozenset()
    e1 = frozenset({e0})
    e2 = frozenset({e0, e1})
    e3 = frozenset({e1})
    X = frozenset({e0, e1, e2, e3})
    A = SimpleNamespace(dom=[e0, e1, e2, e3],
                        E={(a, b) for a in X for b in X if a in b},
                        Cn={}, Fn={}, Rel=set())

    empty = [NOT] + EXISTS(1, ELEM(x(1), x(0)))       # x0 has no elements
    assert sat(empty, A, {0: e0}) and not sat(empty, A, {0: e1})
    assert holds(EXISTS(0, empty), A)
    assert not holds(ELEM(x(0), x(1)), A)             # closure
    assert holds(IMPL(ELEM(x(0), x(1)), ELEM(x(0), x(1))), A)

    # empty set is definable; e1 is not definable by "empty"
    assert is_definition(empty, A)
    assert definable(e0, A, empty)
    assert not definable(e1, A, empty)
    # "x0 ∈ x0" is never satisfied -> not a definition
    assert not is_definition(ELEM(x(0), x(0)), A)
    # "x2 ∈ x0" (param free x2): for x2=e0 three witnesses -> not definition
    assert not is_definition(ELEM(x(2), x(0)), A)
    # "x0 ∈ x1" with free x1 captured by outer ∀x1:
    # inner P[x1/x0] = (x1 ∈ x1), never true -> second conjunct trivially true;
    # first conjunct needs ∃x0 (x0 ∈ x1) for every x1 -> fails at x1 = e0
    assert not is_definition(ELEM(x(0), x(1)), A)
    # "x1 ∈ x0 ∨-ish": P = ¬(x0 ∈ x1); P[x1/x0] = ¬(x1∈x1) true for all b.
    # So needs exactly one element: false.
    assert not is_definition([NOT] + ELEM(x(0), x(1)), A)
    # 1-element structure: anything satisfiable is a definition
    B = SimpleNamespace(dom=[e0], E=set(), Cn={}, Fn={}, Rel=set())
    assert is_definition([NOT] + ELEM(x(0), x(1)), B)
    assert definable(e0, B, [NOT] + ELEM(x(0), x(1)))
    assert not definable(e1, B, [NOT] + ELEM(x(0), x(1)))

    # --- defines
    P = ELEM(x(1), x(0))                              # z ∋ tau(1)
    assert defines(P, {1: e0}, X) == frozenset({e1, e2})
    assert defines(P, {}, X) is None
    assert defines(P, {1: e0, 2: e0}, X) is None
    Q = EXISTS(2, IMPL(ELEM(x(2), x(0)), ELEM(x(2), x(1))))
    assert defines(Q, {1: e0}, X) is None             # bound x2 must be in tau
    # ∃x2 (x2∈x0 → x2∈x1) is true unless every element... with x1 = e0:
    # true iff exists x2 not in x0  -> z ≠ "everything"; all z qualify here
    assert defines(Q, {1: e0, 2: e3}, X) == X
    assert defines(empty, {1: e2}, X) == frozenset({e0})
    assert defines([r(0, 0), LP, RP], {}, X) is None  # not pure

    # --- theta
    order = [e0, e1, e2, e3]
    nonminus = [LP, THETA, LP, x(0), RP, IN, x(0), RP]
    assert theta(nonminus, A, order) == e0
    assert theta([BOT, BOT], A, list(reversed(order))) == e0  # not formula
    Anon = SimpleNamespace(dom=[e1], E=set(), Cn={}, Fn={}, Rel=set())
    assert theta(nonminus, Anon, [e1]) is None
    # P = ∃x1 (x1 ∈ x0): Ns={0,1}; dep_only(0) true; dep_only(1) false
    # (same x1, different x0 can differ).  good(a) iff a nonempty.
    nonempty = EXISTS(1, ELEM(x(1), x(0)))
    assert theta(nonempty, A, order) == e1
    assert theta(nonempty, A, [e0, e3, e1]) == e3
    # 1-element-ish: B dom=[e0], E empty: ∃x1(x1∈x0) never true -> Z empty
    assert theta(nonempty, B, [e0]) == e0
    # Z = everything (tautology with vars): dep_only all true, all good
    taut = IMPL(ELEM(x(0), x(1)), ELEM(x(0), x(1)))
    assert theta(taut, A, [e2]) == e2
    # P = (x1 ∈ x0): dep_only(0) false, dep_only(1) false -> first in order
    assert theta(ELEM(x(1), x(0)), A, list(reversed(order))) == e3
    # P = ¬∃x1(x1∈x0): Z = σ with x0 = e0; only x0 depends -> e0 good; x1:
    # dep_only(1) false (x0 varies). result first good = e0
    assert theta(empty, A, [e3, e2, e0, e1]) == e0
    # closed P with Z empty -> first in order
    assert theta([BOT], A, [e2, e0]) == e2
    # closed true P: Ns empty, good everything
    assert theta([NOT, BOT], A, [e3]) == e3
    # P = (x0 ∈ x2) with x2 replaced: (x0 ∈ x0) false for all -> Z empty -> first
    assert theta(ELEM(x(0), x(0)), A, [e1]) == e1

    # --- henkin_ok
    assert henkin_ok(empty, A, e0)
    assert not henkin_ok(empty, A, e1)
    assert henkin_ok(ELEM(x(0), x(0)), A, e1)        # no witness -> vacuous
    assert henkin_ok(ELEM(x(0), x(1)), A, e1)        # two free vars -> True
    assert henkin_ok(nonminus, A, e3)                # not Formula₋ -> True
    assert henkin_ok([BOT], A, e0)                   # closed -> True
    v = theta(empty, A, order)
    assert henkin_ok(empty, A, v)

    # --- structure with constants / functions / relations
    D = SimpleNamespace(dom=[0, 1],
                        E={(0, 1)},
                        Cn={c(0): 1},
                        Fn={(f(1, 0), (0,)): 1, (f(1, 0), (1,)): 0},
                        Rel={(r(1, 0), (1,))})
    assert sat([r(1, 0), LP, c(0), RP], D, {})
    assert sat([r(1, 0), LP, f(1, 0), LP, x(0), RP, RP], D, {0: 0})
    assert not sat([r(1, 0), LP, f(1, 0), LP, x(0), RP, RP], D, {0: 1})
    # x0 ∈ c0 holds only for x0 = 0
    assert not holds(ELEM(x(0), c(0)), D)
    assert holds(EXISTS(0, ELEM(x(0), c(0))), D)
    # f(c0) = f(1) = 0, and (0, 1) ∈ E
    assert sat([LP, f(1, 0), LP, c(0), RP, IN, c(0), RP], D, {})

    # --- next_level
    L0 = frozenset()
    o0 = []
    # from L_0 = ∅: only definable subset is ∅
    X1, o1 = next_level(L0, o0, [(5, {}, e0), (2, {}, e0)])
    assert X1 == frozenset({e0}) and o1 == [e0]
    # from {e0}: new e1 (by n=3) and e0 (old)
    X2, o2 = next_level(X1, o1, [(7, {1: e0}, e0), (3, {1: e0}, e1)])
    assert X2 == frozenset({e0, e1}) and o2 == [e0, e1]
    # new elements ordered by least (n, tau); old ones first, in `order`
    Y = frozenset({e0, e1})
    ordY = [e1, e0]                      # deliberately non-standard order
    defs = [
        (4, {1: e0, 2: e0}, e2),         # e2 least: (4, (1,1))
        (4, {1: e1, 2: e0}, e3),         # e3 least: (4, (0,1)) < e2's
        (9, {1: e1, 2: e1}, e2),
        (1, {1: e0, 2: e1}, e0),         # old element, ignored for keys
        (6, {1: e1, 2: e1}, e1),
    ]
    Y1, oY1 = next_level(Y, ordY, defs)
    assert Y1 == frozenset({e0, e1, e2, e3})
    assert oY1 == [e1, e0, e3, e2], oY1
    # n dominates tau
    defs2 = [(2, {1: e0}, e3), (1, {1: e1}, e2)]
    _, o = next_level(Y, ordY, defs2)
    assert o == [e2, e3]
    # second key decides when first is equal
    defs3 = [(4, {1: e1, 2: e0}, e2), (4, {1: e1, 2: e1}, e3)]
    _, o = next_level(Y, ordY, defs3)
    assert o == [e3, e2]                 # e1 precedes e0 in ordY

    # --- u_values
    n0, n1, n2 = _vn(0), _vn(1), _vn(2)
    assert n1 == e1 and n2 == e2
    SU = {0: frozenset(), 1: frozenset({n0}), 2: frozenset({n0, n1})}
    Dm = [n0, n1, n2, e3, frozenset({n2})]
    uv = u_values(Dm, 2, SU)
    assert uv == {n0: SU[0], n1: SU[1], n2: frozenset(),
                  e3: frozenset(), frozenset({n2}): frozenset()}
    uv = u_values(Dm, 3, SU)
    assert uv[n2] == SU[2] and uv[e3] == frozenset()
    assert u_values([n0, 5], 0, {}) == {n0: frozenset(), 5: frozenset()}

    print("all self-tests passed")
