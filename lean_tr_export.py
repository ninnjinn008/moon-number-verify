"""
書き写しの検証（改訂42）のための書き出し。

各部品 X について、生成プログラムが実際に作る式（下の層もすべて展開したもの）を作り、
その中で下の層の部品の呼び出しから生じた部分木を、名前つきの関係 .rel "名前" c [引数] に置き換えたもの r_X を書き出す
（c はその呼び出しの時点の新しい変数の番号。部分木は「下の層の部品を単独で生成した式」の変数を付け替えたもの）。
Lean 側では
  ・r_X の意味が意図した条件と一致すること（手で証明する）
  ・r_X の .rel をそれぞれ下の層の展開形に戻したもの full_X が、意図した条件を満たすこと（一般的な補題で自動的に）
  ・full_X が生成プログラムの出力そのもの（lit_X）と一致すること（rfl）
を確かめる。
"""
import sys, functools
from fol import Ctx, Atom, Not, And, All, Oracle
import arith as A, parse as P, metacode as MC, semantics as SM, definable as DF, ordinals as OR, structure as ST, lorder as LO, cnf as CN, inacc_seq as IS, ffunc as FF

REC = {}
KEEP = []

def wrap(mod, attr, name_fn):
    fn = getattr(mod, attr)
    if getattr(fn, "_wrapped", False): return
    @functools.wraps(fn)
    def w(ctx, *args, **kw):
        c = ctx.n
        r = fn(ctx, *args, **kw)
        nm, as_ = name_fn(*args, **kw)
        REC[id(r)] = (nm, as_, c)
        KEEP.append(r)
        return r
    w._wrapped = True
    setattr(mod, attr, w)

def plain(name, k): return lambda *a: (name, list(a[:k]))
for attr, nm, k in [("empty", "empty", 1), ("succ_of", "succ", 2), ("trans", "trans", 1), ("nat", "nat", 1),
                    ("pair", "pair", 3), ("triple", "triple", 4), ("hyper_table", "hyper_table", 2),
                    ("hyper", "hyper", 4), ("add", "add", 3), ("mul", "mul", 3), ("exp", "exp", 3),
                    ("divides", "divides", 2), ("prime", "prime", 1), ("_is_one", "is_one", 1),
                    ("prime_table", "prime_table", 1), ("nth_prime", "nth_prime", 2), ("seqfun", "seqfun", 2),
                    ("prod_table", "prod_table", 2), ("encode", "encode", 2)]:
    wrap(A, attr, plain(nm, k))
wrap(A, "numeral", lambda v, k: (f"numeral{k}", [v]))
wrap(P, "tuple4", plain("tuple4", 1))
wrap(P, "is_punct", lambda t, a0: (f"punct{a0}", [t]))
for attr, nm in [("is_var", "symvar"), ("is_const", "symconst"), ("is_func", "symfunc"), ("is_rel", "symrel"),
                 ("is_elem", "symelem"), ("is_theta", "symtheta")]:
    wrap(P, attr, plain(nm, 1))
wrap(P, "plus2", plain("plus2", 2))
wrap(P, "certificate_ok", plain("certificate", 4))
wrap(P, "formula", lambda s, minus=False: ("formula_minus" if minus else "formula", [s]))
wrap(SM, "sat", lambda *a, extended=False: ("sat_ext" if extended else "sat", list(a[:7])))

# sat の内部の部品（SatParts のメソッド）。引数 = 使う集合の変数（fields）＋メソッドの引数
SP_PARTS = [("assign", "assign", ["Ns", "dom"], 1), ("update", "update", ["Ns", "dom"], 4),
            ("inS", "in_s", ["S"], 3), ("in_pair_set", "in_pair", [], 3), ("in_triple_set", "in_triple", [], 4),
            ("cons", "cons", [], 3), ("term_clause", "term_clause", ["s", "Cn", "Fn", "TV"], 4),
            ("list_clause", "list_clause", ["C", "K0", "TV"], 5),
            ("formula_clause", "formula_clause", ["s", "dom", "E", "Rel", "Ns", "C", "K0", "K1", "TV", "S"], 3),
            ("tv_ok", "tv_ok", ["s", "dom", "Cn", "Fn", "Ns", "C", "K0", "TV"], 0),
            ("s_ok", "s_ok", ["s", "dom", "E", "Rel", "Ns", "C", "K0", "K1", "TV", "S"], 0),
            ("varset", "varset", ["s", "h", "Ns"], 0)]
SP_FIELDS = ["s", "dom", "E", "Cn", "Fn", "Rel", "K0", "K1", "h", "Ns", "C", "TV", "S"]

def wrapm(cls, attr, name, fields):
    fn = getattr(cls, attr)
    if getattr(fn, "_wrapped", False): return
    @functools.wraps(fn)
    def w(self, *args):
        c = self.ctx.n
        r = fn(self, *args)
        REC[id(r)] = (name, [getattr(self, f) for f in fields] + list(args), c)
        KEEP.append(r)
        return r
    w._wrapped = True
    setattr(cls, attr, w)
for attr, nm, fields, _ in SP_PARTS:
    wrapm(SM.SatParts, attr, nm, fields)
wrapm(DF.WParts, "assign_W", "assign_w", ["W", "dom"])
wrapm(DF.WParts, "update", "update_w", ["W", "dom"])
wrap(DF, "is_definition", lambda *a, mutate=False: ("is_definition", list(a[:6])))
wrap(DF, "param_true", plain("param_true", 7))
wrap(DF, "definable_in", lambda *a, mutate=False: ("definable_in", list(a[:7])))
wrap(OR, "ordinal", plain("ordinal", 1))
wrap(ST, "e_restrict", plain("e_restrict", 2))
for attr, nm, k in [("_func_on", "func_on", 3), ("_in_pair", "in_pair_l", 3), ("pure", "pure", 2),
                    ("def_code", "def_code", 1), ("defines", "defines", 4), ("lex_less", "lex_less", 3),
                    ("def_less", "def_less", 5), ("def_table", "def_table", 2), ("new_less", "new_less", 4),
                    ("step", "step", 4), ("l_order", "l_order", 3)]:
    wrap(LO, attr, plain(nm, k))

def sp_standalone(attr, fields, nargs):
    def mk(ctx, *vs):
        vals = dict(zip(fields, vs[:len(fields)]))
        dummy = {f: 10 ** 7 + i for i, f in enumerate(SP_FIELDS)}
        sp = SM.SatParts(ctx, *[vals.get(f, dummy[f]) for f in SP_FIELDS])
        return getattr(sp, attr)(*vs[len(fields):])
    return mk
wrap(MC, "metacode", plain("metacode", 2))
wrap(MC, "formula_code", lambda n, minus=False: ("formula_code_minus" if minus else "formula_code", [n]))
wrap(ST, "theta_value", plain("theta_value", 3))
for attr, nm, k in [("least_good", "least_good", 8), ("theta_L", "theta_l", 6)]:
    wrap(LO, attr, plain(nm, k))
# 改訂52：残りの層（cnf・ordinals・inacc_seq・structure・struct_rec・ffunc）
wrap(CN, "dec", plain("dec", 3))
wrap(CN, "row_shape", lambda r, k0: (f"row_shape{k0}", [r]))
for attr, nm, k in [("table_ok", "table_ok", 1), ("cnf_cmp", "cnf_cmp", 3), ("cnf_lt", "cnf_lt", 2)]:
    wrap(CN, attr, plain(nm, k))
for attr, nm, k in [("is_omega", "omega", 1), ("func", "func", 3), ("bij", "bij", 3), ("regular", "regular", 1),
                    ("_power_of", "power_of", 2), ("strong_limit", "strong_limit", 1), ("inaccessible", "inaccessible", 1)]:
    wrap(OR, attr, plain(nm, k))
for attr, nm, k in [("o_ok", "o_ok", 2), ("ord_of", "ord_of", 2), ("lam_ok", "lam_ok", 2), ("eps0", "eps0", 1),
                    ("lam_of", "lam_of", 2)]:
    wrap(IS, attr, plain(nm, k))
for attr, nm, k in [("vstage", "vstage", 2), ("cn_ok", "cn_ok", 1), ("theta_ok", "theta_ok", 2)]:
    wrap(ST, attr, plain(nm, k))
wrap(ST, "fn_ok", lambda Fn, D, alpha, SU=None: ("fn_ok", [Fn, D, alpha, SU]))
for attr, nm, k in [("struct_rec", "struct_rec", 2), ("struct_full", "struct_full", 6)]:
    wrap(LO, attr, plain(nm, k))
for attr, nm, k in [("_func_on", "func_on2", 2), ("struct_table", "struct_table", 2), ("definable_set", "definable_set", 3),
                    ("finite_sum", "finite_sum", 2), ("f_val", "f_val", 2), ("lngn", "lngn", 1)]:
    wrap(FF, attr, plain(nm, k))
wrap(FF, "iterate10", lambda a, x, times=10: ("iterate10", [a, x]))

# 部品：(Lean 名, 引数の個数, 単独で生成する関数)
PARTS = [
    ("empty", 1, lambda c, a: A.empty(c, a)),
    ("succ", 2, lambda c, a, b: A.succ_of(c, a, b)),
    ("trans", 1, lambda c, a: A.trans(c, a)),
    ("pair", 3, lambda c, *v: A.pair(c, *v)),
    ("is_one", 1, lambda c, a: A._is_one(c, a)),
] + [(f"numeral{k}", 1, (lambda k: lambda c, a: A.numeral(c, a, k))(k)) for k in range(10)] + [
    ("nat", 1, lambda c, a: A.nat(c, a)),
    ("triple", 4, lambda c, *v: A.triple(c, *v)),
    ("hyper_table", 2, lambda c, *v: A.hyper_table(c, *v)),
    ("hyper", 4, lambda c, *v: A.hyper(c, *v)),
    ("add", 3, lambda c, *v: A.add(c, *v)),
    ("mul", 3, lambda c, *v: A.mul(c, *v)),
    ("exp", 3, lambda c, *v: A.exp(c, *v)),
    ("divides", 2, lambda c, *v: A.divides(c, *v)),
    ("prime", 1, lambda c, a: A.prime(c, a)),
    ("prime_table", 1, lambda c, a: A.prime_table(c, a)),
    ("nth_prime", 2, lambda c, *v: A.nth_prime(c, *v)),
    ("seqfun", 2, lambda c, *v: A.seqfun(c, *v)),
    ("prod_table", 2, lambda c, *v: A.prod_table(c, *v)),
    ("encode", 2, lambda c, *v: A.encode(c, *v)),
    ("tuple4", 1, lambda c, a: P.tuple4(c, a)),
    ("metacode", 2, lambda c, *v: MC.metacode(c, *v)),
] + [(f"punct{a}", 1, (lambda a: lambda c, t: P.is_punct(c, t, a))(a)) for a in range(6)] + [
    ("symvar", 1, lambda c, t: P.is_var(c, t)),
    ("symconst", 1, lambda c, t: P.is_const(c, t)),
    ("symfunc", 1, lambda c, t: P.is_func(c, t)),
    ("symrel", 1, lambda c, t: P.is_rel(c, t)),
    ("symelem", 1, lambda c, t: P.is_elem(c, t)),
    ("symtheta", 1, lambda c, t: P.is_theta(c, t)),
    ("plus2", 2, lambda c, *v: P.plus2(c, *v)),
    ("certificate", 4, lambda c, *v: P.certificate_ok(c, *v)),
    ("formula", 1, lambda c, s: P.formula(c, s)),
    ("formula_minus", 1, lambda c, s: P.formula(c, s, True)),
] + [(nm, len(fields) + nargs, sp_standalone(attr, fields, nargs)) for attr, nm, fields, nargs in SP_PARTS] + [
    ("sat", 7, lambda c, *v: SM.sat(c, *v)),
    ("sat_ext", 7, lambda c, *v: SM.sat(c, *v, extended=True)),
    ("assign_w", 3, lambda c, W, dom, sg: DF.WParts(c, W, dom).assign_W(sg)),
    ("update_w", 6, lambda c, W, dom, *v: DF.WParts(c, W, dom).update(*v)),
    ("is_definition", 6, lambda c, *v: DF.is_definition(c, *v)),
    ("param_true", 7, lambda c, *v: DF.param_true(c, *v)),
    ("definable_in", 7, lambda c, *v: DF.definable_in(c, *v)),
    ("ordinal", 1, lambda c, *v: OR.ordinal(c, *v)),
    ("e_restrict", 2, lambda c, *v: ST.e_restrict(c, *v)),
    ("func_on", 3, lambda c, *v: LO._func_on(c, *v)),
    ("in_pair_l", 3, lambda c, *v: LO._in_pair(c, *v)),
    ("pure", 2, lambda c, *v: LO.pure(c, *v)),
    ("def_code", 1, lambda c, *v: LO.def_code(c, *v)),
    ("defines", 4, lambda c, *v: LO.defines(c, *v)),
    ("lex_less", 3, lambda c, *v: LO.lex_less(c, *v)),
    ("def_less", 5, lambda c, *v: LO.def_less(c, *v)),
    ("def_table", 2, lambda c, *v: LO.def_table(c, *v)),
    ("new_less", 4, lambda c, *v: LO.new_less(c, *v)),
    ("step", 4, lambda c, *v: LO.step(c, *v)),
    ("l_order", 3, lambda c, *v: LO.l_order(c, *v)),
    ("formula_code_minus", 1, lambda c, n: MC.formula_code(c, n, minus=True)),
    ("theta_value", 3, lambda c, *v: ST.theta_value(c, *v)),
    ("least_good", 8, lambda c, *v: LO.least_good(c, *v)),
    ("theta_l", 6, lambda c, *v: LO.theta_L(c, *v)),
    ("numeral10", 1, lambda c, a: A.numeral(c, a, 10)),
    ("numeral11", 1, lambda c, a: A.numeral(c, a, 11)),
    ("numeral12", 1, lambda c, a: A.numeral(c, a, 12)),
    ("dec", 3, lambda c, *v: CN.dec(c, *v)),
    ("row_shape0", 1, lambda c, r: CN.row_shape(c, r, 0)),
    ("row_shape1", 1, lambda c, r: CN.row_shape(c, r, 1)),
    ("table_ok", 1, lambda c, *v: CN.table_ok(c, *v)),
    ("cnf_cmp", 3, lambda c, *v: CN.cnf_cmp(c, *v)),
    ("cnf_lt", 2, lambda c, *v: CN.cnf_lt(c, *v)),
    ("omega", 1, lambda c, *v: OR.is_omega(c, *v)),
    ("func", 3, lambda c, *v: OR.func(c, *v)),
    ("bij", 3, lambda c, *v: OR.bij(c, *v)),
    ("regular", 1, lambda c, *v: OR.regular(c, *v)),
    ("power_of", 2, lambda c, *v: OR._power_of(c, *v)),
    ("strong_limit", 1, lambda c, *v: OR.strong_limit(c, *v)),
    ("inaccessible", 1, lambda c, *v: OR.inaccessible(c, *v)),
    ("o_ok", 2, lambda c, *v: IS.o_ok(c, *v)),
    ("ord_of", 2, lambda c, *v: IS.ord_of(c, *v)),
    ("lam_ok", 2, lambda c, *v: IS.lam_ok(c, *v)),
    ("eps0", 1, lambda c, *v: IS.eps0(c, *v)),
    ("lam_of", 2, lambda c, *v: IS.lam_of(c, *v)),
    ("vstage", 2, lambda c, *v: ST.vstage(c, *v)),
    ("cn_ok", 1, lambda c, *v: ST.cn_ok(c, *v)),
    ("theta_ok", 2, lambda c, *v: ST.theta_ok(c, *v)),
    ("fn_ok", 4, lambda c, *v: ST.fn_ok(c, *v)),
    ("struct_rec", 2, lambda c, *v: LO.struct_rec(c, *v)),
    ("struct_full", 6, lambda c, *v: LO.struct_full(c, *v)),
    ("func_on2", 2, lambda c, *v: FF._func_on(c, *v)),
    ("struct_table", 2, lambda c, *v: FF.struct_table(c, *v)),
    ("definable_set", 3, lambda c, *v: FF.definable_set(c, *v)),
    ("finite_sum", 2, lambda c, *v: FF.finite_sum(c, *v)),
    ("f_val", 2, lambda c, *v: FF.f_val(c, *v)),
    ("iterate10", 2, lambda c, *v: FF.iterate10(c, *v)),
    ("lngn", 1, lambda c, *v: FF.lngn(c, *v)),
]

def term(f, root, used):
    if f is not root and id(f) in REC:
        nm, as_, c = REC[id(f)]
        used.add(nm)
        return f"(.rel .{nm} {c} [{', '.join(map(str, as_))}])"
    if isinstance(f, Atom): return f"(.{'mem' if f.op == '∈' else 'eq'} {f.a} {f.b})"
    if isinstance(f, Not): return f"(.neg {term(f.p, root, used)})"
    if isinstance(f, And): return f"(.conj {term(f.p, root, used)} {term(f.q, root, used)})"
    if isinstance(f, All): return f"(.all {f.v} {term(f.p, root, used)})"
    raise TypeError(f)

def lit(f):
    if isinstance(f, Atom): return f"(.{'mem' if f.op == '∈' else 'eq'} {f.a} {f.b})"
    if isinstance(f, Not): return f"(.neg {lit(f.p)})"
    if isinstance(f, And): return f"(.conj {lit(f.p)} {lit(f.q)})"
    if isinstance(f, All): return f"(.all {f.v} {lit(f.p)})"
    raise TypeError(f)

# 層ごとのファイル（改訂45）。部品を加えたとき、その層から後だけをビルドし直せばよい。
LAYERS = [("A", "empty", "metacode"), ("B", "punct0", "formula_minus"), ("C", "assign", "sat_ext"),
          ("D", "assign_w", "definable_in"), ("E", "ordinal", "l_order"),
          ("F", "formula_code_minus", "theta_l"), ("G", "numeral10", "cnf_lt"), ("H", "omega", "lam_of"),
          ("I", "vstage", "struct_full"), ("J", "func_on2", "lngn")]
# 生成プログラムの出力そのもの（lit）と記号列で照合する部品：各層の最上位と、TrNat が使う算術の部品
LIT = {"nat", "numeral2", "hyper", "add", "mul", "exp", "divides", "prime", "nth_prime", "encode", "metacode",
       "formula", "formula_minus"}

def layer_of(names):
    out, cur = {}, None
    for n in names:
        for L, a, b in LAYERS:
            if n == a: cur = L
        out[n] = cur
    return out

def main(out="lean"):
    names = [p[0] for p in PARTS]
    lay = layer_of(names)
    files = {L: [] for L, _, _ in LAYERS}
    lits = {L: [] for L, _, _ in LAYERS}
    checks = []
    prev = "TrCore"
    for L, _, _ in LAYERS:
        files[L] += [f"import {prev}", "set_option maxRecDepth 200000", "namespace Tr", "",
                     f"/-! 生成プログラムが書き出した部品（層 {L}。lean_tr_export.py による。手で編集しない）。 -/", ""]
        lits[L] += [f"import TrParts{L}", "set_option maxRecDepth 200000", "namespace Tr", "",
                    f"/-! 生成プログラムの出力そのもの（層 {L} の lit）と、展開した式 full_X との一致。 -/", ""]
        prev = f"TrParts{L}"
    for name, k, mk in PARTS:
        ctx = Ctx(start=0); vs = [ctx.fresh() for _ in range(k)]
        f = mk(ctx, *vs)
        used = set()
        L = lay[name]
        files[L].append(f"def r_{name} : F := {term(f, f, used)}")
        assert used <= set(k_of), (name, used - set(k_of))
        tbl = "fun nm => match nm with\n" + "".join(f"    | .{u} => some ({k_of[u]}, full_{u})\n" for u in sorted(used)) + "    | _ => none"
        files[L].append(f"def tbl_{name} : Nm → Option (Nat × F) := {tbl}")
        files[L].append(f"def full_{name} : F := expand tbl_{name} r_{name}")
        files[L].append("")
        if name in LIT:
            lits[L].append(f"def lit_{name} : F := {lit(f)}")
            lits[L].append(f"theorem full_lit_{name} : full_{name} = lit_{name} := rfl")
            lits[L].append("")
        checks.append(f"theorem chk_{name} : check3 tbl_{name} r_{name} = true := by kernel_rfl")
        checks.append(f"theorem rge_{name} : relGe {k} r_{name} = true := by kernel_rfl")
        k_of[name] = k
    for L, _, _ in LAYERS:
        open(f"{out}/TrParts{L}.lean", "w").write("\n".join(files[L] + ["end Tr"]) + "\n")
        open(f"{out}/TrLit{L}.lean", "w").write("\n".join(lits[L] + ["end Tr"]) + "\n")
    C = ["import TrExp", "set_option maxRecDepth 200000", "namespace Tr", "",
         "/-! .rel の引数が条件を満たすこと（check2）。 -/", ""] + checks + ["end Tr"]
    open(f"{out}/TrCheck.lean", "w").write("\n".join(C) + "\n")

k_of = {}
if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "lean")

def means(out="lean/TrMeans.lean"):
    L = ["/-", "  書き写しの検証：各部品について、展開した式 full_X の意味が意図した条件（Rstd）と一致すること（mean_full_X）。",
         "  lit を持つ部品については、生成プログラムの出力そのもの lit_X についても（mean_X）。",
         "  （lean_tr_export.py が書き出す。各部品の証明は TrRel.lean の rel_X と、一般的な補題 expand_ok2 による。）", "-/",
         "import TrCheck", "import TrRel", "import TrRelD", "import TrRelE", "import TrRelF", "import TrRelG", "import TrRelH", "import TrRelI", "import TrRelJ"] + [f"import TrLit{L}" for L, _, _ in LAYERS] + [
         "namespace Tr", "section", "variable {α : Type} (mem : α → α → Prop)", ""]
    for name, k, mk in PARTS:
        ctx = Ctx(start=0); vs = [ctx.fresh() for _ in range(k)]
        f = mk(ctx, *vs); used = set(); term(f, f, used)
        L.append(f"theorem bvt_{name} : BvOk tbl_{name} := by\n"
                 f"  intro n k g h\n"
                 f"  cases n <;> simp only [tbl_{name}, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h\n"
                 + "".join(f"  case {u} => obtain ⟨rfl, rfl⟩ := h; exact bvok_{u}\n" for u in sorted(used)) +
                 f"theorem bvok_{name} : ∀ v, v ∈ bv full_{name} → {k} ≤ v := by\n"
                 f"  rw [full_{name}]; exact bv_expand_ge tbl_{name} bvt_{name} {k} r_{name} chk_{name} rge_{name}\n")
        L.append(f"theorem mean_full_{name} (R0 : Nm → List α → Prop) (e : Nat → α) :\n"
                 f"    ev mem R0 full_{name} e ↔ Rstd mem .{name} ((List.range {k}).map e) := by\n"
                 f"  have htbl : ∀ n k g, tbl_{name} n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by\n"
                 f"    intro n k g h\n"
                 f"    cases n <;> simp only [tbl_{name}, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h\n"
                 + "".join(f"    case {u} => obtain ⟨rfl, rfl⟩ := h; exact mean_full_{u} mem R0\n" for u in sorted(used)) +
                 f"  rw [full_{name}, expand_ok3 mem R0 (Rstd mem) tbl_{name} htbl bvt_{name} r_{name} chk_{name} e]\n"
                 f"  exact rel_{name} mem e\n")
        if name in LIT:
            L.append(f"theorem mean_{name} (R0 : Nm → List α → Prop) (e : Nat → α) :\n"
                     f"    ev mem R0 lit_{name} e ↔ Rstd mem .{name} ((List.range {k}).map e) := by\n"
                     f"  rw [← full_lit_{name}]; exact mean_full_{name} mem R0 e\n")
    L += ["end", "end Tr"]
    open(out, "w").write("\n".join(L) + "\n")

if __name__ == "__main__":
    means()
