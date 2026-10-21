"""
生成プログラムの式を Lean の Fml に書き出し、Δ0 である部品には IsD0 の証明項も書き出す（改訂36）。

  python3 lean_export.py  →  lean/Export.lean を生成し、Lean で検査すると、
  各部品について「推移的なクラスの上で、制限した評価と全体での評価が一致する」という定理が得られる。
Δ0 かどうかの判定は Python 側でも行い、Δ0 でない部品は一覧として出力する（証明項は書き出さない）。
"""
import sys
from fol import Ctx, Atom, Not, And, All, Oracle
import arith as A, ordinals as OR, structure as ST

def is_ball(f):
    return (isinstance(f, All) and isinstance(f.p, Not) and isinstance(f.p.p, And)
            and isinstance(f.p.p.p, Atom) and f.p.p.p.op == '∈' and f.p.p.p.a == f.v and f.p.p.p.b != f.v)

def d0(f):
    if isinstance(f, Atom): return True
    if isinstance(f, Not): return d0(f.p)
    if isinstance(f, And): return d0(f.p) and d0(f.q)
    if isinstance(f, All): return is_ball(f) and d0(f.p.p.q)
    raise TypeError(f)

def term(f):
    if isinstance(f, Atom): return f"(.{'mem' if f.op == '∈' else 'eq'} {f.a} {f.b})"
    if isinstance(f, Not): return f"(.neg {term(f.p)})"
    if isinstance(f, And): return f"(.conj {term(f.p)} {term(f.q)})"
    if isinstance(f, All): return f"(.all {f.v} {term(f.p)})"
    raise TypeError(f)

def proof(f):
    if isinstance(f, Atom): return f"(IsD0.{'mem' if f.op == '∈' else 'eq'} {f.a} {f.b})"
    if isinstance(f, Not): return f"(IsD0.neg {proof(f.p)})"
    if isinstance(f, And): return f"(IsD0.conj {proof(f.p)} {proof(f.q)})"
    assert is_ball(f)
    return f"(IsD0.ball {f.v} {f.p.p.p.b} (by decide) {proof(f.p.p.q)})"

SIDE = ("(by intro e x he hx; "
        "have k1 : ∀ n, ¬ mem x (e n) := fun n h => hx (trans _ _ (he n) h); "
        "have k2 : ∀ n, x ≠ e n := fun n h => hx (h ▸ he n); "
        "simp [evalU, upd, k1, k2])")

def absproof(f):
    """AbsF の証明項。Δ0 の部分木は d0、有界量化は ball、それ以外の ∀ は outside（U の外では本体が真）。"""
    if d0(f): return f"(AbsF.d0 {proof(f)})"
    if isinstance(f, Not): return f"(AbsF.neg {absproof(f.p)})"
    if isinstance(f, And): return f"(AbsF.conj {absproof(f.p)} {absproof(f.q)})"
    if is_ball(f): return f"(AbsF.ball {f.v} {f.p.p.p.b} (by decide) {absproof(f.p.p.q)})"
    return f"(AbsF.outside {f.v} {absproof(f.p)} {SIDE})"

def size(f):
    if isinstance(f, Atom): return 1
    if isinstance(f, Not): return 1 + size(f.p)
    if isinstance(f, And): return 1 + size(f.p) + size(f.q)
    return 1 + size(f.p)

PARTS = [("pair", 3, A.pair), ("triple", 4, A.triple), ("trans", 1, A.trans),
         ("ordinal", 1, OR.ordinal), ("func", 3, OR.func), ("bij", 3, OR.bij), ("e_restrict", 2, ST.e_restrict),
         ("empty", 1, A.empty), ("succ_of", 2, A.succ_of), ("is_omega", 1, OR.is_omega)]

def main():
    out = ["import Moon", "namespace Moon", ""]
    rows = []
    for name, k, mk in PARTS:
        ctx = Ctx(start=0); vs = [ctx.fresh() for _ in range(k)]
        f = mk(ctx, *vs)
        ok = d0(f)
        rows.append((name, size(f), ok))
        out.append(f"def f_{name} : Fml := {term(f)}")
        if ok:
            out.append(f"theorem d0_{name} : IsD0 f_{name} := {proof(f)}")
            out.append(f"theorem abs_{name} {{α : Type}} (mem : α → α → Prop) (U : α → Prop)\n"
                       f"    (trans : ∀ x y, U y → mem x y → U x) (e : Nat → α) (he : ∀ n, U (e n)) :\n"
                       f"    evalU mem U f_{name} e ↔ evalU mem (fun _ => True) f_{name} e :=\n"
                       f"  absolute mem U trans d0_{name} e he")
        else:
            out.append(f"theorem absF_{name} {{α : Type}} (mem : α → α → Prop) (U : α → Prop)\n"
                       f"    (trans : ∀ x y, U y → mem x y → U x) : AbsF mem U f_{name} :=\n"
                       f"  {absproof(f)}")
            out.append(f"theorem abs_{name} {{α : Type}} (mem : α → α → Prop) (U : α → Prop)\n"
                       f"    (trans : ∀ x y, U y → mem x y → U x) (e : Nat → α) (he : ∀ n, U (e n)) :\n"
                       f"    evalU mem U f_{name} e ↔ evalU mem (fun _ => True) f_{name} e :=\n"
                       f"  absoluteF mem U trans (absF_{name} mem U trans) e he")
        out.append("")
    out.append("end Moon")
    open("lean/Export.lean", "w", encoding="utf-8").write("\n".join(out))
    for name, n, ok in rows:
        print(f"{name:12s} ノード {n:5d}  {'Δ0' if ok else 'Δ0 ではない（U の外で本体が真になる量化子で AbsF を構成）'}")
    if "--old" in sys.argv:   # 旧版の順序対で同じ構成を試す（失敗することを確かめる用）
        ctx = Ctx(start=0); vs = [ctx.fresh() for _ in range(3)]
        f = A.pair_old(ctx, *vs)
        src = ["import Moon", "namespace Moon", f"def f_pair_old : Fml := {term(f)}",
               "theorem absF_pair_old {α : Type} (mem : α → α → Prop) (U : α → Prop)\n"
               "    (trans : ∀ x y, U y → mem x y → U x) : AbsF mem U f_pair_old :=\n"
               f"  {absproof(f)}", "end Moon"]
        open("lean/OldPair.lean", "w", encoding="utf-8").write("\n".join(src))

if __name__ == "__main__":
    main()
