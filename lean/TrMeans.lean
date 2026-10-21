/-
  書き写しの検証：各部品について、展開した式 full_X の意味が意図した条件（Rstd）と一致すること（mean_full_X）。
  lit を持つ部品については、生成プログラムの出力そのもの lit_X についても（mean_X）。
  （lean_tr_export.py が書き出す。各部品の証明は TrRel.lean の rel_X と、一般的な補題 expand_ok2 による。）
-/
import TrCheck
import TrRel
import TrRelD
import TrRelE
import TrRelF
import TrRelG
import TrRelH
import TrRelI
import TrRelJ
import TrLitA
import TrLitB
import TrLitC
import TrLitD
import TrLitE
import TrLitF
import TrLitG
import TrLitH
import TrLitI
import TrLitJ
namespace Tr
section
variable {α : Type} (mem : α → α → Prop)

theorem bvt_empty : BvOk tbl_empty := by
  intro n k g h
  cases n <;> simp only [tbl_empty, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
theorem bvok_empty : ∀ v, v ∈ bv full_empty → 1 ≤ v := by
  rw [full_empty]; exact bv_expand_ge tbl_empty bvt_empty 1 r_empty chk_empty rge_empty

theorem mean_full_empty (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_empty e ↔ Rstd mem .empty ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_empty n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_empty, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  rw [full_empty, expand_ok3 mem R0 (Rstd mem) tbl_empty htbl bvt_empty r_empty chk_empty e]
  exact rel_empty mem e

theorem bvt_succ : BvOk tbl_succ := by
  intro n k g h
  cases n <;> simp only [tbl_succ, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
theorem bvok_succ : ∀ v, v ∈ bv full_succ → 2 ≤ v := by
  rw [full_succ]; exact bv_expand_ge tbl_succ bvt_succ 2 r_succ chk_succ rge_succ

theorem mean_full_succ (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_succ e ↔ Rstd mem .succ ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_succ n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_succ, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  rw [full_succ, expand_ok3 mem R0 (Rstd mem) tbl_succ htbl bvt_succ r_succ chk_succ e]
  exact rel_succ mem e

theorem bvt_trans : BvOk tbl_trans := by
  intro n k g h
  cases n <;> simp only [tbl_trans, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
theorem bvok_trans : ∀ v, v ∈ bv full_trans → 1 ≤ v := by
  rw [full_trans]; exact bv_expand_ge tbl_trans bvt_trans 1 r_trans chk_trans rge_trans

theorem mean_full_trans (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_trans e ↔ Rstd mem .trans ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_trans n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_trans, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  rw [full_trans, expand_ok3 mem R0 (Rstd mem) tbl_trans htbl bvt_trans r_trans chk_trans e]
  exact rel_trans mem e

theorem bvt_pair : BvOk tbl_pair := by
  intro n k g h
  cases n <;> simp only [tbl_pair, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
theorem bvok_pair : ∀ v, v ∈ bv full_pair → 3 ≤ v := by
  rw [full_pair]; exact bv_expand_ge tbl_pair bvt_pair 3 r_pair chk_pair rge_pair

theorem mean_full_pair (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_pair e ↔ Rstd mem .pair ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_pair n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_pair, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  rw [full_pair, expand_ok3 mem R0 (Rstd mem) tbl_pair htbl bvt_pair r_pair chk_pair e]
  exact rel_pair mem e

theorem bvt_is_one : BvOk tbl_is_one := by
  intro n k g h
  cases n <;> simp only [tbl_is_one, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_is_one : ∀ v, v ∈ bv full_is_one → 1 ≤ v := by
  rw [full_is_one]; exact bv_expand_ge tbl_is_one bvt_is_one 1 r_is_one chk_is_one rge_is_one

theorem mean_full_is_one (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_is_one e ↔ Rstd mem .is_one ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_is_one n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_is_one, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_is_one, expand_ok3 mem R0 (Rstd mem) tbl_is_one htbl bvt_is_one r_is_one chk_is_one e]
  exact rel_is_one mem e

theorem bvt_numeral0 : BvOk tbl_numeral0 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral0, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
theorem bvok_numeral0 : ∀ v, v ∈ bv full_numeral0 → 1 ≤ v := by
  rw [full_numeral0]; exact bv_expand_ge tbl_numeral0 bvt_numeral0 1 r_numeral0 chk_numeral0 rge_numeral0

theorem mean_full_numeral0 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral0 e ↔ Rstd mem .numeral0 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral0 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral0, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  rw [full_numeral0, expand_ok3 mem R0 (Rstd mem) tbl_numeral0 htbl bvt_numeral0 r_numeral0 chk_numeral0 e]
  exact rel_numeral0 mem e

theorem bvt_numeral1 : BvOk tbl_numeral1 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral1, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral1 : ∀ v, v ∈ bv full_numeral1 → 1 ≤ v := by
  rw [full_numeral1]; exact bv_expand_ge tbl_numeral1 bvt_numeral1 1 r_numeral1 chk_numeral1 rge_numeral1

theorem mean_full_numeral1 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral1 e ↔ Rstd mem .numeral1 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral1 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral1, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral1, expand_ok3 mem R0 (Rstd mem) tbl_numeral1 htbl bvt_numeral1 r_numeral1 chk_numeral1 e]
  exact rel_numeral1 mem e

theorem bvt_numeral2 : BvOk tbl_numeral2 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral2 : ∀ v, v ∈ bv full_numeral2 → 1 ≤ v := by
  rw [full_numeral2]; exact bv_expand_ge tbl_numeral2 bvt_numeral2 1 r_numeral2 chk_numeral2 rge_numeral2

theorem mean_full_numeral2 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral2 e ↔ Rstd mem .numeral2 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral2 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral2, expand_ok3 mem R0 (Rstd mem) tbl_numeral2 htbl bvt_numeral2 r_numeral2 chk_numeral2 e]
  exact rel_numeral2 mem e

theorem mean_numeral2 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_numeral2 e ↔ Rstd mem .numeral2 ((List.range 1).map e) := by
  rw [← full_lit_numeral2]; exact mean_full_numeral2 mem R0 e

theorem bvt_numeral3 : BvOk tbl_numeral3 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral3, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral3 : ∀ v, v ∈ bv full_numeral3 → 1 ≤ v := by
  rw [full_numeral3]; exact bv_expand_ge tbl_numeral3 bvt_numeral3 1 r_numeral3 chk_numeral3 rge_numeral3

theorem mean_full_numeral3 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral3 e ↔ Rstd mem .numeral3 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral3 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral3, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral3, expand_ok3 mem R0 (Rstd mem) tbl_numeral3 htbl bvt_numeral3 r_numeral3 chk_numeral3 e]
  exact rel_numeral3 mem e

theorem bvt_numeral4 : BvOk tbl_numeral4 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral4, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral4 : ∀ v, v ∈ bv full_numeral4 → 1 ≤ v := by
  rw [full_numeral4]; exact bv_expand_ge tbl_numeral4 bvt_numeral4 1 r_numeral4 chk_numeral4 rge_numeral4

theorem mean_full_numeral4 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral4 e ↔ Rstd mem .numeral4 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral4 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral4, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral4, expand_ok3 mem R0 (Rstd mem) tbl_numeral4 htbl bvt_numeral4 r_numeral4 chk_numeral4 e]
  exact rel_numeral4 mem e

theorem bvt_numeral5 : BvOk tbl_numeral5 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral5, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral4
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral5 : ∀ v, v ∈ bv full_numeral5 → 1 ≤ v := by
  rw [full_numeral5]; exact bv_expand_ge tbl_numeral5 bvt_numeral5 1 r_numeral5 chk_numeral5 rge_numeral5

theorem mean_full_numeral5 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral5 e ↔ Rstd mem .numeral5 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral5 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral5, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral4 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral5, expand_ok3 mem R0 (Rstd mem) tbl_numeral5 htbl bvt_numeral5 r_numeral5 chk_numeral5 e]
  exact rel_numeral5 mem e

theorem bvt_numeral6 : BvOk tbl_numeral6 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral6, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral5 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral5
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral6 : ∀ v, v ∈ bv full_numeral6 → 1 ≤ v := by
  rw [full_numeral6]; exact bv_expand_ge tbl_numeral6 bvt_numeral6 1 r_numeral6 chk_numeral6 rge_numeral6

theorem mean_full_numeral6 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral6 e ↔ Rstd mem .numeral6 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral6 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral6, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral5 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral5 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral6, expand_ok3 mem R0 (Rstd mem) tbl_numeral6 htbl bvt_numeral6 r_numeral6 chk_numeral6 e]
  exact rel_numeral6 mem e

theorem bvt_numeral7 : BvOk tbl_numeral7 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral7, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral6 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral6
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral7 : ∀ v, v ∈ bv full_numeral7 → 1 ≤ v := by
  rw [full_numeral7]; exact bv_expand_ge tbl_numeral7 bvt_numeral7 1 r_numeral7 chk_numeral7 rge_numeral7

theorem mean_full_numeral7 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral7 e ↔ Rstd mem .numeral7 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral7 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral7, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral6 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral6 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral7, expand_ok3 mem R0 (Rstd mem) tbl_numeral7 htbl bvt_numeral7 r_numeral7 chk_numeral7 e]
  exact rel_numeral7 mem e

theorem bvt_numeral8 : BvOk tbl_numeral8 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral8, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral7 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral7
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral8 : ∀ v, v ∈ bv full_numeral8 → 1 ≤ v := by
  rw [full_numeral8]; exact bv_expand_ge tbl_numeral8 bvt_numeral8 1 r_numeral8 chk_numeral8 rge_numeral8

theorem mean_full_numeral8 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral8 e ↔ Rstd mem .numeral8 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral8 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral8, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral7 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral7 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral8, expand_ok3 mem R0 (Rstd mem) tbl_numeral8 htbl bvt_numeral8 r_numeral8 chk_numeral8 e]
  exact rel_numeral8 mem e

theorem bvt_numeral9 : BvOk tbl_numeral9 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral9, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral8 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral8
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral9 : ∀ v, v ∈ bv full_numeral9 → 1 ≤ v := by
  rw [full_numeral9]; exact bv_expand_ge tbl_numeral9 bvt_numeral9 1 r_numeral9 chk_numeral9 rge_numeral9

theorem mean_full_numeral9 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral9 e ↔ Rstd mem .numeral9 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral9 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral9, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral8 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral8 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral9, expand_ok3 mem R0 (Rstd mem) tbl_numeral9 htbl bvt_numeral9 r_numeral9 chk_numeral9 e]
  exact rel_numeral9 mem e

theorem bvt_nat : BvOk tbl_nat := by
  intro n k g h
  cases n <;> simp only [tbl_nat, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case trans => obtain ⟨rfl, rfl⟩ := h; exact bvok_trans
theorem bvok_nat : ∀ v, v ∈ bv full_nat → 1 ≤ v := by
  rw [full_nat]; exact bv_expand_ge tbl_nat bvt_nat 1 r_nat chk_nat rge_nat

theorem mean_full_nat (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_nat e ↔ Rstd mem .nat ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_nat n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_nat, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case trans => obtain ⟨rfl, rfl⟩ := h; exact mean_full_trans mem R0
  rw [full_nat, expand_ok3 mem R0 (Rstd mem) tbl_nat htbl bvt_nat r_nat chk_nat e]
  exact rel_nat mem e

theorem mean_nat (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_nat e ↔ Rstd mem .nat ((List.range 1).map e) := by
  rw [← full_lit_nat]; exact mean_full_nat mem R0 e

theorem bvt_triple : BvOk tbl_triple := by
  intro n k g h
  cases n <;> simp only [tbl_triple, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_triple : ∀ v, v ∈ bv full_triple → 4 ≤ v := by
  rw [full_triple]; exact bv_expand_ge tbl_triple bvt_triple 4 r_triple chk_triple rge_triple

theorem mean_full_triple (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_triple e ↔ Rstd mem .triple ((List.range 4).map e) := by
  have htbl : ∀ n k g, tbl_triple n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_triple, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_triple, expand_ok3 mem R0 (Rstd mem) tbl_triple htbl bvt_triple r_triple chk_triple e]
  exact rel_triple mem e

theorem bvt_hyper_table : BvOk tbl_hyper_table := by
  intro n k g h
  cases n <;> simp only [tbl_hyper_table, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
theorem bvok_hyper_table : ∀ v, v ∈ bv full_hyper_table → 2 ≤ v := by
  rw [full_hyper_table]; exact bv_expand_ge tbl_hyper_table bvt_hyper_table 2 r_hyper_table chk_hyper_table rge_hyper_table

theorem mean_full_hyper_table (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_hyper_table e ↔ Rstd mem .hyper_table ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_hyper_table n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_hyper_table, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
  rw [full_hyper_table, expand_ok3 mem R0 (Rstd mem) tbl_hyper_table htbl bvt_hyper_table r_hyper_table chk_hyper_table e]
  exact rel_hyper_table mem e

theorem bvt_hyper : BvOk tbl_hyper := by
  intro n k g h
  cases n <;> simp only [tbl_hyper, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case hyper_table => obtain ⟨rfl, rfl⟩ := h; exact bvok_hyper_table
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
theorem bvok_hyper : ∀ v, v ∈ bv full_hyper → 4 ≤ v := by
  rw [full_hyper]; exact bv_expand_ge tbl_hyper bvt_hyper 4 r_hyper chk_hyper rge_hyper

theorem mean_full_hyper (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_hyper e ↔ Rstd mem .hyper ((List.range 4).map e) := by
  have htbl : ∀ n k g, tbl_hyper n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_hyper, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case hyper_table => obtain ⟨rfl, rfl⟩ := h; exact mean_full_hyper_table mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
  rw [full_hyper, expand_ok3 mem R0 (Rstd mem) tbl_hyper htbl bvt_hyper r_hyper chk_hyper e]
  exact rel_hyper mem e

theorem mean_hyper (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_hyper e ↔ Rstd mem .hyper ((List.range 4).map e) := by
  rw [← full_lit_hyper]; exact mean_full_hyper mem R0 e

theorem bvt_add : BvOk tbl_add := by
  intro n k g h
  cases n <;> simp only [tbl_add, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case hyper => obtain ⟨rfl, rfl⟩ := h; exact bvok_hyper
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
theorem bvok_add : ∀ v, v ∈ bv full_add → 3 ≤ v := by
  rw [full_add]; exact bv_expand_ge tbl_add bvt_add 3 r_add chk_add rge_add

theorem mean_full_add (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_add e ↔ Rstd mem .add ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_add n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_add, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case hyper => obtain ⟨rfl, rfl⟩ := h; exact mean_full_hyper mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
  rw [full_add, expand_ok3 mem R0 (Rstd mem) tbl_add htbl bvt_add r_add chk_add e]
  exact rel_add mem e

theorem mean_add (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_add e ↔ Rstd mem .add ((List.range 3).map e) := by
  rw [← full_lit_add]; exact mean_full_add mem R0 e

theorem bvt_mul : BvOk tbl_mul := by
  intro n k g h
  cases n <;> simp only [tbl_mul, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case hyper => obtain ⟨rfl, rfl⟩ := h; exact bvok_hyper
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
theorem bvok_mul : ∀ v, v ∈ bv full_mul → 3 ≤ v := by
  rw [full_mul]; exact bv_expand_ge tbl_mul bvt_mul 3 r_mul chk_mul rge_mul

theorem mean_full_mul (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_mul e ↔ Rstd mem .mul ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_mul n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_mul, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case hyper => obtain ⟨rfl, rfl⟩ := h; exact mean_full_hyper mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
  rw [full_mul, expand_ok3 mem R0 (Rstd mem) tbl_mul htbl bvt_mul r_mul chk_mul e]
  exact rel_mul mem e

theorem mean_mul (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_mul e ↔ Rstd mem .mul ((List.range 3).map e) := by
  rw [← full_lit_mul]; exact mean_full_mul mem R0 e

theorem bvt_exp : BvOk tbl_exp := by
  intro n k g h
  cases n <;> simp only [tbl_exp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case hyper => obtain ⟨rfl, rfl⟩ := h; exact bvok_hyper
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
theorem bvok_exp : ∀ v, v ∈ bv full_exp → 3 ≤ v := by
  rw [full_exp]; exact bv_expand_ge tbl_exp bvt_exp 3 r_exp chk_exp rge_exp

theorem mean_full_exp (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_exp e ↔ Rstd mem .exp ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_exp n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_exp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case hyper => obtain ⟨rfl, rfl⟩ := h; exact mean_full_hyper mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
  rw [full_exp, expand_ok3 mem R0 (Rstd mem) tbl_exp htbl bvt_exp r_exp chk_exp e]
  exact rel_exp mem e

theorem mean_exp (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_exp e ↔ Rstd mem .exp ((List.range 3).map e) := by
  rw [← full_lit_exp]; exact mean_full_exp mem R0 e

theorem bvt_divides : BvOk tbl_divides := by
  intro n k g h
  cases n <;> simp only [tbl_divides, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case mul => obtain ⟨rfl, rfl⟩ := h; exact bvok_mul
theorem bvok_divides : ∀ v, v ∈ bv full_divides → 2 ≤ v := by
  rw [full_divides]; exact bv_expand_ge tbl_divides bvt_divides 2 r_divides chk_divides rge_divides

theorem mean_full_divides (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_divides e ↔ Rstd mem .divides ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_divides n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_divides, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case mul => obtain ⟨rfl, rfl⟩ := h; exact mean_full_mul mem R0
  rw [full_divides, expand_ok3 mem R0 (Rstd mem) tbl_divides htbl bvt_divides r_divides chk_divides e]
  exact rel_divides mem e

theorem mean_divides (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_divides e ↔ Rstd mem .divides ((List.range 2).map e) := by
  rw [← full_lit_divides]; exact mean_full_divides mem R0 e

theorem bvt_prime : BvOk tbl_prime := by
  intro n k g h
  cases n <;> simp only [tbl_prime, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case divides => obtain ⟨rfl, rfl⟩ := h; exact bvok_divides
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case is_one => obtain ⟨rfl, rfl⟩ := h; exact bvok_is_one
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
theorem bvok_prime : ∀ v, v ∈ bv full_prime → 1 ≤ v := by
  rw [full_prime]; exact bv_expand_ge tbl_prime bvt_prime 1 r_prime chk_prime rge_prime

theorem mean_full_prime (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_prime e ↔ Rstd mem .prime ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_prime n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_prime, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case divides => obtain ⟨rfl, rfl⟩ := h; exact mean_full_divides mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case is_one => obtain ⟨rfl, rfl⟩ := h; exact mean_full_is_one mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
  rw [full_prime, expand_ok3 mem R0 (Rstd mem) tbl_prime htbl bvt_prime r_prime chk_prime e]
  exact rel_prime mem e

theorem mean_prime (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_prime e ↔ Rstd mem .prime ((List.range 1).map e) := by
  rw [← full_lit_prime]; exact mean_full_prime mem R0 e

theorem bvt_prime_table : BvOk tbl_prime_table := by
  intro n k g h
  cases n <;> simp only [tbl_prime_table, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case prime => obtain ⟨rfl, rfl⟩ := h; exact bvok_prime
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_prime_table : ∀ v, v ∈ bv full_prime_table → 1 ≤ v := by
  rw [full_prime_table]; exact bv_expand_ge tbl_prime_table bvt_prime_table 1 r_prime_table chk_prime_table rge_prime_table

theorem mean_full_prime_table (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_prime_table e ↔ Rstd mem .prime_table ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_prime_table n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_prime_table, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case prime => obtain ⟨rfl, rfl⟩ := h; exact mean_full_prime mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_prime_table, expand_ok3 mem R0 (Rstd mem) tbl_prime_table htbl bvt_prime_table r_prime_table chk_prime_table e]
  exact rel_prime_table mem e

theorem bvt_nth_prime : BvOk tbl_nth_prime := by
  intro n k g h
  cases n <;> simp only [tbl_nth_prime, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case prime_table => obtain ⟨rfl, rfl⟩ := h; exact bvok_prime_table
theorem bvok_nth_prime : ∀ v, v ∈ bv full_nth_prime → 2 ≤ v := by
  rw [full_nth_prime]; exact bv_expand_ge tbl_nth_prime bvt_nth_prime 2 r_nth_prime chk_nth_prime rge_nth_prime

theorem mean_full_nth_prime (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_nth_prime e ↔ Rstd mem .nth_prime ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_nth_prime n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_nth_prime, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case prime_table => obtain ⟨rfl, rfl⟩ := h; exact mean_full_prime_table mem R0
  rw [full_nth_prime, expand_ok3 mem R0 (Rstd mem) tbl_nth_prime htbl bvt_nth_prime r_nth_prime chk_nth_prime e]
  exact rel_nth_prime mem e

theorem mean_nth_prime (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_nth_prime e ↔ Rstd mem .nth_prime ((List.range 2).map e) := by
  rw [← full_lit_nth_prime]; exact mean_full_nth_prime mem R0 e

theorem bvt_seqfun : BvOk tbl_seqfun := by
  intro n k g h
  cases n <;> simp only [tbl_seqfun, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_seqfun : ∀ v, v ∈ bv full_seqfun → 2 ≤ v := by
  rw [full_seqfun]; exact bv_expand_ge tbl_seqfun bvt_seqfun 2 r_seqfun chk_seqfun rge_seqfun

theorem mean_full_seqfun (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_seqfun e ↔ Rstd mem .seqfun ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_seqfun n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_seqfun, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_seqfun, expand_ok3 mem R0 (Rstd mem) tbl_seqfun htbl bvt_seqfun r_seqfun chk_seqfun e]
  exact rel_seqfun mem e

theorem bvt_prod_table : BvOk tbl_prod_table := by
  intro n k g h
  cases n <;> simp only [tbl_prod_table, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case exp => obtain ⟨rfl, rfl⟩ := h; exact bvok_exp
  case is_one => obtain ⟨rfl, rfl⟩ := h; exact bvok_is_one
  case mul => obtain ⟨rfl, rfl⟩ := h; exact bvok_mul
  case nth_prime => obtain ⟨rfl, rfl⟩ := h; exact bvok_nth_prime
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_prod_table : ∀ v, v ∈ bv full_prod_table → 2 ≤ v := by
  rw [full_prod_table]; exact bv_expand_ge tbl_prod_table bvt_prod_table 2 r_prod_table chk_prod_table rge_prod_table

theorem mean_full_prod_table (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_prod_table e ↔ Rstd mem .prod_table ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_prod_table n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_prod_table, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case exp => obtain ⟨rfl, rfl⟩ := h; exact mean_full_exp mem R0
    case is_one => obtain ⟨rfl, rfl⟩ := h; exact mean_full_is_one mem R0
    case mul => obtain ⟨rfl, rfl⟩ := h; exact mean_full_mul mem R0
    case nth_prime => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nth_prime mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_prod_table, expand_ok3 mem R0 (Rstd mem) tbl_prod_table htbl bvt_prod_table r_prod_table chk_prod_table e]
  exact rel_prod_table mem e

theorem bvt_encode : BvOk tbl_encode := by
  intro n k g h
  cases n <;> simp only [tbl_encode, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case exp => obtain ⟨rfl, rfl⟩ := h; exact bvok_exp
  case mul => obtain ⟨rfl, rfl⟩ := h; exact bvok_mul
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case prod_table => obtain ⟨rfl, rfl⟩ := h; exact bvok_prod_table
  case seqfun => obtain ⟨rfl, rfl⟩ := h; exact bvok_seqfun
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_encode : ∀ v, v ∈ bv full_encode → 2 ≤ v := by
  rw [full_encode]; exact bv_expand_ge tbl_encode bvt_encode 2 r_encode chk_encode rge_encode

theorem mean_full_encode (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_encode e ↔ Rstd mem .encode ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_encode n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_encode, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case exp => obtain ⟨rfl, rfl⟩ := h; exact mean_full_exp mem R0
    case mul => obtain ⟨rfl, rfl⟩ := h; exact mean_full_mul mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case prod_table => obtain ⟨rfl, rfl⟩ := h; exact mean_full_prod_table mem R0
    case seqfun => obtain ⟨rfl, rfl⟩ := h; exact mean_full_seqfun mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_encode, expand_ok3 mem R0 (Rstd mem) tbl_encode htbl bvt_encode r_encode chk_encode e]
  exact rel_encode mem e

theorem mean_encode (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_encode e ↔ Rstd mem .encode ((List.range 2).map e) := by
  rw [← full_lit_encode]; exact mean_full_encode mem R0 e

theorem bvt_tuple4 : BvOk tbl_tuple4 := by
  intro n k g h
  cases n <;> simp only [tbl_tuple4, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral4
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_tuple4 : ∀ v, v ∈ bv full_tuple4 → 1 ≤ v := by
  rw [full_tuple4]; exact bv_expand_ge tbl_tuple4 bvt_tuple4 1 r_tuple4 chk_tuple4 rge_tuple4

theorem mean_full_tuple4 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_tuple4 e ↔ Rstd mem .tuple4 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_tuple4 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_tuple4, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral4 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_tuple4, expand_ok3 mem R0 (Rstd mem) tbl_tuple4 htbl bvt_tuple4 r_tuple4 chk_tuple4 e]
  exact rel_tuple4 mem e

theorem bvt_metacode : BvOk tbl_metacode := by
  intro n k g h
  cases n <;> simp only [tbl_metacode, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case encode => obtain ⟨rfl, rfl⟩ := h; exact bvok_encode
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_tuple4
theorem bvok_metacode : ∀ v, v ∈ bv full_metacode → 2 ≤ v := by
  rw [full_metacode]; exact bv_expand_ge tbl_metacode bvt_metacode 2 r_metacode chk_metacode rge_metacode

theorem mean_full_metacode (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_metacode e ↔ Rstd mem .metacode ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_metacode n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_metacode, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case encode => obtain ⟨rfl, rfl⟩ := h; exact mean_full_encode mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_tuple4 mem R0
  rw [full_metacode, expand_ok3 mem R0 (Rstd mem) tbl_metacode htbl bvt_metacode r_metacode chk_metacode e]
  exact rel_metacode mem e

theorem mean_metacode (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_metacode e ↔ Rstd mem .metacode ((List.range 2).map e) := by
  rw [← full_lit_metacode]; exact mean_full_metacode mem R0 e

theorem bvt_punct0 : BvOk tbl_punct0 := by
  intro n k g h
  cases n <;> simp only [tbl_punct0, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_punct0 : ∀ v, v ∈ bv full_punct0 → 1 ≤ v := by
  rw [full_punct0]; exact bv_expand_ge tbl_punct0 bvt_punct0 1 r_punct0 chk_punct0 rge_punct0

theorem mean_full_punct0 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_punct0 e ↔ Rstd mem .punct0 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_punct0 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_punct0, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_punct0, expand_ok3 mem R0 (Rstd mem) tbl_punct0 htbl bvt_punct0 r_punct0 chk_punct0 e]
  exact rel_punct0 mem e

theorem bvt_punct1 : BvOk tbl_punct1 := by
  intro n k g h
  cases n <;> simp only [tbl_punct1, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_punct1 : ∀ v, v ∈ bv full_punct1 → 1 ≤ v := by
  rw [full_punct1]; exact bv_expand_ge tbl_punct1 bvt_punct1 1 r_punct1 chk_punct1 rge_punct1

theorem mean_full_punct1 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_punct1 e ↔ Rstd mem .punct1 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_punct1 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_punct1, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_punct1, expand_ok3 mem R0 (Rstd mem) tbl_punct1 htbl bvt_punct1 r_punct1 chk_punct1 e]
  exact rel_punct1 mem e

theorem bvt_punct2 : BvOk tbl_punct2 := by
  intro n k g h
  cases n <;> simp only [tbl_punct2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_punct2 : ∀ v, v ∈ bv full_punct2 → 1 ≤ v := by
  rw [full_punct2]; exact bv_expand_ge tbl_punct2 bvt_punct2 1 r_punct2 chk_punct2 rge_punct2

theorem mean_full_punct2 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_punct2 e ↔ Rstd mem .punct2 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_punct2 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_punct2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_punct2, expand_ok3 mem R0 (Rstd mem) tbl_punct2 htbl bvt_punct2 r_punct2 chk_punct2 e]
  exact rel_punct2 mem e

theorem bvt_punct3 : BvOk tbl_punct3 := by
  intro n k g h
  cases n <;> simp only [tbl_punct3, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_punct3 : ∀ v, v ∈ bv full_punct3 → 1 ≤ v := by
  rw [full_punct3]; exact bv_expand_ge tbl_punct3 bvt_punct3 1 r_punct3 chk_punct3 rge_punct3

theorem mean_full_punct3 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_punct3 e ↔ Rstd mem .punct3 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_punct3 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_punct3, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_punct3, expand_ok3 mem R0 (Rstd mem) tbl_punct3 htbl bvt_punct3 r_punct3 chk_punct3 e]
  exact rel_punct3 mem e

theorem bvt_punct4 : BvOk tbl_punct4 := by
  intro n k g h
  cases n <;> simp only [tbl_punct4, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral4
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_punct4 : ∀ v, v ∈ bv full_punct4 → 1 ≤ v := by
  rw [full_punct4]; exact bv_expand_ge tbl_punct4 bvt_punct4 1 r_punct4 chk_punct4 rge_punct4

theorem mean_full_punct4 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_punct4 e ↔ Rstd mem .punct4 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_punct4 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_punct4, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral4 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_punct4, expand_ok3 mem R0 (Rstd mem) tbl_punct4 htbl bvt_punct4 r_punct4 chk_punct4 e]
  exact rel_punct4 mem e

theorem bvt_punct5 : BvOk tbl_punct5 := by
  intro n k g h
  cases n <;> simp only [tbl_punct5, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case numeral5 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral5
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_punct5 : ∀ v, v ∈ bv full_punct5 → 1 ≤ v := by
  rw [full_punct5]; exact bv_expand_ge tbl_punct5 bvt_punct5 1 r_punct5 chk_punct5 rge_punct5

theorem mean_full_punct5 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_punct5 e ↔ Rstd mem .punct5 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_punct5 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_punct5, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case numeral5 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral5 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_punct5, expand_ok3 mem R0 (Rstd mem) tbl_punct5 htbl bvt_punct5 r_punct5 chk_punct5 e]
  exact rel_punct5 mem e

theorem bvt_symvar : BvOk tbl_symvar := by
  intro n k g h
  cases n <;> simp only [tbl_symvar, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case numeral7 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral7
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_symvar : ∀ v, v ∈ bv full_symvar → 1 ≤ v := by
  rw [full_symvar]; exact bv_expand_ge tbl_symvar bvt_symvar 1 r_symvar chk_symvar rge_symvar

theorem mean_full_symvar (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_symvar e ↔ Rstd mem .symvar ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_symvar n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_symvar, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case numeral7 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral7 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_symvar, expand_ok3 mem R0 (Rstd mem) tbl_symvar htbl bvt_symvar r_symvar chk_symvar e]
  exact rel_symvar mem e

theorem bvt_symconst : BvOk tbl_symconst := by
  intro n k g h
  cases n <;> simp only [tbl_symconst, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case numeral6 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral6
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_symconst : ∀ v, v ∈ bv full_symconst → 1 ≤ v := by
  rw [full_symconst]; exact bv_expand_ge tbl_symconst bvt_symconst 1 r_symconst chk_symconst rge_symconst

theorem mean_full_symconst (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_symconst e ↔ Rstd mem .symconst ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_symconst n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_symconst, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case numeral6 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral6 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_symconst, expand_ok3 mem R0 (Rstd mem) tbl_symconst htbl bvt_symconst r_symconst chk_symconst e]
  exact rel_symconst mem e

theorem bvt_symfunc : BvOk tbl_symfunc := by
  intro n k g h
  cases n <;> simp only [tbl_symfunc, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral4
  case numeral8 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral8
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_symfunc : ∀ v, v ∈ bv full_symfunc → 1 ≤ v := by
  rw [full_symfunc]; exact bv_expand_ge tbl_symfunc bvt_symfunc 1 r_symfunc chk_symfunc rge_symfunc

theorem mean_full_symfunc (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_symfunc e ↔ Rstd mem .symfunc ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_symfunc n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_symfunc, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral4 mem R0
    case numeral8 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral8 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_symfunc, expand_ok3 mem R0 (Rstd mem) tbl_symfunc htbl bvt_symfunc r_symfunc chk_symfunc e]
  exact rel_symfunc mem e

theorem bvt_symrel : BvOk tbl_symrel := by
  intro n k g h
  cases n <;> simp only [tbl_symrel, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral6 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral6
  case numeral9 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral9
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_symrel : ∀ v, v ∈ bv full_symrel → 1 ≤ v := by
  rw [full_symrel]; exact bv_expand_ge tbl_symrel bvt_symrel 1 r_symrel chk_symrel rge_symrel

theorem mean_full_symrel (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_symrel e ↔ Rstd mem .symrel ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_symrel n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_symrel, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral6 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral6 mem R0
    case numeral9 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral9 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_symrel, expand_ok3 mem R0 (Rstd mem) tbl_symrel htbl bvt_symrel r_symrel chk_symrel e]
  exact rel_symrel mem e

theorem bvt_symelem : BvOk tbl_symelem := by
  intro n k g h
  cases n <;> simp only [tbl_symelem, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case numeral5 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral5
  case numeral9 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral9
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_symelem : ∀ v, v ∈ bv full_symelem → 1 ≤ v := by
  rw [full_symelem]; exact bv_expand_ge tbl_symelem bvt_symelem 1 r_symelem chk_symelem rge_symelem

theorem mean_full_symelem (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_symelem e ↔ Rstd mem .symelem ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_symelem n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_symelem, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case numeral5 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral5 mem R0
    case numeral9 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral9 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_symelem, expand_ok3 mem R0 (Rstd mem) tbl_symelem htbl bvt_symelem r_symelem chk_symelem e]
  exact rel_symelem mem e

theorem bvt_symtheta : BvOk tbl_symtheta := by
  intro n k g h
  cases n <;> simp only [tbl_symtheta, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case numeral8 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral8
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_symtheta : ∀ v, v ∈ bv full_symtheta → 1 ≤ v := by
  rw [full_symtheta]; exact bv_expand_ge tbl_symtheta bvt_symtheta 1 r_symtheta chk_symtheta rge_symtheta

theorem mean_full_symtheta (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_symtheta e ↔ Rstd mem .symtheta ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_symtheta n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_symtheta, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case numeral8 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral8 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_symtheta, expand_ok3 mem R0 (Rstd mem) tbl_symtheta htbl bvt_symtheta r_symtheta chk_symtheta e]
  exact rel_symtheta mem e

theorem bvt_plus2 : BvOk tbl_plus2 := by
  intro n k g h
  cases n <;> simp only [tbl_plus2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_plus2 : ∀ v, v ∈ bv full_plus2 → 2 ≤ v := by
  rw [full_plus2]; exact bv_expand_ge tbl_plus2 bvt_plus2 2 r_plus2 chk_plus2 rge_plus2

theorem mean_full_plus2 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_plus2 e ↔ Rstd mem .plus2 ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_plus2 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_plus2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_plus2, expand_ok3 mem R0 (Rstd mem) tbl_plus2 htbl bvt_plus2 r_plus2 chk_plus2 e]
  exact rel_plus2 mem e

theorem bvt_certificate : BvOk tbl_certificate := by
  intro n k g h
  cases n <;> simp only [tbl_certificate, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case plus2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_plus2
  case punct0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct0
  case punct1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct1
  case punct2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct2
  case punct3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct3
  case punct4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct4
  case punct5 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct5
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case symconst => obtain ⟨rfl, rfl⟩ := h; exact bvok_symconst
  case symelem => obtain ⟨rfl, rfl⟩ := h; exact bvok_symelem
  case symfunc => obtain ⟨rfl, rfl⟩ := h; exact bvok_symfunc
  case symrel => obtain ⟨rfl, rfl⟩ := h; exact bvok_symrel
  case symvar => obtain ⟨rfl, rfl⟩ := h; exact bvok_symvar
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
theorem bvok_certificate : ∀ v, v ∈ bv full_certificate → 4 ≤ v := by
  rw [full_certificate]; exact bv_expand_ge tbl_certificate bvt_certificate 4 r_certificate chk_certificate rge_certificate

theorem mean_full_certificate (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_certificate e ↔ Rstd mem .certificate ((List.range 4).map e) := by
  have htbl : ∀ n k g, tbl_certificate n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_certificate, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case plus2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_plus2 mem R0
    case punct0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct0 mem R0
    case punct1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct1 mem R0
    case punct2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct2 mem R0
    case punct3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct3 mem R0
    case punct4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct4 mem R0
    case punct5 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct5 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case symconst => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symconst mem R0
    case symelem => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symelem mem R0
    case symfunc => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symfunc mem R0
    case symrel => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symrel mem R0
    case symvar => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symvar mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
  rw [full_certificate, expand_ok3 mem R0 (Rstd mem) tbl_certificate htbl bvt_certificate r_certificate chk_certificate e]
  exact rel_certificate mem e

theorem bvt_formula : BvOk tbl_formula := by
  intro n k g h
  cases n <;> simp only [tbl_formula, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case certificate => obtain ⟨rfl, rfl⟩ := h; exact bvok_certificate
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
  case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_tuple4
theorem bvok_formula : ∀ v, v ∈ bv full_formula → 1 ≤ v := by
  rw [full_formula]; exact bv_expand_ge tbl_formula bvt_formula 1 r_formula chk_formula rge_formula

theorem mean_full_formula (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_formula e ↔ Rstd mem .formula ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_formula n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_formula, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case certificate => obtain ⟨rfl, rfl⟩ := h; exact mean_full_certificate mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
    case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_tuple4 mem R0
  rw [full_formula, expand_ok3 mem R0 (Rstd mem) tbl_formula htbl bvt_formula r_formula chk_formula e]
  exact rel_formula mem e

theorem mean_formula (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_formula e ↔ Rstd mem .formula ((List.range 1).map e) := by
  rw [← full_lit_formula]; exact mean_full_formula mem R0 e

theorem bvt_formula_minus : BvOk tbl_formula_minus := by
  intro n k g h
  cases n <;> simp only [tbl_formula_minus, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case certificate => obtain ⟨rfl, rfl⟩ := h; exact bvok_certificate
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case symtheta => obtain ⟨rfl, rfl⟩ := h; exact bvok_symtheta
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
  case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_tuple4
theorem bvok_formula_minus : ∀ v, v ∈ bv full_formula_minus → 1 ≤ v := by
  rw [full_formula_minus]; exact bv_expand_ge tbl_formula_minus bvt_formula_minus 1 r_formula_minus chk_formula_minus rge_formula_minus

theorem mean_full_formula_minus (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_formula_minus e ↔ Rstd mem .formula_minus ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_formula_minus n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_formula_minus, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case certificate => obtain ⟨rfl, rfl⟩ := h; exact mean_full_certificate mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case symtheta => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symtheta mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
    case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_tuple4 mem R0
  rw [full_formula_minus, expand_ok3 mem R0 (Rstd mem) tbl_formula_minus htbl bvt_formula_minus r_formula_minus chk_formula_minus e]
  exact rel_formula_minus mem e

theorem mean_formula_minus (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 lit_formula_minus e ↔ Rstd mem .formula_minus ((List.range 1).map e) := by
  rw [← full_lit_formula_minus]; exact mean_full_formula_minus mem R0 e

theorem bvt_assign : BvOk tbl_assign := by
  intro n k g h
  cases n <;> simp only [tbl_assign, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_assign : ∀ v, v ∈ bv full_assign → 3 ≤ v := by
  rw [full_assign]; exact bv_expand_ge tbl_assign bvt_assign 3 r_assign chk_assign rge_assign

theorem mean_full_assign (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_assign e ↔ Rstd mem .assign ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_assign n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_assign, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_assign, expand_ok3 mem R0 (Rstd mem) tbl_assign htbl bvt_assign r_assign chk_assign e]
  exact rel_assign mem e

theorem bvt_update : BvOk tbl_update := by
  intro n k g h
  cases n <;> simp only [tbl_update, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case assign => obtain ⟨rfl, rfl⟩ := h; exact bvok_assign
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_update : ∀ v, v ∈ bv full_update → 6 ≤ v := by
  rw [full_update]; exact bv_expand_ge tbl_update bvt_update 6 r_update chk_update rge_update

theorem mean_full_update (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_update e ↔ Rstd mem .update ((List.range 6).map e) := by
  have htbl : ∀ n k g, tbl_update n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_update, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case assign => obtain ⟨rfl, rfl⟩ := h; exact mean_full_assign mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_update, expand_ok3 mem R0 (Rstd mem) tbl_update htbl bvt_update r_update chk_update e]
  exact rel_update mem e

theorem bvt_in_s : BvOk tbl_in_s := by
  intro n k g h
  cases n <;> simp only [tbl_in_s, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_in_s : ∀ v, v ∈ bv full_in_s → 4 ≤ v := by
  rw [full_in_s]; exact bv_expand_ge tbl_in_s bvt_in_s 4 r_in_s chk_in_s rge_in_s

theorem mean_full_in_s (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_in_s e ↔ Rstd mem .in_s ((List.range 4).map e) := by
  have htbl : ∀ n k g, tbl_in_s n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_in_s, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_in_s, expand_ok3 mem R0 (Rstd mem) tbl_in_s htbl bvt_in_s r_in_s chk_in_s e]
  exact rel_in_s mem e

theorem bvt_in_pair : BvOk tbl_in_pair := by
  intro n k g h
  cases n <;> simp only [tbl_in_pair, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_in_pair : ∀ v, v ∈ bv full_in_pair → 3 ≤ v := by
  rw [full_in_pair]; exact bv_expand_ge tbl_in_pair bvt_in_pair 3 r_in_pair chk_in_pair rge_in_pair

theorem mean_full_in_pair (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_in_pair e ↔ Rstd mem .in_pair ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_in_pair n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_in_pair, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_in_pair, expand_ok3 mem R0 (Rstd mem) tbl_in_pair htbl bvt_in_pair r_in_pair chk_in_pair e]
  exact rel_in_pair mem e

theorem bvt_in_triple : BvOk tbl_in_triple := by
  intro n k g h
  cases n <;> simp only [tbl_in_triple, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
theorem bvok_in_triple : ∀ v, v ∈ bv full_in_triple → 4 ≤ v := by
  rw [full_in_triple]; exact bv_expand_ge tbl_in_triple bvt_in_triple 4 r_in_triple chk_in_triple rge_in_triple

theorem mean_full_in_triple (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_in_triple e ↔ Rstd mem .in_triple ((List.range 4).map e) := by
  have htbl : ∀ n k g, tbl_in_triple n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_in_triple, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
  rw [full_in_triple, expand_ok3 mem R0 (Rstd mem) tbl_in_triple htbl bvt_in_triple r_in_triple chk_in_triple e]
  exact rel_in_triple mem e

theorem bvt_cons : BvOk tbl_cons := by
  intro n k g h
  cases n <;> simp only [tbl_cons, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case in_pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_in_pair
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_cons : ∀ v, v ∈ bv full_cons → 3 ≤ v := by
  rw [full_cons]; exact bv_expand_ge tbl_cons bvt_cons 3 r_cons chk_cons rge_cons

theorem mean_full_cons (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_cons e ↔ Rstd mem .cons ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_cons n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_cons, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case in_pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_in_pair mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_cons, expand_ok3 mem R0 (Rstd mem) tbl_cons htbl bvt_cons r_cons chk_cons e]
  exact rel_cons mem e

theorem bvt_term_clause : BvOk tbl_term_clause := by
  intro n k g h
  cases n <;> simp only [tbl_term_clause, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case in_pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_in_pair
  case in_triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_in_triple
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case plus2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_plus2
  case punct4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct4
  case punct5 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct5
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case symconst => obtain ⟨rfl, rfl⟩ := h; exact bvok_symconst
  case symfunc => obtain ⟨rfl, rfl⟩ := h; exact bvok_symfunc
  case symvar => obtain ⟨rfl, rfl⟩ := h; exact bvok_symvar
theorem bvok_term_clause : ∀ v, v ∈ bv full_term_clause → 8 ≤ v := by
  rw [full_term_clause]; exact bv_expand_ge tbl_term_clause bvt_term_clause 8 r_term_clause chk_term_clause rge_term_clause

theorem mean_full_term_clause (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_term_clause e ↔ Rstd mem .term_clause ((List.range 8).map e) := by
  have htbl : ∀ n k g, tbl_term_clause n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_term_clause, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case in_pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_in_pair mem R0
    case in_triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_in_triple mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case plus2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_plus2 mem R0
    case punct4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct4 mem R0
    case punct5 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct5 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case symconst => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symconst mem R0
    case symfunc => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symfunc mem R0
    case symvar => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symvar mem R0
  rw [full_term_clause, expand_ok3 mem R0 (Rstd mem) tbl_term_clause htbl bvt_term_clause r_term_clause chk_term_clause e]
  exact rel_term_clause mem e

theorem bvt_list_clause : BvOk tbl_list_clause := by
  intro n k g h
  cases n <;> simp only [tbl_list_clause, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case cons => obtain ⟨rfl, rfl⟩ := h; exact bvok_cons
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case plus2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_plus2
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
theorem bvok_list_clause : ∀ v, v ∈ bv full_list_clause → 8 ≤ v := by
  rw [full_list_clause]; exact bv_expand_ge tbl_list_clause bvt_list_clause 8 r_list_clause chk_list_clause rge_list_clause

theorem mean_full_list_clause (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_list_clause e ↔ Rstd mem .list_clause ((List.range 8).map e) := by
  have htbl : ∀ n k g, tbl_list_clause n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_list_clause, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case cons => obtain ⟨rfl, rfl⟩ := h; exact mean_full_cons mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case plus2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_plus2 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
  rw [full_list_clause, expand_ok3 mem R0 (Rstd mem) tbl_list_clause htbl bvt_list_clause r_list_clause chk_list_clause e]
  exact rel_list_clause mem e

theorem bvt_formula_clause : BvOk tbl_formula_clause := by
  intro n k g h
  cases n <;> simp only [tbl_formula_clause, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case in_pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_in_pair
  case in_s => obtain ⟨rfl, rfl⟩ := h; exact bvok_in_s
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case plus2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_plus2
  case punct0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct0
  case punct1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct1
  case punct2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct2
  case punct3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct3
  case punct4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct4
  case punct5 => obtain ⟨rfl, rfl⟩ := h; exact bvok_punct5
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case symelem => obtain ⟨rfl, rfl⟩ := h; exact bvok_symelem
  case symrel => obtain ⟨rfl, rfl⟩ := h; exact bvok_symrel
  case symvar => obtain ⟨rfl, rfl⟩ := h; exact bvok_symvar
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
  case update => obtain ⟨rfl, rfl⟩ := h; exact bvok_update
theorem bvok_formula_clause : ∀ v, v ∈ bv full_formula_clause → 13 ≤ v := by
  rw [full_formula_clause]; exact bv_expand_ge tbl_formula_clause bvt_formula_clause 13 r_formula_clause chk_formula_clause rge_formula_clause

theorem mean_full_formula_clause (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_formula_clause e ↔ Rstd mem .formula_clause ((List.range 13).map e) := by
  have htbl : ∀ n k g, tbl_formula_clause n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_formula_clause, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case in_pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_in_pair mem R0
    case in_s => obtain ⟨rfl, rfl⟩ := h; exact mean_full_in_s mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case plus2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_plus2 mem R0
    case punct0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct0 mem R0
    case punct1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct1 mem R0
    case punct2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct2 mem R0
    case punct3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct3 mem R0
    case punct4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct4 mem R0
    case punct5 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_punct5 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case symelem => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symelem mem R0
    case symrel => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symrel mem R0
    case symvar => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symvar mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
    case update => obtain ⟨rfl, rfl⟩ := h; exact mean_full_update mem R0
  rw [full_formula_clause, expand_ok3 mem R0 (Rstd mem) tbl_formula_clause htbl bvt_formula_clause r_formula_clause chk_formula_clause e]
  exact rel_formula_clause mem e

theorem bvt_tv_ok : BvOk tbl_tv_ok := by
  intro n k g h
  cases n <;> simp only [tbl_tv_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case assign => obtain ⟨rfl, rfl⟩ := h; exact bvok_assign
  case list_clause => obtain ⟨rfl, rfl⟩ := h; exact bvok_list_clause
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case plus2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_plus2
  case term_clause => obtain ⟨rfl, rfl⟩ := h; exact bvok_term_clause
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
theorem bvok_tv_ok : ∀ v, v ∈ bv full_tv_ok → 8 ≤ v := by
  rw [full_tv_ok]; exact bv_expand_ge tbl_tv_ok bvt_tv_ok 8 r_tv_ok chk_tv_ok rge_tv_ok

theorem mean_full_tv_ok (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_tv_ok e ↔ Rstd mem .tv_ok ((List.range 8).map e) := by
  have htbl : ∀ n k g, tbl_tv_ok n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_tv_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case assign => obtain ⟨rfl, rfl⟩ := h; exact mean_full_assign mem R0
    case list_clause => obtain ⟨rfl, rfl⟩ := h; exact mean_full_list_clause mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case plus2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_plus2 mem R0
    case term_clause => obtain ⟨rfl, rfl⟩ := h; exact mean_full_term_clause mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
  rw [full_tv_ok, expand_ok3 mem R0 (Rstd mem) tbl_tv_ok htbl bvt_tv_ok r_tv_ok chk_tv_ok e]
  exact rel_tv_ok mem e

theorem bvt_s_ok : BvOk tbl_s_ok := by
  intro n k g h
  cases n <;> simp only [tbl_s_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case assign => obtain ⟨rfl, rfl⟩ := h; exact bvok_assign
  case formula_clause => obtain ⟨rfl, rfl⟩ := h; exact bvok_formula_clause
  case in_s => obtain ⟨rfl, rfl⟩ := h; exact bvok_in_s
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
theorem bvok_s_ok : ∀ v, v ∈ bv full_s_ok → 10 ≤ v := by
  rw [full_s_ok]; exact bv_expand_ge tbl_s_ok bvt_s_ok 10 r_s_ok chk_s_ok rge_s_ok

theorem mean_full_s_ok (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_s_ok e ↔ Rstd mem .s_ok ((List.range 10).map e) := by
  have htbl : ∀ n k g, tbl_s_ok n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_s_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case assign => obtain ⟨rfl, rfl⟩ := h; exact mean_full_assign mem R0
    case formula_clause => obtain ⟨rfl, rfl⟩ := h; exact mean_full_formula_clause mem R0
    case in_s => obtain ⟨rfl, rfl⟩ := h; exact mean_full_in_s mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
  rw [full_s_ok, expand_ok3 mem R0 (Rstd mem) tbl_s_ok htbl bvt_s_ok r_s_ok chk_s_ok e]
  exact rel_s_ok mem e

theorem bvt_varset : BvOk tbl_varset := by
  intro n k g h
  cases n <;> simp only [tbl_varset, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case symvar => obtain ⟨rfl, rfl⟩ := h; exact bvok_symvar
theorem bvok_varset : ∀ v, v ∈ bv full_varset → 3 ≤ v := by
  rw [full_varset]; exact bv_expand_ge tbl_varset bvt_varset 3 r_varset chk_varset rge_varset

theorem mean_full_varset (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_varset e ↔ Rstd mem .varset ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_varset n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_varset, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case symvar => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symvar mem R0
  rw [full_varset, expand_ok3 mem R0 (Rstd mem) tbl_varset htbl bvt_varset r_varset chk_varset e]
  exact rel_varset mem e

theorem bvt_sat : BvOk tbl_sat := by
  intro n k g h
  cases n <;> simp only [tbl_sat, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case assign => obtain ⟨rfl, rfl⟩ := h; exact bvok_assign
  case certificate => obtain ⟨rfl, rfl⟩ := h; exact bvok_certificate
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case in_s => obtain ⟨rfl, rfl⟩ := h; exact bvok_in_s
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case s_ok => obtain ⟨rfl, rfl⟩ := h; exact bvok_s_ok
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
  case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_tuple4
  case tv_ok => obtain ⟨rfl, rfl⟩ := h; exact bvok_tv_ok
  case varset => obtain ⟨rfl, rfl⟩ := h; exact bvok_varset
theorem bvok_sat : ∀ v, v ∈ bv full_sat → 7 ≤ v := by
  rw [full_sat]; exact bv_expand_ge tbl_sat bvt_sat 7 r_sat chk_sat rge_sat

theorem mean_full_sat (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_sat e ↔ Rstd mem .sat ((List.range 7).map e) := by
  have htbl : ∀ n k g, tbl_sat n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_sat, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case assign => obtain ⟨rfl, rfl⟩ := h; exact mean_full_assign mem R0
    case certificate => obtain ⟨rfl, rfl⟩ := h; exact mean_full_certificate mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case in_s => obtain ⟨rfl, rfl⟩ := h; exact mean_full_in_s mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case s_ok => obtain ⟨rfl, rfl⟩ := h; exact mean_full_s_ok mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
    case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_tuple4 mem R0
    case tv_ok => obtain ⟨rfl, rfl⟩ := h; exact mean_full_tv_ok mem R0
    case varset => obtain ⟨rfl, rfl⟩ := h; exact mean_full_varset mem R0
  rw [full_sat, expand_ok3 mem R0 (Rstd mem) tbl_sat htbl bvt_sat r_sat chk_sat e]
  exact rel_sat mem e

theorem bvt_sat_ext : BvOk tbl_sat_ext := by
  intro n k g h
  cases n <;> simp only [tbl_sat_ext, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case assign => obtain ⟨rfl, rfl⟩ := h; exact bvok_assign
  case certificate => obtain ⟨rfl, rfl⟩ := h; exact bvok_certificate
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case in_s => obtain ⟨rfl, rfl⟩ := h; exact bvok_in_s
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case s_ok => obtain ⟨rfl, rfl⟩ := h; exact bvok_s_ok
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
  case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_tuple4
  case tv_ok => obtain ⟨rfl, rfl⟩ := h; exact bvok_tv_ok
  case varset => obtain ⟨rfl, rfl⟩ := h; exact bvok_varset
theorem bvok_sat_ext : ∀ v, v ∈ bv full_sat_ext → 7 ≤ v := by
  rw [full_sat_ext]; exact bv_expand_ge tbl_sat_ext bvt_sat_ext 7 r_sat_ext chk_sat_ext rge_sat_ext

theorem mean_full_sat_ext (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_sat_ext e ↔ Rstd mem .sat_ext ((List.range 7).map e) := by
  have htbl : ∀ n k g, tbl_sat_ext n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_sat_ext, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case assign => obtain ⟨rfl, rfl⟩ := h; exact mean_full_assign mem R0
    case certificate => obtain ⟨rfl, rfl⟩ := h; exact mean_full_certificate mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case in_s => obtain ⟨rfl, rfl⟩ := h; exact mean_full_in_s mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case s_ok => obtain ⟨rfl, rfl⟩ := h; exact mean_full_s_ok mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
    case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_tuple4 mem R0
    case tv_ok => obtain ⟨rfl, rfl⟩ := h; exact mean_full_tv_ok mem R0
    case varset => obtain ⟨rfl, rfl⟩ := h; exact mean_full_varset mem R0
  rw [full_sat_ext, expand_ok3 mem R0 (Rstd mem) tbl_sat_ext htbl bvt_sat_ext r_sat_ext chk_sat_ext e]
  exact rel_sat_ext mem e

theorem bvt_assign_w : BvOk tbl_assign_w := by
  intro n k g h
  cases n <;> simp only [tbl_assign_w, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_assign_w : ∀ v, v ∈ bv full_assign_w → 3 ≤ v := by
  rw [full_assign_w]; exact bv_expand_ge tbl_assign_w bvt_assign_w 3 r_assign_w chk_assign_w rge_assign_w

theorem mean_full_assign_w (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_assign_w e ↔ Rstd mem .assign_w ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_assign_w n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_assign_w, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_assign_w, expand_ok3 mem R0 (Rstd mem) tbl_assign_w htbl bvt_assign_w r_assign_w chk_assign_w e]
  exact rel_assign_w mem e

theorem bvt_update_w : BvOk tbl_update_w := by
  intro n k g h
  cases n <;> simp only [tbl_update_w, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case assign_w => obtain ⟨rfl, rfl⟩ := h; exact bvok_assign_w
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_update_w : ∀ v, v ∈ bv full_update_w → 6 ≤ v := by
  rw [full_update_w]; exact bv_expand_ge tbl_update_w bvt_update_w 6 r_update_w chk_update_w rge_update_w

theorem mean_full_update_w (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_update_w e ↔ Rstd mem .update_w ((List.range 6).map e) := by
  have htbl : ∀ n k g, tbl_update_w n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_update_w, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case assign_w => obtain ⟨rfl, rfl⟩ := h; exact mean_full_assign_w mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_update_w, expand_ok3 mem R0 (Rstd mem) tbl_update_w htbl bvt_update_w r_update_w chk_update_w e]
  exact rel_update_w mem e

theorem bvt_is_definition : BvOk tbl_is_definition := by
  intro n k g h
  cases n <;> simp only [tbl_is_definition, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case assign_w => obtain ⟨rfl, rfl⟩ := h; exact bvok_assign_w
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case sat_ext => obtain ⟨rfl, rfl⟩ := h; exact bvok_sat_ext
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case symvar => obtain ⟨rfl, rfl⟩ := h; exact bvok_symvar
  case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_tuple4
  case update_w => obtain ⟨rfl, rfl⟩ := h; exact bvok_update_w
theorem bvok_is_definition : ∀ v, v ∈ bv full_is_definition → 6 ≤ v := by
  rw [full_is_definition]; exact bv_expand_ge tbl_is_definition bvt_is_definition 6 r_is_definition chk_is_definition rge_is_definition

theorem mean_full_is_definition (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_is_definition e ↔ Rstd mem .is_definition ((List.range 6).map e) := by
  have htbl : ∀ n k g, tbl_is_definition n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_is_definition, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case assign_w => obtain ⟨rfl, rfl⟩ := h; exact mean_full_assign_w mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case sat_ext => obtain ⟨rfl, rfl⟩ := h; exact mean_full_sat_ext mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case symvar => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symvar mem R0
    case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_tuple4 mem R0
    case update_w => obtain ⟨rfl, rfl⟩ := h; exact mean_full_update_w mem R0
  rw [full_is_definition, expand_ok3 mem R0 (Rstd mem) tbl_is_definition htbl bvt_is_definition r_is_definition chk_is_definition e]
  exact rel_is_definition mem e

theorem bvt_param_true : BvOk tbl_param_true := by
  intro n k g h
  cases n <;> simp only [tbl_param_true, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case assign_w => obtain ⟨rfl, rfl⟩ := h; exact bvok_assign_w
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case sat_ext => obtain ⟨rfl, rfl⟩ := h; exact bvok_sat_ext
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case symvar => obtain ⟨rfl, rfl⟩ := h; exact bvok_symvar
  case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_tuple4
theorem bvok_param_true : ∀ v, v ∈ bv full_param_true → 7 ≤ v := by
  rw [full_param_true]; exact bv_expand_ge tbl_param_true bvt_param_true 7 r_param_true chk_param_true rge_param_true

theorem mean_full_param_true (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_param_true e ↔ Rstd mem .param_true ((List.range 7).map e) := by
  have htbl : ∀ n k g, tbl_param_true n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_param_true, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case assign_w => obtain ⟨rfl, rfl⟩ := h; exact mean_full_assign_w mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case sat_ext => obtain ⟨rfl, rfl⟩ := h; exact mean_full_sat_ext mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case symvar => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symvar mem R0
    case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_tuple4 mem R0
  rw [full_param_true, expand_ok3 mem R0 (Rstd mem) tbl_param_true htbl bvt_param_true r_param_true chk_param_true e]
  exact rel_param_true mem e

theorem bvt_definable_in : BvOk tbl_definable_in := by
  intro n k g h
  cases n <;> simp only [tbl_definable_in, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case is_definition => obtain ⟨rfl, rfl⟩ := h; exact bvok_is_definition
  case param_true => obtain ⟨rfl, rfl⟩ := h; exact bvok_param_true
theorem bvok_definable_in : ∀ v, v ∈ bv full_definable_in → 7 ≤ v := by
  rw [full_definable_in]; exact bv_expand_ge tbl_definable_in bvt_definable_in 7 r_definable_in chk_definable_in rge_definable_in

theorem mean_full_definable_in (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_definable_in e ↔ Rstd mem .definable_in ((List.range 7).map e) := by
  have htbl : ∀ n k g, tbl_definable_in n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_definable_in, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case is_definition => obtain ⟨rfl, rfl⟩ := h; exact mean_full_is_definition mem R0
    case param_true => obtain ⟨rfl, rfl⟩ := h; exact mean_full_param_true mem R0
  rw [full_definable_in, expand_ok3 mem R0 (Rstd mem) tbl_definable_in htbl bvt_definable_in r_definable_in chk_definable_in e]
  exact rel_definable_in mem e

theorem bvt_ordinal : BvOk tbl_ordinal := by
  intro n k g h
  cases n <;> simp only [tbl_ordinal, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
theorem bvok_ordinal : ∀ v, v ∈ bv full_ordinal → 1 ≤ v := by
  rw [full_ordinal]; exact bv_expand_ge tbl_ordinal bvt_ordinal 1 r_ordinal chk_ordinal rge_ordinal

theorem mean_full_ordinal (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_ordinal e ↔ Rstd mem .ordinal ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_ordinal n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_ordinal, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  rw [full_ordinal, expand_ok3 mem R0 (Rstd mem) tbl_ordinal htbl bvt_ordinal r_ordinal chk_ordinal e]
  exact rel_ordinal mem e

theorem bvt_e_restrict : BvOk tbl_e_restrict := by
  intro n k g h
  cases n <;> simp only [tbl_e_restrict, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_e_restrict : ∀ v, v ∈ bv full_e_restrict → 2 ≤ v := by
  rw [full_e_restrict]; exact bv_expand_ge tbl_e_restrict bvt_e_restrict 2 r_e_restrict chk_e_restrict rge_e_restrict

theorem mean_full_e_restrict (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_e_restrict e ↔ Rstd mem .e_restrict ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_e_restrict n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_e_restrict, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_e_restrict, expand_ok3 mem R0 (Rstd mem) tbl_e_restrict htbl bvt_e_restrict r_e_restrict chk_e_restrict e]
  exact rel_e_restrict mem e

theorem bvt_func_on : BvOk tbl_func_on := by
  intro n k g h
  cases n <;> simp only [tbl_func_on, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_func_on : ∀ v, v ∈ bv full_func_on → 3 ≤ v := by
  rw [full_func_on]; exact bv_expand_ge tbl_func_on bvt_func_on 3 r_func_on chk_func_on rge_func_on

theorem mean_full_func_on (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_func_on e ↔ Rstd mem .func_on ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_func_on n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_func_on, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_func_on, expand_ok3 mem R0 (Rstd mem) tbl_func_on htbl bvt_func_on r_func_on chk_func_on e]
  exact rel_func_on mem e

theorem bvt_in_pair_l : BvOk tbl_in_pair_l := by
  intro n k g h
  cases n <;> simp only [tbl_in_pair_l, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_in_pair_l : ∀ v, v ∈ bv full_in_pair_l → 3 ≤ v := by
  rw [full_in_pair_l]; exact bv_expand_ge tbl_in_pair_l bvt_in_pair_l 3 r_in_pair_l chk_in_pair_l rge_in_pair_l

theorem mean_full_in_pair_l (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_in_pair_l e ↔ Rstd mem .in_pair_l ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_in_pair_l n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_in_pair_l, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_in_pair_l, expand_ok3 mem R0 (Rstd mem) tbl_in_pair_l htbl bvt_in_pair_l r_in_pair_l chk_in_pair_l e]
  exact rel_in_pair_l mem e

theorem bvt_pure : BvOk tbl_pure := by
  intro n k g h
  cases n <;> simp only [tbl_pure, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case symconst => obtain ⟨rfl, rfl⟩ := h; exact bvok_symconst
  case symfunc => obtain ⟨rfl, rfl⟩ := h; exact bvok_symfunc
  case symrel => obtain ⟨rfl, rfl⟩ := h; exact bvok_symrel
theorem bvok_pure : ∀ v, v ∈ bv full_pure → 2 ≤ v := by
  rw [full_pure]; exact bv_expand_ge tbl_pure bvt_pure 2 r_pure chk_pure rge_pure

theorem mean_full_pure (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_pure e ↔ Rstd mem .pure ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_pure n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_pure, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case symconst => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symconst mem R0
    case symfunc => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symfunc mem R0
    case symrel => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symrel mem R0
  rw [full_pure, expand_ok3 mem R0 (Rstd mem) tbl_pure htbl bvt_pure r_pure chk_pure e]
  exact rel_pure mem e

theorem bvt_def_code : BvOk tbl_def_code := by
  intro n k g h
  cases n <;> simp only [tbl_def_code, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case formula_minus => obtain ⟨rfl, rfl⟩ := h; exact bvok_formula_minus
  case metacode => obtain ⟨rfl, rfl⟩ := h; exact bvok_metacode
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case pure => obtain ⟨rfl, rfl⟩ := h; exact bvok_pure
theorem bvok_def_code : ∀ v, v ∈ bv full_def_code → 1 ≤ v := by
  rw [full_def_code]; exact bv_expand_ge tbl_def_code bvt_def_code 1 r_def_code chk_def_code rge_def_code

theorem mean_full_def_code (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_def_code e ↔ Rstd mem .def_code ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_def_code n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_def_code, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case formula_minus => obtain ⟨rfl, rfl⟩ := h; exact mean_full_formula_minus mem R0
    case metacode => obtain ⟨rfl, rfl⟩ := h; exact mean_full_metacode mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case pure => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pure mem R0
  rw [full_def_code, expand_ok3 mem R0 (Rstd mem) tbl_def_code htbl bvt_def_code r_def_code chk_def_code e]
  exact rel_def_code mem e

theorem bvt_defines : BvOk tbl_defines := by
  intro n k g h
  cases n <;> simp only [tbl_defines, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case e_restrict => obtain ⟨rfl, rfl⟩ := h; exact bvok_e_restrict
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case formula_minus => obtain ⟨rfl, rfl⟩ := h; exact bvok_formula_minus
  case func_on => obtain ⟨rfl, rfl⟩ := h; exact bvok_func_on
  case metacode => obtain ⟨rfl, rfl⟩ := h; exact bvok_metacode
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case pure => obtain ⟨rfl, rfl⟩ := h; exact bvok_pure
  case sat_ext => obtain ⟨rfl, rfl⟩ := h; exact bvok_sat_ext
  case symvar => obtain ⟨rfl, rfl⟩ := h; exact bvok_symvar
theorem bvok_defines : ∀ v, v ∈ bv full_defines → 4 ≤ v := by
  rw [full_defines]; exact bv_expand_ge tbl_defines bvt_defines 4 r_defines chk_defines rge_defines

theorem mean_full_defines (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_defines e ↔ Rstd mem .defines ((List.range 4).map e) := by
  have htbl : ∀ n k g, tbl_defines n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_defines, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case e_restrict => obtain ⟨rfl, rfl⟩ := h; exact mean_full_e_restrict mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case formula_minus => obtain ⟨rfl, rfl⟩ := h; exact mean_full_formula_minus mem R0
    case func_on => obtain ⟨rfl, rfl⟩ := h; exact mean_full_func_on mem R0
    case metacode => obtain ⟨rfl, rfl⟩ := h; exact mean_full_metacode mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case pure => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pure mem R0
    case sat_ext => obtain ⟨rfl, rfl⟩ := h; exact mean_full_sat_ext mem R0
    case symvar => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symvar mem R0
  rw [full_defines, expand_ok3 mem R0 (Rstd mem) tbl_defines htbl bvt_defines r_defines chk_defines e]
  exact rel_defines mem e

theorem bvt_lex_less : BvOk tbl_lex_less := by
  intro n k g h
  cases n <;> simp only [tbl_lex_less, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case in_pair_l => obtain ⟨rfl, rfl⟩ := h; exact bvok_in_pair_l
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_lex_less : ∀ v, v ∈ bv full_lex_less → 3 ≤ v := by
  rw [full_lex_less]; exact bv_expand_ge tbl_lex_less bvt_lex_less 3 r_lex_less chk_lex_less rge_lex_less

theorem mean_full_lex_less (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_lex_less e ↔ Rstd mem .lex_less ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_lex_less n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_lex_less, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case in_pair_l => obtain ⟨rfl, rfl⟩ := h; exact mean_full_in_pair_l mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_lex_less, expand_ok3 mem R0 (Rstd mem) tbl_lex_less htbl bvt_lex_less r_lex_less chk_lex_less e]
  exact rel_lex_less mem e

theorem bvt_def_less : BvOk tbl_def_less := by
  intro n k g h
  cases n <;> simp only [tbl_def_less, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case lex_less => obtain ⟨rfl, rfl⟩ := h; exact bvok_lex_less
theorem bvok_def_less : ∀ v, v ∈ bv full_def_less → 5 ≤ v := by
  rw [full_def_less]; exact bv_expand_ge tbl_def_less bvt_def_less 5 r_def_less chk_def_less rge_def_less

theorem mean_full_def_less (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_def_less e ↔ Rstd mem .def_less ((List.range 5).map e) := by
  have htbl : ∀ n k g, tbl_def_less n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_def_less, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case lex_less => obtain ⟨rfl, rfl⟩ := h; exact mean_full_lex_less mem R0
  rw [full_def_less, expand_ok3 mem R0 (Rstd mem) tbl_def_less htbl bvt_def_less r_def_less chk_def_less e]
  exact rel_def_less mem e

theorem bvt_def_table : BvOk tbl_def_table := by
  intro n k g h
  cases n <;> simp only [tbl_def_table, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case def_code => obtain ⟨rfl, rfl⟩ := h; exact bvok_def_code
  case defines => obtain ⟨rfl, rfl⟩ := h; exact bvok_defines
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case triple => obtain ⟨rfl, rfl⟩ := h; exact bvok_triple
theorem bvok_def_table : ∀ v, v ∈ bv full_def_table → 2 ≤ v := by
  rw [full_def_table]; exact bv_expand_ge tbl_def_table bvt_def_table 2 r_def_table chk_def_table rge_def_table

theorem mean_full_def_table (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_def_table e ↔ Rstd mem .def_table ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_def_table n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_def_table, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case def_code => obtain ⟨rfl, rfl⟩ := h; exact mean_full_def_code mem R0
    case defines => obtain ⟨rfl, rfl⟩ := h; exact mean_full_defines mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case triple => obtain ⟨rfl, rfl⟩ := h; exact mean_full_triple mem R0
  rw [full_def_table, expand_ok3 mem R0 (Rstd mem) tbl_def_table htbl bvt_def_table r_def_table chk_def_table e]
  exact rel_def_table mem e

theorem bvt_new_less : BvOk tbl_new_less := by
  intro n k g h
  cases n <;> simp only [tbl_new_less, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case def_less => obtain ⟨rfl, rfl⟩ := h; exact bvok_def_less
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_new_less : ∀ v, v ∈ bv full_new_less → 4 ≤ v := by
  rw [full_new_less]; exact bv_expand_ge tbl_new_less bvt_new_less 4 r_new_less chk_new_less rge_new_less

theorem mean_full_new_less (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_new_less e ↔ Rstd mem .new_less ((List.range 4).map e) := by
  have htbl : ∀ n k g, tbl_new_less n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_new_less, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case def_less => obtain ⟨rfl, rfl⟩ := h; exact mean_full_def_less mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_new_less, expand_ok3 mem R0 (Rstd mem) tbl_new_less htbl bvt_new_less r_new_less chk_new_less e]
  exact rel_new_less mem e

theorem bvt_step : BvOk tbl_step := by
  intro n k g h
  cases n <;> simp only [tbl_step, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case def_table => obtain ⟨rfl, rfl⟩ := h; exact bvok_def_table
  case in_pair_l => obtain ⟨rfl, rfl⟩ := h; exact bvok_in_pair_l
  case new_less => obtain ⟨rfl, rfl⟩ := h; exact bvok_new_less
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_step : ∀ v, v ∈ bv full_step → 4 ≤ v := by
  rw [full_step]; exact bv_expand_ge tbl_step bvt_step 4 r_step chk_step rge_step

theorem mean_full_step (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_step e ↔ Rstd mem .step ((List.range 4).map e) := by
  have htbl : ∀ n k g, tbl_step n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_step, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case def_table => obtain ⟨rfl, rfl⟩ := h; exact mean_full_def_table mem R0
    case in_pair_l => obtain ⟨rfl, rfl⟩ := h; exact mean_full_in_pair_l mem R0
    case new_less => obtain ⟨rfl, rfl⟩ := h; exact mean_full_new_less mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_step, expand_ok3 mem R0 (Rstd mem) tbl_step htbl bvt_step r_step chk_step e]
  exact rel_step mem e

theorem bvt_l_order : BvOk tbl_l_order := by
  intro n k g h
  cases n <;> simp only [tbl_l_order, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case ordinal => obtain ⟨rfl, rfl⟩ := h; exact bvok_ordinal
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case step => obtain ⟨rfl, rfl⟩ := h; exact bvok_step
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_l_order : ∀ v, v ∈ bv full_l_order → 3 ≤ v := by
  rw [full_l_order]; exact bv_expand_ge tbl_l_order bvt_l_order 3 r_l_order chk_l_order rge_l_order

theorem mean_full_l_order (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_l_order e ↔ Rstd mem .l_order ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_l_order n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_l_order, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case ordinal => obtain ⟨rfl, rfl⟩ := h; exact mean_full_ordinal mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case step => obtain ⟨rfl, rfl⟩ := h; exact mean_full_step mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_l_order, expand_ok3 mem R0 (Rstd mem) tbl_l_order htbl bvt_l_order r_l_order chk_l_order e]
  exact rel_l_order mem e

theorem bvt_formula_code_minus : BvOk tbl_formula_code_minus := by
  intro n k g h
  cases n <;> simp only [tbl_formula_code_minus, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case formula_minus => obtain ⟨rfl, rfl⟩ := h; exact bvok_formula_minus
  case metacode => obtain ⟨rfl, rfl⟩ := h; exact bvok_metacode
theorem bvok_formula_code_minus : ∀ v, v ∈ bv full_formula_code_minus → 1 ≤ v := by
  rw [full_formula_code_minus]; exact bv_expand_ge tbl_formula_code_minus bvt_formula_code_minus 1 r_formula_code_minus chk_formula_code_minus rge_formula_code_minus

theorem mean_full_formula_code_minus (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_formula_code_minus e ↔ Rstd mem .formula_code_minus ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_formula_code_minus n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_formula_code_minus, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case formula_minus => obtain ⟨rfl, rfl⟩ := h; exact mean_full_formula_minus mem R0
    case metacode => obtain ⟨rfl, rfl⟩ := h; exact mean_full_metacode mem R0
  rw [full_formula_code_minus, expand_ok3 mem R0 (Rstd mem) tbl_formula_code_minus htbl bvt_formula_code_minus r_formula_code_minus chk_formula_code_minus e]
  exact rel_formula_code_minus mem e

theorem bvt_theta_value : BvOk tbl_theta_value := by
  intro n k g h
  cases n <;> simp only [tbl_theta_value, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case numeral8 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral8
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_theta_value : ∀ v, v ∈ bv full_theta_value → 3 ≤ v := by
  rw [full_theta_value]; exact bv_expand_ge tbl_theta_value bvt_theta_value 3 r_theta_value chk_theta_value rge_theta_value

theorem mean_full_theta_value (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_theta_value e ↔ Rstd mem .theta_value ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_theta_value n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_theta_value, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case numeral8 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral8 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_theta_value, expand_ok3 mem R0 (Rstd mem) tbl_theta_value htbl bvt_theta_value r_theta_value chk_theta_value e]
  exact rel_theta_value mem e

theorem bvt_least_good : BvOk tbl_least_good := by
  intro n k g h
  cases n <;> simp only [tbl_least_good, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case func_on => obtain ⟨rfl, rfl⟩ := h; exact bvok_func_on
  case in_pair_l => obtain ⟨rfl, rfl⟩ := h; exact bvok_in_pair_l
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case sat => obtain ⟨rfl, rfl⟩ := h; exact bvok_sat
  case symvar => obtain ⟨rfl, rfl⟩ := h; exact bvok_symvar
theorem bvok_least_good : ∀ v, v ∈ bv full_least_good → 8 ≤ v := by
  rw [full_least_good]; exact bv_expand_ge tbl_least_good bvt_least_good 8 r_least_good chk_least_good rge_least_good

theorem mean_full_least_good (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_least_good e ↔ Rstd mem .least_good ((List.range 8).map e) := by
  have htbl : ∀ n k g, tbl_least_good n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_least_good, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case func_on => obtain ⟨rfl, rfl⟩ := h; exact mean_full_func_on mem R0
    case in_pair_l => obtain ⟨rfl, rfl⟩ := h; exact mean_full_in_pair_l mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case sat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_sat mem R0
    case symvar => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symvar mem R0
  rw [full_least_good, expand_ok3 mem R0 (Rstd mem) tbl_least_good htbl bvt_least_good r_least_good chk_least_good e]
  exact rel_least_good mem e

theorem bvt_theta_l : BvOk tbl_theta_l := by
  intro n k g h
  cases n <;> simp only [tbl_theta_l, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case formula_code_minus => obtain ⟨rfl, rfl⟩ := h; exact bvok_formula_code_minus
  case formula_minus => obtain ⟨rfl, rfl⟩ := h; exact bvok_formula_minus
  case least_good => obtain ⟨rfl, rfl⟩ := h; exact bvok_least_good
  case metacode => obtain ⟨rfl, rfl⟩ := h; exact bvok_metacode
  case theta_value => obtain ⟨rfl, rfl⟩ := h; exact bvok_theta_value
theorem bvok_theta_l : ∀ v, v ∈ bv full_theta_l → 6 ≤ v := by
  rw [full_theta_l]; exact bv_expand_ge tbl_theta_l bvt_theta_l 6 r_theta_l chk_theta_l rge_theta_l

theorem mean_full_theta_l (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_theta_l e ↔ Rstd mem .theta_l ((List.range 6).map e) := by
  have htbl : ∀ n k g, tbl_theta_l n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_theta_l, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case formula_code_minus => obtain ⟨rfl, rfl⟩ := h; exact mean_full_formula_code_minus mem R0
    case formula_minus => obtain ⟨rfl, rfl⟩ := h; exact mean_full_formula_minus mem R0
    case least_good => obtain ⟨rfl, rfl⟩ := h; exact mean_full_least_good mem R0
    case metacode => obtain ⟨rfl, rfl⟩ := h; exact mean_full_metacode mem R0
    case theta_value => obtain ⟨rfl, rfl⟩ := h; exact mean_full_theta_value mem R0
  rw [full_theta_l, expand_ok3 mem R0 (Rstd mem) tbl_theta_l htbl bvt_theta_l r_theta_l chk_theta_l e]
  exact rel_theta_l mem e

theorem bvt_numeral10 : BvOk tbl_numeral10 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral10, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral9 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral9
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral10 : ∀ v, v ∈ bv full_numeral10 → 1 ≤ v := by
  rw [full_numeral10]; exact bv_expand_ge tbl_numeral10 bvt_numeral10 1 r_numeral10 chk_numeral10 rge_numeral10

theorem mean_full_numeral10 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral10 e ↔ Rstd mem .numeral10 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral10 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral10, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral9 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral9 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral10, expand_ok3 mem R0 (Rstd mem) tbl_numeral10 htbl bvt_numeral10 r_numeral10 chk_numeral10 e]
  exact rel_numeral10 mem e

theorem bvt_numeral11 : BvOk tbl_numeral11 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral11, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral10 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral10
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral11 : ∀ v, v ∈ bv full_numeral11 → 1 ≤ v := by
  rw [full_numeral11]; exact bv_expand_ge tbl_numeral11 bvt_numeral11 1 r_numeral11 chk_numeral11 rge_numeral11

theorem mean_full_numeral11 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral11 e ↔ Rstd mem .numeral11 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral11 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral11, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral10 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral10 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral11, expand_ok3 mem R0 (Rstd mem) tbl_numeral11 htbl bvt_numeral11 r_numeral11 chk_numeral11 e]
  exact rel_numeral11 mem e

theorem bvt_numeral12 : BvOk tbl_numeral12 := by
  intro n k g h
  cases n <;> simp only [tbl_numeral12, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral11 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral11
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_numeral12 : ∀ v, v ∈ bv full_numeral12 → 1 ≤ v := by
  rw [full_numeral12]; exact bv_expand_ge tbl_numeral12 bvt_numeral12 1 r_numeral12 chk_numeral12 rge_numeral12

theorem mean_full_numeral12 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_numeral12 e ↔ Rstd mem .numeral12 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_numeral12 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_numeral12, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral11 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral11 mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_numeral12, expand_ok3 mem R0 (Rstd mem) tbl_numeral12 htbl bvt_numeral12 r_numeral12 chk_numeral12 e]
  exact rel_numeral12 mem e

theorem bvt_dec : BvOk tbl_dec := by
  intro n k g h
  cases n <;> simp only [tbl_dec, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case divides => obtain ⟨rfl, rfl⟩ := h; exact bvok_divides
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case exp => obtain ⟨rfl, rfl⟩ := h; exact bvok_exp
  case mul => obtain ⟨rfl, rfl⟩ := h; exact bvok_mul
  case prime => obtain ⟨rfl, rfl⟩ := h; exact bvok_prime
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_dec : ∀ v, v ∈ bv full_dec → 3 ≤ v := by
  rw [full_dec]; exact bv_expand_ge tbl_dec bvt_dec 3 r_dec chk_dec rge_dec

theorem mean_full_dec (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_dec e ↔ Rstd mem .dec ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_dec n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_dec, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case divides => obtain ⟨rfl, rfl⟩ := h; exact mean_full_divides mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case exp => obtain ⟨rfl, rfl⟩ := h; exact mean_full_exp mem R0
    case mul => obtain ⟨rfl, rfl⟩ := h; exact mean_full_mul mem R0
    case prime => obtain ⟨rfl, rfl⟩ := h; exact mean_full_prime mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_dec, expand_ok3 mem R0 (Rstd mem) tbl_dec htbl bvt_dec r_dec chk_dec e]
  exact rel_dec mem e

theorem bvt_row_shape0 : BvOk tbl_row_shape0 := by
  intro n k g h
  cases n <;> simp only [tbl_row_shape0, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral4
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_row_shape0 : ∀ v, v ∈ bv full_row_shape0 → 1 ≤ v := by
  rw [full_row_shape0]; exact bv_expand_ge tbl_row_shape0 bvt_row_shape0 1 r_row_shape0 chk_row_shape0 rge_row_shape0

theorem mean_full_row_shape0 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_row_shape0 e ↔ Rstd mem .row_shape0 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_row_shape0 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_row_shape0, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral4 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_row_shape0, expand_ok3 mem R0 (Rstd mem) tbl_row_shape0 htbl bvt_row_shape0 r_row_shape0 chk_row_shape0 e]
  exact rel_row_shape0 mem e

theorem bvt_row_shape1 : BvOk tbl_row_shape1 := by
  intro n k g h
  cases n <;> simp only [tbl_row_shape1, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral4
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_row_shape1 : ∀ v, v ∈ bv full_row_shape1 → 1 ≤ v := by
  rw [full_row_shape1]; exact bv_expand_ge tbl_row_shape1 bvt_row_shape1 1 r_row_shape1 chk_row_shape1 rge_row_shape1

theorem mean_full_row_shape1 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_row_shape1 e ↔ Rstd mem .row_shape1 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_row_shape1 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_row_shape1, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral4 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_row_shape1, expand_ok3 mem R0 (Rstd mem) tbl_row_shape1 htbl bvt_row_shape1 r_row_shape1 chk_row_shape1 e]
  exact rel_row_shape1 mem e

theorem bvt_table_ok : BvOk tbl_table_ok := by
  intro n k g h
  cases n <;> simp only [tbl_table_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case dec => obtain ⟨rfl, rfl⟩ := h; exact bvok_dec
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case row_shape0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_row_shape0
  case row_shape1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_row_shape1
theorem bvok_table_ok : ∀ v, v ∈ bv full_table_ok → 1 ≤ v := by
  rw [full_table_ok]; exact bv_expand_ge tbl_table_ok bvt_table_ok 1 r_table_ok chk_table_ok rge_table_ok

theorem mean_full_table_ok (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_table_ok e ↔ Rstd mem .table_ok ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_table_ok n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_table_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case dec => obtain ⟨rfl, rfl⟩ := h; exact mean_full_dec mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case row_shape0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_row_shape0 mem R0
    case row_shape1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_row_shape1 mem R0
  rw [full_table_ok, expand_ok3 mem R0 (Rstd mem) tbl_table_ok htbl bvt_table_ok r_table_ok chk_table_ok e]
  exact rel_table_ok mem e

theorem bvt_cnf_cmp : BvOk tbl_cnf_cmp := by
  intro n k g h
  cases n <;> simp only [tbl_cnf_cmp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case row_shape1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_row_shape1
  case table_ok => obtain ⟨rfl, rfl⟩ := h; exact bvok_table_ok
theorem bvok_cnf_cmp : ∀ v, v ∈ bv full_cnf_cmp → 3 ≤ v := by
  rw [full_cnf_cmp]; exact bv_expand_ge tbl_cnf_cmp bvt_cnf_cmp 3 r_cnf_cmp chk_cnf_cmp rge_cnf_cmp

theorem mean_full_cnf_cmp (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_cnf_cmp e ↔ Rstd mem .cnf_cmp ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_cnf_cmp n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_cnf_cmp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case row_shape1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_row_shape1 mem R0
    case table_ok => obtain ⟨rfl, rfl⟩ := h; exact mean_full_table_ok mem R0
  rw [full_cnf_cmp, expand_ok3 mem R0 (Rstd mem) tbl_cnf_cmp htbl bvt_cnf_cmp r_cnf_cmp chk_cnf_cmp e]
  exact rel_cnf_cmp mem e

theorem bvt_cnf_lt : BvOk tbl_cnf_lt := by
  intro n k g h
  cases n <;> simp only [tbl_cnf_lt, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case cnf_cmp => obtain ⟨rfl, rfl⟩ := h; exact bvok_cnf_cmp
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
theorem bvok_cnf_lt : ∀ v, v ∈ bv full_cnf_lt → 2 ≤ v := by
  rw [full_cnf_lt]; exact bv_expand_ge tbl_cnf_lt bvt_cnf_lt 2 r_cnf_lt chk_cnf_lt rge_cnf_lt

theorem mean_full_cnf_lt (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_cnf_lt e ↔ Rstd mem .cnf_lt ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_cnf_lt n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_cnf_lt, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case cnf_cmp => obtain ⟨rfl, rfl⟩ := h; exact mean_full_cnf_cmp mem R0
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
  rw [full_cnf_lt, expand_ok3 mem R0 (Rstd mem) tbl_cnf_lt htbl bvt_cnf_lt r_cnf_lt chk_cnf_lt e]
  exact rel_cnf_lt mem e

theorem bvt_omega : BvOk tbl_omega := by
  intro n k g h
  cases n <;> simp only [tbl_omega, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case ordinal => obtain ⟨rfl, rfl⟩ := h; exact bvok_ordinal
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_omega : ∀ v, v ∈ bv full_omega → 1 ≤ v := by
  rw [full_omega]; exact bv_expand_ge tbl_omega bvt_omega 1 r_omega chk_omega rge_omega

theorem mean_full_omega (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_omega e ↔ Rstd mem .omega ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_omega n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_omega, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case ordinal => obtain ⟨rfl, rfl⟩ := h; exact mean_full_ordinal mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_omega, expand_ok3 mem R0 (Rstd mem) tbl_omega htbl bvt_omega r_omega chk_omega e]
  exact rel_omega mem e

theorem bvt_func : BvOk tbl_func := by
  intro n k g h
  cases n <;> simp only [tbl_func, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_func : ∀ v, v ∈ bv full_func → 3 ≤ v := by
  rw [full_func]; exact bv_expand_ge tbl_func bvt_func 3 r_func chk_func rge_func

theorem mean_full_func (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_func e ↔ Rstd mem .func ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_func n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_func, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_func, expand_ok3 mem R0 (Rstd mem) tbl_func htbl bvt_func r_func chk_func e]
  exact rel_func mem e

theorem bvt_bij : BvOk tbl_bij := by
  intro n k g h
  cases n <;> simp only [tbl_bij, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case func => obtain ⟨rfl, rfl⟩ := h; exact bvok_func
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_bij : ∀ v, v ∈ bv full_bij → 3 ≤ v := by
  rw [full_bij]; exact bv_expand_ge tbl_bij bvt_bij 3 r_bij chk_bij rge_bij

theorem mean_full_bij (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_bij e ↔ Rstd mem .bij ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_bij n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_bij, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case func => obtain ⟨rfl, rfl⟩ := h; exact mean_full_func mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_bij, expand_ok3 mem R0 (Rstd mem) tbl_bij htbl bvt_bij r_bij chk_bij e]
  exact rel_bij mem e

theorem bvt_regular : BvOk tbl_regular := by
  intro n k g h
  cases n <;> simp only [tbl_regular, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case func => obtain ⟨rfl, rfl⟩ := h; exact bvok_func
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_regular : ∀ v, v ∈ bv full_regular → 1 ≤ v := by
  rw [full_regular]; exact bv_expand_ge tbl_regular bvt_regular 1 r_regular chk_regular rge_regular

theorem mean_full_regular (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_regular e ↔ Rstd mem .regular ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_regular n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_regular, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case func => obtain ⟨rfl, rfl⟩ := h; exact mean_full_func mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_regular, expand_ok3 mem R0 (Rstd mem) tbl_regular htbl bvt_regular r_regular chk_regular e]
  exact rel_regular mem e

theorem bvt_power_of : BvOk tbl_power_of := by
  intro n k g h
  cases n <;> simp only [tbl_power_of, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
theorem bvok_power_of : ∀ v, v ∈ bv full_power_of → 2 ≤ v := by
  rw [full_power_of]; exact bv_expand_ge tbl_power_of bvt_power_of 2 r_power_of chk_power_of rge_power_of

theorem mean_full_power_of (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_power_of e ↔ Rstd mem .power_of ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_power_of n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_power_of, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  rw [full_power_of, expand_ok3 mem R0 (Rstd mem) tbl_power_of htbl bvt_power_of r_power_of chk_power_of e]
  exact rel_power_of mem e

theorem bvt_strong_limit : BvOk tbl_strong_limit := by
  intro n k g h
  cases n <;> simp only [tbl_strong_limit, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case bij => obtain ⟨rfl, rfl⟩ := h; exact bvok_bij
  case power_of => obtain ⟨rfl, rfl⟩ := h; exact bvok_power_of
theorem bvok_strong_limit : ∀ v, v ∈ bv full_strong_limit → 1 ≤ v := by
  rw [full_strong_limit]; exact bv_expand_ge tbl_strong_limit bvt_strong_limit 1 r_strong_limit chk_strong_limit rge_strong_limit

theorem mean_full_strong_limit (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_strong_limit e ↔ Rstd mem .strong_limit ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_strong_limit n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_strong_limit, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case bij => obtain ⟨rfl, rfl⟩ := h; exact mean_full_bij mem R0
    case power_of => obtain ⟨rfl, rfl⟩ := h; exact mean_full_power_of mem R0
  rw [full_strong_limit, expand_ok3 mem R0 (Rstd mem) tbl_strong_limit htbl bvt_strong_limit r_strong_limit chk_strong_limit e]
  exact rel_strong_limit mem e

theorem bvt_inaccessible : BvOk tbl_inaccessible := by
  intro n k g h
  cases n <;> simp only [tbl_inaccessible, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case omega => obtain ⟨rfl, rfl⟩ := h; exact bvok_omega
  case ordinal => obtain ⟨rfl, rfl⟩ := h; exact bvok_ordinal
  case regular => obtain ⟨rfl, rfl⟩ := h; exact bvok_regular
  case strong_limit => obtain ⟨rfl, rfl⟩ := h; exact bvok_strong_limit
theorem bvok_inaccessible : ∀ v, v ∈ bv full_inaccessible → 1 ≤ v := by
  rw [full_inaccessible]; exact bv_expand_ge tbl_inaccessible bvt_inaccessible 1 r_inaccessible chk_inaccessible rge_inaccessible

theorem mean_full_inaccessible (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_inaccessible e ↔ Rstd mem .inaccessible ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_inaccessible n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_inaccessible, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case omega => obtain ⟨rfl, rfl⟩ := h; exact mean_full_omega mem R0
    case ordinal => obtain ⟨rfl, rfl⟩ := h; exact mean_full_ordinal mem R0
    case regular => obtain ⟨rfl, rfl⟩ := h; exact mean_full_regular mem R0
    case strong_limit => obtain ⟨rfl, rfl⟩ := h; exact mean_full_strong_limit mem R0
  rw [full_inaccessible, expand_ok3 mem R0 (Rstd mem) tbl_inaccessible htbl bvt_inaccessible r_inaccessible chk_inaccessible e]
  exact rel_inaccessible mem e

theorem bvt_o_ok : BvOk tbl_o_ok := by
  intro n k g h
  cases n <;> simp only [tbl_o_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case cnf_lt => obtain ⟨rfl, rfl⟩ := h; exact bvok_cnf_lt
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_o_ok : ∀ v, v ∈ bv full_o_ok → 2 ≤ v := by
  rw [full_o_ok]; exact bv_expand_ge tbl_o_ok bvt_o_ok 2 r_o_ok chk_o_ok rge_o_ok

theorem mean_full_o_ok (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_o_ok e ↔ Rstd mem .o_ok ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_o_ok n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_o_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case cnf_lt => obtain ⟨rfl, rfl⟩ := h; exact mean_full_cnf_lt mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_o_ok, expand_ok3 mem R0 (Rstd mem) tbl_o_ok htbl bvt_o_ok r_o_ok chk_o_ok e]
  exact rel_o_ok mem e

theorem bvt_ord_of : BvOk tbl_ord_of := by
  intro n k g h
  cases n <;> simp only [tbl_ord_of, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case o_ok => obtain ⟨rfl, rfl⟩ := h; exact bvok_o_ok
  case omega => obtain ⟨rfl, rfl⟩ := h; exact bvok_omega
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_ord_of : ∀ v, v ∈ bv full_ord_of → 2 ≤ v := by
  rw [full_ord_of]; exact bv_expand_ge tbl_ord_of bvt_ord_of 2 r_ord_of chk_ord_of rge_ord_of

theorem mean_full_ord_of (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_ord_of e ↔ Rstd mem .ord_of ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_ord_of n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_ord_of, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case o_ok => obtain ⟨rfl, rfl⟩ := h; exact mean_full_o_ok mem R0
    case omega => obtain ⟨rfl, rfl⟩ := h; exact mean_full_omega mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_ord_of, expand_ok3 mem R0 (Rstd mem) tbl_ord_of htbl bvt_ord_of r_ord_of chk_ord_of e]
  exact rel_ord_of mem e

theorem bvt_lam_ok : BvOk tbl_lam_ok := by
  intro n k g h
  cases n <;> simp only [tbl_lam_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case inaccessible => obtain ⟨rfl, rfl⟩ := h; exact bvok_inaccessible
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_lam_ok : ∀ v, v ∈ bv full_lam_ok → 2 ≤ v := by
  rw [full_lam_ok]; exact bv_expand_ge tbl_lam_ok bvt_lam_ok 2 r_lam_ok chk_lam_ok rge_lam_ok

theorem mean_full_lam_ok (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_lam_ok e ↔ Rstd mem .lam_ok ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_lam_ok n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_lam_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case inaccessible => obtain ⟨rfl, rfl⟩ := h; exact mean_full_inaccessible mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_lam_ok, expand_ok3 mem R0 (Rstd mem) tbl_lam_ok htbl bvt_lam_ok r_lam_ok chk_lam_ok e]
  exact rel_lam_ok mem e

theorem bvt_eps0 : BvOk tbl_eps0 := by
  intro n k g h
  cases n <;> simp only [tbl_eps0, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case o_ok => obtain ⟨rfl, rfl⟩ := h; exact bvok_o_ok
  case omega => obtain ⟨rfl, rfl⟩ := h; exact bvok_omega
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_eps0 : ∀ v, v ∈ bv full_eps0 → 1 ≤ v := by
  rw [full_eps0]; exact bv_expand_ge tbl_eps0 bvt_eps0 1 r_eps0 chk_eps0 rge_eps0

theorem mean_full_eps0 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_eps0 e ↔ Rstd mem .eps0 ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_eps0 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_eps0, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case o_ok => obtain ⟨rfl, rfl⟩ := h; exact mean_full_o_ok mem R0
    case omega => obtain ⟨rfl, rfl⟩ := h; exact mean_full_omega mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_eps0, expand_ok3 mem R0 (Rstd mem) tbl_eps0 htbl bvt_eps0 r_eps0 chk_eps0 e]
  exact rel_eps0 mem e

theorem bvt_lam_of : BvOk tbl_lam_of := by
  intro n k g h
  cases n <;> simp only [tbl_lam_of, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case eps0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_eps0
  case lam_ok => obtain ⟨rfl, rfl⟩ := h; exact bvok_lam_ok
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_lam_of : ∀ v, v ∈ bv full_lam_of → 2 ≤ v := by
  rw [full_lam_of]; exact bv_expand_ge tbl_lam_of bvt_lam_of 2 r_lam_of chk_lam_of rge_lam_of

theorem mean_full_lam_of (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_lam_of e ↔ Rstd mem .lam_of ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_lam_of n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_lam_of, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case eps0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_eps0 mem R0
    case lam_ok => obtain ⟨rfl, rfl⟩ := h; exact mean_full_lam_ok mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_lam_of, expand_ok3 mem R0 (Rstd mem) tbl_lam_of htbl bvt_lam_of r_lam_of chk_lam_of e]
  exact rel_lam_of mem e

theorem bvt_vstage : BvOk tbl_vstage := by
  intro n k g h
  cases n <;> simp only [tbl_vstage, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case ordinal => obtain ⟨rfl, rfl⟩ := h; exact bvok_ordinal
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case power_of => obtain ⟨rfl, rfl⟩ := h; exact bvok_power_of
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_vstage : ∀ v, v ∈ bv full_vstage → 2 ≤ v := by
  rw [full_vstage]; exact bv_expand_ge tbl_vstage bvt_vstage 2 r_vstage chk_vstage rge_vstage

theorem mean_full_vstage (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_vstage e ↔ Rstd mem .vstage ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_vstage n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_vstage, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case ordinal => obtain ⟨rfl, rfl⟩ := h; exact mean_full_ordinal mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case power_of => obtain ⟨rfl, rfl⟩ := h; exact mean_full_power_of mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_vstage, expand_ok3 mem R0 (Rstd mem) tbl_vstage htbl bvt_vstage r_vstage chk_vstage e]
  exact rel_vstage mem e

theorem bvt_cn_ok : BvOk tbl_cn_ok := by
  intro n k g h
  cases n <;> simp only [tbl_cn_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case symconst => obtain ⟨rfl, rfl⟩ := h; exact bvok_symconst
  case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_tuple4
theorem bvok_cn_ok : ∀ v, v ∈ bv full_cn_ok → 1 ≤ v := by
  rw [full_cn_ok]; exact bv_expand_ge tbl_cn_ok bvt_cn_ok 1 r_cn_ok chk_cn_ok rge_cn_ok

theorem mean_full_cn_ok (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_cn_ok e ↔ Rstd mem .cn_ok ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_cn_ok n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_cn_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case symconst => obtain ⟨rfl, rfl⟩ := h; exact mean_full_symconst mem R0
    case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_tuple4 mem R0
  rw [full_cn_ok, expand_ok3 mem R0 (Rstd mem) tbl_cn_ok htbl bvt_cn_ok r_cn_ok chk_cn_ok e]
  exact rel_cn_ok mem e

theorem bvt_theta_ok : BvOk tbl_theta_ok := by
  intro n k g h
  cases n <;> simp only [tbl_theta_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_theta_ok : ∀ v, v ∈ bv full_theta_ok → 2 ≤ v := by
  rw [full_theta_ok]; exact bv_expand_ge tbl_theta_ok bvt_theta_ok 2 r_theta_ok chk_theta_ok rge_theta_ok

theorem mean_full_theta_ok (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_theta_ok e ↔ Rstd mem .theta_ok ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_theta_ok n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_theta_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_theta_ok, expand_ok3 mem R0 (Rstd mem) tbl_theta_ok htbl bvt_theta_ok r_theta_ok chk_theta_ok e]
  exact rel_theta_ok mem e

theorem bvt_fn_ok : BvOk tbl_fn_ok := by
  intro n k g h
  cases n <;> simp only [tbl_fn_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral0
  case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral1
  case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral2
  case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral3
  case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral4
  case numeral8 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral8
  case ordinal => obtain ⟨rfl, rfl⟩ := h; exact bvok_ordinal
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case theta_ok => obtain ⟨rfl, rfl⟩ := h; exact bvok_theta_ok
  case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact bvok_tuple4
theorem bvok_fn_ok : ∀ v, v ∈ bv full_fn_ok → 4 ≤ v := by
  rw [full_fn_ok]; exact bv_expand_ge tbl_fn_ok bvt_fn_ok 4 r_fn_ok chk_fn_ok rge_fn_ok

theorem mean_full_fn_ok (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_fn_ok e ↔ Rstd mem .fn_ok ((List.range 4).map e) := by
  have htbl : ∀ n k g, tbl_fn_ok n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_fn_ok, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case numeral0 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral0 mem R0
    case numeral1 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral1 mem R0
    case numeral2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral2 mem R0
    case numeral3 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral3 mem R0
    case numeral4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral4 mem R0
    case numeral8 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral8 mem R0
    case ordinal => obtain ⟨rfl, rfl⟩ := h; exact mean_full_ordinal mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case theta_ok => obtain ⟨rfl, rfl⟩ := h; exact mean_full_theta_ok mem R0
    case tuple4 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_tuple4 mem R0
  rw [full_fn_ok, expand_ok3 mem R0 (Rstd mem) tbl_fn_ok htbl bvt_fn_ok r_fn_ok chk_fn_ok e]
  exact rel_fn_ok mem e

theorem bvt_struct_rec : BvOk tbl_struct_rec := by
  intro n k g h
  cases n <;> simp only [tbl_struct_rec, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case cn_ok => obtain ⟨rfl, rfl⟩ := h; exact bvok_cn_ok
  case e_restrict => obtain ⟨rfl, rfl⟩ := h; exact bvok_e_restrict
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case fn_ok => obtain ⟨rfl, rfl⟩ := h; exact bvok_fn_ok
  case l_order => obtain ⟨rfl, rfl⟩ := h; exact bvok_l_order
  case lam_of => obtain ⟨rfl, rfl⟩ := h; exact bvok_lam_of
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
  case theta_l => obtain ⟨rfl, rfl⟩ := h; exact bvok_theta_l
  case vstage => obtain ⟨rfl, rfl⟩ := h; exact bvok_vstage
theorem bvok_struct_rec : ∀ v, v ∈ bv full_struct_rec → 2 ≤ v := by
  rw [full_struct_rec]; exact bv_expand_ge tbl_struct_rec bvt_struct_rec 2 r_struct_rec chk_struct_rec rge_struct_rec

theorem mean_full_struct_rec (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_struct_rec e ↔ Rstd mem .struct_rec ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_struct_rec n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_struct_rec, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case cn_ok => obtain ⟨rfl, rfl⟩ := h; exact mean_full_cn_ok mem R0
    case e_restrict => obtain ⟨rfl, rfl⟩ := h; exact mean_full_e_restrict mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case fn_ok => obtain ⟨rfl, rfl⟩ := h; exact mean_full_fn_ok mem R0
    case l_order => obtain ⟨rfl, rfl⟩ := h; exact mean_full_l_order mem R0
    case lam_of => obtain ⟨rfl, rfl⟩ := h; exact mean_full_lam_of mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
    case theta_l => obtain ⟨rfl, rfl⟩ := h; exact mean_full_theta_l mem R0
    case vstage => obtain ⟨rfl, rfl⟩ := h; exact mean_full_vstage mem R0
  rw [full_struct_rec, expand_ok3 mem R0 (Rstd mem) tbl_struct_rec htbl bvt_struct_rec r_struct_rec chk_struct_rec e]
  exact rel_struct_rec mem e

theorem bvt_struct_full : BvOk tbl_struct_full := by
  intro n k g h
  cases n <;> simp only [tbl_struct_full, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case ord_of => obtain ⟨rfl, rfl⟩ := h; exact bvok_ord_of
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case struct_rec => obtain ⟨rfl, rfl⟩ := h; exact bvok_struct_rec
theorem bvok_struct_full : ∀ v, v ∈ bv full_struct_full → 6 ≤ v := by
  rw [full_struct_full]; exact bv_expand_ge tbl_struct_full bvt_struct_full 6 r_struct_full chk_struct_full rge_struct_full

theorem mean_full_struct_full (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_struct_full e ↔ Rstd mem .struct_full ((List.range 6).map e) := by
  have htbl : ∀ n k g, tbl_struct_full n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_struct_full, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case ord_of => obtain ⟨rfl, rfl⟩ := h; exact mean_full_ord_of mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case struct_rec => obtain ⟨rfl, rfl⟩ := h; exact mean_full_struct_rec mem R0
  rw [full_struct_full, expand_ok3 mem R0 (Rstd mem) tbl_struct_full htbl bvt_struct_full r_struct_full chk_struct_full e]
  exact rel_struct_full mem e

theorem bvt_func_on2 : BvOk tbl_func_on2 := by
  intro n k g h
  cases n <;> simp only [tbl_func_on2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_func_on2 : ∀ v, v ∈ bv full_func_on2 → 2 ≤ v := by
  rw [full_func_on2]; exact bv_expand_ge tbl_func_on2 bvt_func_on2 2 r_func_on2 chk_func_on2 rge_func_on2

theorem mean_full_func_on2 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_func_on2 e ↔ Rstd mem .func_on2 ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_func_on2 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_func_on2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_func_on2, expand_ok3 mem R0 (Rstd mem) tbl_func_on2 htbl bvt_func_on2 r_func_on2 chk_func_on2 e]
  exact rel_func_on2 mem e

theorem bvt_struct_table : BvOk tbl_struct_table := by
  intro n k g h
  cases n <;> simp only [tbl_struct_table, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case func_on2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_func_on2
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case struct_full => obtain ⟨rfl, rfl⟩ := h; exact bvok_struct_full
theorem bvok_struct_table : ∀ v, v ∈ bv full_struct_table → 2 ≤ v := by
  rw [full_struct_table]; exact bv_expand_ge tbl_struct_table bvt_struct_table 2 r_struct_table chk_struct_table rge_struct_table

theorem mean_full_struct_table (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_struct_table e ↔ Rstd mem .struct_table ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_struct_table n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_struct_table, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case func_on2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_func_on2 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case struct_full => obtain ⟨rfl, rfl⟩ := h; exact mean_full_struct_full mem R0
  rw [full_struct_table, expand_ok3 mem R0 (Rstd mem) tbl_struct_table htbl bvt_struct_table r_struct_table chk_struct_table e]
  exact rel_struct_table mem e

theorem bvt_definable_set : BvOk tbl_definable_set := by
  intro n k g h
  cases n <;> simp only [tbl_definable_set, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case definable_in => obtain ⟨rfl, rfl⟩ := h; exact bvok_definable_in
  case formula => obtain ⟨rfl, rfl⟩ := h; exact bvok_formula
  case metacode => obtain ⟨rfl, rfl⟩ := h; exact bvok_metacode
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
theorem bvok_definable_set : ∀ v, v ∈ bv full_definable_set → 3 ≤ v := by
  rw [full_definable_set]; exact bv_expand_ge tbl_definable_set bvt_definable_set 3 r_definable_set chk_definable_set rge_definable_set

theorem mean_full_definable_set (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_definable_set e ↔ Rstd mem .definable_set ((List.range 3).map e) := by
  have htbl : ∀ n k g, tbl_definable_set n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_definable_set, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case definable_in => obtain ⟨rfl, rfl⟩ := h; exact mean_full_definable_in mem R0
    case formula => obtain ⟨rfl, rfl⟩ := h; exact mean_full_formula mem R0
    case metacode => obtain ⟨rfl, rfl⟩ := h; exact mean_full_metacode mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
  rw [full_definable_set, expand_ok3 mem R0 (Rstd mem) tbl_definable_set htbl bvt_definable_set r_definable_set chk_definable_set e]
  exact rel_definable_set mem e

theorem bvt_finite_sum : BvOk tbl_finite_sum := by
  intro n k g h
  cases n <;> simp only [tbl_finite_sum, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case add => obtain ⟨rfl, rfl⟩ := h; exact bvok_add
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case func_on2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_func_on2
  case nat => obtain ⟨rfl, rfl⟩ := h; exact bvok_nat
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_finite_sum : ∀ v, v ∈ bv full_finite_sum → 2 ≤ v := by
  rw [full_finite_sum]; exact bv_expand_ge tbl_finite_sum bvt_finite_sum 2 r_finite_sum chk_finite_sum rge_finite_sum

theorem mean_full_finite_sum (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_finite_sum e ↔ Rstd mem .finite_sum ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_finite_sum n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_finite_sum, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case add => obtain ⟨rfl, rfl⟩ := h; exact mean_full_add mem R0
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case func_on2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_func_on2 mem R0
    case nat => obtain ⟨rfl, rfl⟩ := h; exact mean_full_nat mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_finite_sum, expand_ok3 mem R0 (Rstd mem) tbl_finite_sum htbl bvt_finite_sum r_finite_sum chk_finite_sum e]
  exact rel_finite_sum mem e

theorem bvt_f_val : BvOk tbl_f_val := by
  intro n k g h
  cases n <;> simp only [tbl_f_val, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case definable_set => obtain ⟨rfl, rfl⟩ := h; exact bvok_definable_set
  case finite_sum => obtain ⟨rfl, rfl⟩ := h; exact bvok_finite_sum
  case struct_table => obtain ⟨rfl, rfl⟩ := h; exact bvok_struct_table
theorem bvok_f_val : ∀ v, v ∈ bv full_f_val → 2 ≤ v := by
  rw [full_f_val]; exact bv_expand_ge tbl_f_val bvt_f_val 2 r_f_val chk_f_val rge_f_val

theorem mean_full_f_val (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_f_val e ↔ Rstd mem .f_val ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_f_val n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_f_val, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case definable_set => obtain ⟨rfl, rfl⟩ := h; exact mean_full_definable_set mem R0
    case finite_sum => obtain ⟨rfl, rfl⟩ := h; exact mean_full_finite_sum mem R0
    case struct_table => obtain ⟨rfl, rfl⟩ := h; exact mean_full_struct_table mem R0
  rw [full_f_val, expand_ok3 mem R0 (Rstd mem) tbl_f_val htbl bvt_f_val r_f_val chk_f_val e]
  exact rel_f_val mem e

theorem bvt_iterate10 : BvOk tbl_iterate10 := by
  intro n k g h
  cases n <;> simp only [tbl_iterate10, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case empty => obtain ⟨rfl, rfl⟩ := h; exact bvok_empty
  case f_val => obtain ⟨rfl, rfl⟩ := h; exact bvok_f_val
  case func_on2 => obtain ⟨rfl, rfl⟩ := h; exact bvok_func_on2
  case numeral10 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral10
  case pair => obtain ⟨rfl, rfl⟩ := h; exact bvok_pair
  case succ => obtain ⟨rfl, rfl⟩ := h; exact bvok_succ
theorem bvok_iterate10 : ∀ v, v ∈ bv full_iterate10 → 2 ≤ v := by
  rw [full_iterate10]; exact bv_expand_ge tbl_iterate10 bvt_iterate10 2 r_iterate10 chk_iterate10 rge_iterate10

theorem mean_full_iterate10 (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_iterate10 e ↔ Rstd mem .iterate10 ((List.range 2).map e) := by
  have htbl : ∀ n k g, tbl_iterate10 n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_iterate10, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case empty => obtain ⟨rfl, rfl⟩ := h; exact mean_full_empty mem R0
    case f_val => obtain ⟨rfl, rfl⟩ := h; exact mean_full_f_val mem R0
    case func_on2 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_func_on2 mem R0
    case numeral10 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral10 mem R0
    case pair => obtain ⟨rfl, rfl⟩ := h; exact mean_full_pair mem R0
    case succ => obtain ⟨rfl, rfl⟩ := h; exact mean_full_succ mem R0
  rw [full_iterate10, expand_ok3 mem R0 (Rstd mem) tbl_iterate10 htbl bvt_iterate10 r_iterate10 chk_iterate10 e]
  exact rel_iterate10 mem e

theorem bvt_lngn : BvOk tbl_lngn := by
  intro n k g h
  cases n <;> simp only [tbl_lngn, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  case hyper => obtain ⟨rfl, rfl⟩ := h; exact bvok_hyper
  case iterate10 => obtain ⟨rfl, rfl⟩ := h; exact bvok_iterate10
  case numeral10 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral10
  case numeral12 => obtain ⟨rfl, rfl⟩ := h; exact bvok_numeral12
theorem bvok_lngn : ∀ v, v ∈ bv full_lngn → 1 ≤ v := by
  rw [full_lngn]; exact bv_expand_ge tbl_lngn bvt_lngn 1 r_lngn chk_lngn rge_lngn

theorem mean_full_lngn (R0 : Nm → List α → Prop) (e : Nat → α) :
    ev mem R0 full_lngn e ↔ Rstd mem .lngn ((List.range 1).map e) := by
  have htbl : ∀ n k g, tbl_lngn n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rstd mem n ((List.range k).map e) := by
    intro n k g h
    cases n <;> simp only [tbl_lngn, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case hyper => obtain ⟨rfl, rfl⟩ := h; exact mean_full_hyper mem R0
    case iterate10 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_iterate10 mem R0
    case numeral10 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral10 mem R0
    case numeral12 => obtain ⟨rfl, rfl⟩ := h; exact mean_full_numeral12 mem R0
  rw [full_lngn, expand_ok3 mem R0 (Rstd mem) tbl_lngn htbl bvt_lngn r_lngn chk_lngn e]
  exact rel_lngn mem e

end
end Tr
