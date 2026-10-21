import TrPartsD
import TrLem
/-! 定義可能性の層（definable.py）の各部品が、意図した条件を正しく書き写していること。 -/
namespace Tr
section
variable {α : Type} (mem : α → α → Prop) (e : Nat → α)

theorem rel_assign_w : ev mem (Rstd mem) r_assign_w e ↔ Rstd mem .assign_w ((List.range 3).map e) := by
  simp only [r_assign_w]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [AssignM, orImp, and_assoc]
  done
theorem rel_update_w : ev mem (Rstd mem) r_update_w e ↔ Rstd mem .update_w ((List.range 6).map e) := by
  simp only [r_update_w]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [UpdateM, At, orImp, and_assoc]
  done
theorem rel_is_definition : ev mem (Rstd mem) r_is_definition e ↔ Rstd mem .is_definition ((List.range 6).map e) := by
  simp only [r_is_definition]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [IsDefM, DefCommon, WDef, VarSet, SeqWith, At, Comp, orImp, and_assoc]
  done
theorem rel_param_true : ev mem (Rstd mem) r_param_true e ↔ Rstd mem .param_true ((List.range 7).map e) := by
  simp only [r_param_true]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [ParamTrueM, DefCommon, WDef, VarSet, SeqWith, At, Comp, orImp, and_assoc]
  done
theorem rel_definable_in : ev mem (Rstd mem) r_definable_in e ↔ Rstd mem .definable_in ((List.range 7).map e) := by
  simp only [r_definable_in]
  tr_raw
  simp [DefinableInM, and_assoc]
  done
end
end Tr
