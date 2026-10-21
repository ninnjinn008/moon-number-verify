import TrPartsJ
import TrLem
/-! 層 J の各部品が、意図した条件を正しく書き写していること（改訂52）。 -/
namespace Tr
section
variable {α : Type} (mem : α → α → Prop) (e : Nat → α)

theorem rel_func_on2 : ev mem (Rstd mem) r_func_on2 e ↔ Rstd mem .func_on2 ((List.range 2).map e) := by
  simp only [r_func_on2]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [FuncOn2, At, orImp, and_assoc, iff_def]
  done
theorem rel_struct_table : ev mem (Rstd mem) r_struct_table e ↔ Rstd mem .struct_table ((List.range 2).map e) := by
  simp only [r_struct_table]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [StructTable, StructParts, At, orImp, and_assoc, iff_def]
  done
theorem rel_definable_set : ev mem (Rstd mem) r_definable_set e ↔ Rstd mem .definable_set ((List.range 3).map e) := by
  simp only [r_definable_set]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [DefinableSet, StructParts, At, orImp, and_assoc, iff_def]
  done
theorem rel_finite_sum : ev mem (Rstd mem) r_finite_sum e ↔ Rstd mem .finite_sum ((List.range 2).map e) := by
  simp only [r_finite_sum]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [FiniteSum, At, orImp, and_assoc, iff_def]
  done
theorem rel_f_val : ev mem (Rstd mem) r_f_val e ↔ Rstd mem .f_val ((List.range 2).map e) := by
  simp only [r_f_val]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [FValM, orImp, and_assoc, iff_def]
  done
theorem rel_iterate10 : ev mem (Rstd mem) r_iterate10 e ↔ Rstd mem .iterate10 ((List.range 2).map e) := by
  simp only [r_iterate10]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [Iterate10, At, orImp, and_assoc, iff_def]
  done
theorem rel_lngn : ev mem (Rstd mem) r_lngn e ↔ Rstd mem .lngn ((List.range 1).map e) := by
  simp only [r_lngn]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [LngnM, orImp, and_assoc, iff_def]
  done
end
end Tr
