import TrPartsE
import TrLem
/-! L の段階と <_L の層（lorder.py）の各部品が、意図した条件を正しく書き写していること。 -/
namespace Tr
section
variable {α : Type} (mem : α → α → Prop) (e : Nat → α)

theorem rel_ordinal : ev mem (Rstd mem) r_ordinal e ↔ Rstd mem .ordinal ((List.range 1).map e) := by
  simp only [r_ordinal]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [OrdinalM, Trans, orImp, and_assoc, iff_def]
  done
theorem rel_e_restrict : ev mem (Rstd mem) r_e_restrict e ↔ Rstd mem .e_restrict ((List.range 2).map e) := by
  simp only [r_e_restrict]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [ERestrict, orImp, and_assoc, iff_def]
  done
theorem rel_func_on : ev mem (Rstd mem) r_func_on e ↔ Rstd mem .func_on ((List.range 3).map e) := by
  simp only [r_func_on]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [AssignM, orImp, and_assoc, iff_def]
  done
theorem rel_in_pair_l : ev mem (Rstd mem) r_in_pair_l e ↔ Rstd mem .in_pair_l ((List.range 3).map e) := by
  simp only [r_in_pair_l]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [InPair, orImp, and_assoc, iff_def]
  done
theorem rel_pure : ev mem (Rstd mem) r_pure e ↔ Rstd mem .pure ((List.range 2).map e) := by
  simp only [r_pure]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [Pure, At, orImp, and_assoc, iff_def]
  done
theorem rel_def_code : ev mem (Rstd mem) r_def_code e ↔ Rstd mem .def_code ((List.range 1).map e) := by
  simp only [r_def_code]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [DefCode, SeqWith, orImp, and_assoc, iff_def]
  done
theorem rel_defines : ev mem (Rstd mem) r_defines e ↔ Rstd mem .defines ((List.range 4).map e) := by
  simp only [r_defines]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [DefinesM, SigmaIs, VarSet, SeqWith, At, Comp, orImp, and_assoc, iff_def]
  done
theorem rel_lex_less : ev mem (Rstd mem) r_lex_less e ↔ Rstd mem .lex_less ((List.range 3).map e) := by
  simp only [r_lex_less]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [LexLess, InPair, orImp, and_assoc, iff_def]
  done
theorem rel_def_less : ev mem (Rstd mem) r_def_less e ↔ Rstd mem .def_less ((List.range 5).map e) := by
  simp only [r_def_less]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [DefLess, orImp, and_assoc, iff_def]
  done
theorem rel_def_table : ev mem (Rstd mem) r_def_table e ↔ Rstd mem .def_table ((List.range 2).map e) := by
  simp only [r_def_table]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [DefTable, DefEntry, orImp, and_assoc, iff_def]
  done
theorem rel_new_less : ev mem (Rstd mem) r_new_less e ↔ Rstd mem .new_less ((List.range 4).map e) := by
  simp only [r_new_less]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [NewLess, DefEntry, orImp, and_assoc, iff_def]
  done
theorem rel_step : ev mem (Rstd mem) r_step e ↔ Rstd mem .step ((List.range 4).map e) := by
  simp only [r_step]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [StepM, DefEntry, InPair, orImp, and_assoc, iff_def]
  done
theorem rel_l_order : ev mem (Rstd mem) r_l_order e ↔ Rstd mem .l_order ((List.range 3).map e) := by
  simp only [r_l_order]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [LOrderM, AtT, ValueOk, UnionOk, IsSucc, At, orImp, and_assoc, iff_def]
  done
end
end Tr
