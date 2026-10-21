import TrPartsH
import TrLem
/-! 層 H の各部品が、意図した条件を正しく書き写していること（改訂52）。 -/
namespace Tr
section
variable {α : Type} (mem : α → α → Prop) (e : Nat → α)

theorem rel_omega : ev mem (Rstd mem) r_omega e ↔ Rstd mem .omega ((List.range 1).map e) := by
  simp only [r_omega]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [OmegaM, IsSucc, orImp, and_assoc, iff_def]
  done
theorem rel_func : ev mem (Rstd mem) r_func e ↔ Rstd mem .func ((List.range 3).map e) := by
  simp only [r_func]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [FuncM, At, orImp, and_assoc, iff_def]
  done
theorem rel_bij : ev mem (Rstd mem) r_bij e ↔ Rstd mem .bij ((List.range 3).map e) := by
  simp only [r_bij]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [BijM, At, orImp, and_assoc, iff_def]
  done
theorem rel_regular : ev mem (Rstd mem) r_regular e ↔ Rstd mem .regular ((List.range 1).map e) := by
  simp only [r_regular]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [RegularM, At, orImp, and_assoc, iff_def]
  done
theorem rel_power_of : ev mem (Rstd mem) r_power_of e ↔ Rstd mem .power_of ((List.range 2).map e) := by
  simp only [r_power_of]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [PowerOf, orImp, and_assoc, iff_def]
  done
theorem rel_strong_limit : ev mem (Rstd mem) r_strong_limit e ↔ Rstd mem .strong_limit ((List.range 1).map e) := by
  simp only [r_strong_limit]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [StrongLimitM, orImp, and_assoc, iff_def]
  done
theorem rel_inaccessible : ev mem (Rstd mem) r_inaccessible e ↔ Rstd mem .inaccessible ((List.range 1).map e) := by
  simp only [r_inaccessible]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [InaccM, orImp, and_assoc, iff_def]
  done
theorem rel_o_ok : ev mem (Rstd mem) r_o_ok e ↔ Rstd mem .o_ok ((List.range 2).map e) := by
  simp only [r_o_ok]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [OOk, FuncDom, At, orImp, and_assoc, iff_def]
  done
theorem rel_ord_of : ev mem (Rstd mem) r_ord_of e ↔ Rstd mem .ord_of ((List.range 2).map e) := by
  simp only [r_ord_of]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [OrdOf, At, orImp, and_assoc, iff_def]
  done
theorem rel_lam_ok : ev mem (Rstd mem) r_lam_ok e ↔ Rstd mem .lam_ok ((List.range 2).map e) := by
  simp only [r_lam_ok]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [LamOk, FuncDom, At, orImp, and_assoc, iff_def]
  done
theorem rel_eps0 : ev mem (Rstd mem) r_eps0 e ↔ Rstd mem .eps0 ((List.range 1).map e) := by
  simp only [r_eps0]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [Eps0M, At, orImp, and_assoc, iff_def]
  done
theorem rel_lam_of : ev mem (Rstd mem) r_lam_of e ↔ Rstd mem .lam_of ((List.range 2).map e) := by
  simp only [r_lam_of]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [LamOf, At, orImp, and_assoc, iff_def]
  done
end
end Tr
