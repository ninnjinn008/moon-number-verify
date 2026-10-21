import TrPartsF
import TrLem
/-! Θ の層（lorder.py の least_good・theta_L）の各部品が、意図した条件を正しく書き写していること。 -/
namespace Tr
section
variable {α : Type} (mem : α → α → Prop) (e : Nat → α)

theorem rel_formula_code_minus : ev mem (Rstd mem) r_formula_code_minus e ↔ Rstd mem .formula_code_minus ((List.range 1).map e) := by
  simp only [r_formula_code_minus]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [FormulaCodeMinus, orImp, and_assoc, iff_def]
  done
theorem rel_theta_value : ev mem (Rstd mem) r_theta_value e ↔ Rstd mem .theta_value ((List.range 3).map e) := by
  simp only [r_theta_value]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [ThetaValue, SingSeq, SymTheta, CompIs, SeqWith, At, orImp, and_assoc, iff_def]
  done
theorem rel_least_good : ev mem (Rstd mem) r_least_good e ↔ Rstd mem .least_good ((List.range 8).map e) := by
  simp only [r_least_good]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [LeastGood, GoodS, DepOnlyS, UpdateM, VarSet, SeqWith, At, Comp, orImp, and_assoc, iff_def]
  done
theorem rel_theta_l : ev mem (Rstd mem) r_theta_l e ↔ Rstd mem .theta_l ((List.range 6).map e) := by
  simp only [r_theta_l]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [ThetaLM, orImp, and_assoc, iff_def]
  done
end
end Tr
