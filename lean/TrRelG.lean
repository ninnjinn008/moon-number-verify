import TrPartsG
import TrLem
/-! 層 G の各部品が、意図した条件を正しく書き写していること（改訂52）。 -/
namespace Tr
section
variable {α : Type} (mem : α → α → Prop) (e : Nat → α)

theorem rel_numeral10 : ev mem (Rstd mem) r_numeral10 e ↔ Rstd mem .numeral10 ((List.range 1).map e) := by
  simp [r_numeral10, ev, upd, rstd_simp, r1, Num]
theorem rel_numeral11 : ev mem (Rstd mem) r_numeral11 e ↔ Rstd mem .numeral11 ((List.range 1).map e) := by
  simp [r_numeral11, ev, upd, rstd_simp, r1, Num]
theorem rel_numeral12 : ev mem (Rstd mem) r_numeral12 e ↔ Rstd mem .numeral12 ((List.range 1).map e) := by
  simp [r_numeral12, ev, upd, rstd_simp, r1, Num]
theorem rel_dec : ev mem (Rstd mem) r_dec e ↔ Rstd mem .dec ((List.range 3).map e) := by
  simp only [r_dec]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [DecM, orImp, and_assoc, iff_def]
  done
theorem rel_row_shape0 : ev mem (Rstd mem) r_row_shape0 e ↔ Rstd mem .row_shape0 ((List.range 1).map e) := by
  simp only [r_row_shape0]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [RowShape, Comp, SeqWith, orImp, and_assoc, iff_def]
  done
theorem rel_row_shape1 : ev mem (Rstd mem) r_row_shape1 e ↔ Rstd mem .row_shape1 ((List.range 1).map e) := by
  simp only [r_row_shape1]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [RowShape, Comp, SeqWith, orImp, and_assoc, iff_def]
  done
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rel_table_ok : ev mem (Rstd mem) r_table_ok e ↔ Rstd mem .table_ok ((List.range 1).map e) := by
  simp only [r_table_ok]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [TableOk, HrOk, CmpOk, RowGet0, RowGet1, RowShape, Comp, orImp, and_assoc, iff_def]
  done
theorem rel_cnf_cmp : ev mem (Rstd mem) r_cnf_cmp e ↔ Rstd mem .cnf_cmp ((List.range 3).map e) := by
  simp only [r_cnf_cmp]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [CnfCmp, RowGet1, Comp, orImp, and_assoc, iff_def]
  done
theorem rel_cnf_lt : ev mem (Rstd mem) r_cnf_lt e ↔ Rstd mem .cnf_lt ((List.range 2).map e) := by
  simp only [r_cnf_lt]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [CnfLt, orImp, and_assoc, iff_def]
  done
end
end Tr
