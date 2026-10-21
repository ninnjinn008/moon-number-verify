import TrPartsI
import TrLem
/-! 層 I の各部品が、意図した条件を正しく書き写していること（改訂52）。 -/
namespace Tr
section
variable {α : Type} (mem : α → α → Prop) (e : Nat → α)

theorem rel_vstage : ev mem (Rstd mem) r_vstage e ↔ Rstd mem .vstage ((List.range 2).map e) := by
  simp only [r_vstage]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [VStage, VVal, FuncDom, IsSucc, At, orImp, and_assoc, iff_def]
  done
theorem rel_cn_ok : ev mem (Rstd mem) r_cn_ok e ↔ Rstd mem .cn_ok ((List.range 1).map e) := by
  simp only [r_cn_ok]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [CnOk, orImp, and_assoc, iff_def]
  done
theorem rel_theta_ok : ev mem (Rstd mem) r_theta_ok e ↔ Rstd mem .theta_ok ((List.range 2).map e) := by
  simp only [r_theta_ok]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [FuncM, At, orImp, and_assoc, iff_def]
  done
set_option maxHeartbeats 4000000 in
theorem rel_fn_ok : ev mem (Rstd mem) r_fn_ok e ↔ Rstd mem .fn_ok ((List.range 4).map e) := by
  simp only [r_fn_ok]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [FnOk, FnEntry, UVal, IsU, IsF, SymTheta, CompIs, SingSeq, ThetaValue, SeqWith, Comp, At, orImp, and_assoc, iff_def]
  done
theorem rel_struct_rec : ev mem (Rstd mem) r_struct_rec e ↔ Rstd mem .struct_rec ((List.range 2).map e) := by
  simp only [r_struct_rec]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [StructRec, StructParts, LevelM, FuncDom, At, orImp, and_assoc, iff_def]
  done
theorem rel_struct_full : ev mem (Rstd mem) r_struct_full e ↔ Rstd mem .struct_full ((List.range 6).map e) := by
  simp only [r_struct_full]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [StructFull, StructParts, At, orImp, and_assoc, iff_def]
  done
end
end Tr
