/-
  書き写しの検証（改訂42）：各部品の式（下の層は名前つきの関係）が、意図した条件と一致すること。
-/
import TrPartsC
import TrLem
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Tr

section
variable {α : Type} (mem : α → α → Prop) (e : Nat → α)


theorem rel_empty : ev mem (Rstd mem) r_empty e ↔ Rstd mem .empty ((List.range 1).map e) := by
  simp [r_empty, ev, upd, rstd_simp, r1, Empty]
theorem rel_succ : ev mem (Rstd mem) r_succ e ↔ Rstd mem .succ ((List.range 2).map e) := by
  simp [r_succ, ev, upd, rstd_simp, r2, Succ, orImp, iff_def]
theorem rel_trans : ev mem (Rstd mem) r_trans e ↔ Rstd mem .trans ((List.range 1).map e) := by
  simp [r_trans, ev, upd, rstd_simp, r1, Trans]
theorem rel_pair : ev mem (Rstd mem) r_pair e ↔ Rstd mem .pair ((List.range 3).map e) := by
  simp [r_pair, ev, upd, rstd_simp, r3, Pair, Sing, Dbl, orImp, and_assoc]
theorem rel_is_one : ev mem (Rstd mem) r_is_one e ↔ Rstd mem .is_one ((List.range 1).map e) := by
  simp [r_is_one, ev, upd, rstd_simp, r1, IsOne]
theorem rel_numeral0 : ev mem (Rstd mem) r_numeral0 e ↔ Rstd mem .numeral0 ((List.range 1).map e) := by
  simp [r_numeral0, ev, upd, rstd_simp, r1, Num, Empty]
theorem rel_numeral1 : ev mem (Rstd mem) r_numeral1 e ↔ Rstd mem .numeral1 ((List.range 1).map e) := by
  simp [r_numeral1, ev, upd, rstd_simp, r1, Num]
theorem rel_numeral2 : ev mem (Rstd mem) r_numeral2 e ↔ Rstd mem .numeral2 ((List.range 1).map e) := by
  simp [r_numeral2, ev, upd, rstd_simp, r1, Num]
theorem rel_numeral3 : ev mem (Rstd mem) r_numeral3 e ↔ Rstd mem .numeral3 ((List.range 1).map e) := by
  simp [r_numeral3, ev, upd, rstd_simp, r1, Num]
theorem rel_numeral4 : ev mem (Rstd mem) r_numeral4 e ↔ Rstd mem .numeral4 ((List.range 1).map e) := by
  simp [r_numeral4, ev, upd, rstd_simp, r1, Num]
theorem rel_nat : ev mem (Rstd mem) r_nat e ↔ Rstd mem .nat ((List.range 1).map e) := by
  simp [r_nat, ev, upd, rstd_simp, r1, NatM, orImp, and_assoc]
  done
theorem rel_triple : ev mem (Rstd mem) r_triple e ↔ Rstd mem .triple ((List.range 4).map e) := by
  simp [r_triple, ev, upd, rstd_simp, r4, Triple, L_first]

theorem rel_hyper_table : ev mem (Rstd mem) r_hyper_table e ↔ Rstd mem .hyper_table ((List.range 2).map e) := by
  simp only [r_hyper_table]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [rstd_simp, r2, HyperTable, HCase, HBase, IsOne, orImp, and_assoc]
  done
theorem rel_hyper : ev mem (Rstd mem) r_hyper e ↔ Rstd mem .hyper ((List.range 4).map e) := by
  simp [r_hyper, ev, upd, rstd_simp, r4, Hyper]
theorem rel_add : ev mem (Rstd mem) r_add e ↔ Rstd mem .add ((List.range 3).map e) := by
  simp [r_add, ev, upd, rstd_simp, r3, Op]
theorem rel_mul : ev mem (Rstd mem) r_mul e ↔ Rstd mem .mul ((List.range 3).map e) := by
  simp [r_mul, ev, upd, rstd_simp, r3, Op]
theorem rel_exp : ev mem (Rstd mem) r_exp e ↔ Rstd mem .exp ((List.range 3).map e) := by
  simp [r_exp, ev, upd, rstd_simp, r3, Op]
theorem rel_divides : ev mem (Rstd mem) r_divides e ↔ Rstd mem .divides ((List.range 2).map e) := by
  simp [r_divides, ev, upd, rstd_simp, r2, Divides]
theorem rel_prime : ev mem (Rstd mem) r_prime e ↔ Rstd mem .prime ((List.range 1).map e) := by
  simp only [r_prime]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [rstd_simp, r1, PrimeM, Small, orImp, and_assoc]
  done
theorem rel_prime_table : ev mem (Rstd mem) r_prime_table e ↔ Rstd mem .prime_table ((List.range 1).map e) := by
  simp only [r_prime_table]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [rstd_simp, r1, PrimeTable, orImp, and_assoc]
  done
theorem rel_nth_prime : ev mem (Rstd mem) r_nth_prime e ↔ Rstd mem .nth_prime ((List.range 2).map e) := by
  simp only [r_nth_prime]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [rstd_simp, r2, NthPrime]
  done
theorem rel_seqfun : ev mem (Rstd mem) r_seqfun e ↔ Rstd mem .seqfun ((List.range 2).map e) := by
  simp only [r_seqfun]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [rstd_simp, r2, SeqWith, and_assoc]
  done
theorem rel_prod_table : ev mem (Rstd mem) r_prod_table e ↔ Rstd mem .prod_table ((List.range 2).map e) := by
  simp only [r_prod_table]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [rstd_simp, r2, ProdTable, orImp, and_assoc]
  done
theorem rel_encode : ev mem (Rstd mem) r_encode e ↔ Rstd mem .encode ((List.range 2).map e) := by
  simp only [r_encode]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [rstd_simp, r2, EncodeM, and_assoc]
  done
theorem rel_tuple4 : ev mem (Rstd mem) r_tuple4 e ↔ Rstd mem .tuple4 ((List.range 1).map e) := by
  simp only [r_tuple4]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [rstd_simp, r1, Tuple4, SeqWith, and_assoc]
  done
theorem rel_metacode : ev mem (Rstd mem) r_metacode e ↔ Rstd mem .metacode ((List.range 2).map e) := by
  simp only [r_metacode]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [rstd_simp, r2, MetaCodeM, SeqWith, and_assoc]
  done
theorem rel_numeral5 : ev mem (Rstd mem) r_numeral5 e ↔ Rstd mem .numeral5 ((List.range 1).map e) := by
  simp [r_numeral5, ev, upd, rstd_simp, r1, Num]
theorem rel_numeral6 : ev mem (Rstd mem) r_numeral6 e ↔ Rstd mem .numeral6 ((List.range 1).map e) := by
  simp [r_numeral6, ev, upd, rstd_simp, r1, Num]
theorem rel_numeral7 : ev mem (Rstd mem) r_numeral7 e ↔ Rstd mem .numeral7 ((List.range 1).map e) := by
  simp [r_numeral7, ev, upd, rstd_simp, r1, Num]
theorem rel_numeral8 : ev mem (Rstd mem) r_numeral8 e ↔ Rstd mem .numeral8 ((List.range 1).map e) := by
  simp [r_numeral8, ev, upd, rstd_simp, r1, Num]
theorem rel_numeral9 : ev mem (Rstd mem) r_numeral9 e ↔ Rstd mem .numeral9 ((List.range 1).map e) := by
  simp [r_numeral9, ev, upd, rstd_simp, r1, Num]
theorem rel_punct0 : ev mem (Rstd mem) r_punct0 e ↔ Rstd mem .punct0 ((List.range 1).map e) := by
  simp only [r_punct0]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [PunctM, CompIs, orImp, and_assoc]
  done
theorem rel_punct1 : ev mem (Rstd mem) r_punct1 e ↔ Rstd mem .punct1 ((List.range 1).map e) := by
  simp only [r_punct1]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [PunctM, CompIs, orImp, and_assoc]
  done
theorem rel_punct2 : ev mem (Rstd mem) r_punct2 e ↔ Rstd mem .punct2 ((List.range 1).map e) := by
  simp only [r_punct2]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [PunctM, CompIs, orImp, and_assoc]
  done
theorem rel_punct3 : ev mem (Rstd mem) r_punct3 e ↔ Rstd mem .punct3 ((List.range 1).map e) := by
  simp only [r_punct3]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [PunctM, CompIs, orImp, and_assoc]
  done
theorem rel_punct4 : ev mem (Rstd mem) r_punct4 e ↔ Rstd mem .punct4 ((List.range 1).map e) := by
  simp only [r_punct4]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [PunctM, CompIs, orImp, and_assoc]
  done
theorem rel_punct5 : ev mem (Rstd mem) r_punct5 e ↔ Rstd mem .punct5 ((List.range 1).map e) := by
  simp only [r_punct5]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [PunctM, CompIs, orImp, and_assoc]
  done
theorem rel_symvar : ev mem (Rstd mem) r_symvar e ↔ Rstd mem .symvar ((List.range 1).map e) := by
  simp only [r_symvar]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [SymVar, CompIs, orImp, and_assoc]
  done
theorem rel_symconst : ev mem (Rstd mem) r_symconst e ↔ Rstd mem .symconst ((List.range 1).map e) := by
  simp only [r_symconst]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [SymConst, CompIs, orImp, and_assoc]
  done
theorem rel_symfunc : ev mem (Rstd mem) r_symfunc e ↔ Rstd mem .symfunc ((List.range 1).map e) := by
  simp only [r_symfunc]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [SymFunc, CompIs, orImp, and_assoc]
  done
theorem rel_symrel : ev mem (Rstd mem) r_symrel e ↔ Rstd mem .symrel ((List.range 1).map e) := by
  simp only [r_symrel]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [SymRel, CompIs, orImp, and_assoc]
  done
theorem rel_symelem : ev mem (Rstd mem) r_symelem e ↔ Rstd mem .symelem ((List.range 1).map e) := by
  simp only [r_symelem]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [SymElem, CompIs, orImp, and_assoc]
  done
theorem rel_symtheta : ev mem (Rstd mem) r_symtheta e ↔ Rstd mem .symtheta ((List.range 1).map e) := by
  simp only [r_symtheta]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [SymTheta, CompIs, orImp, and_assoc]
  done
theorem rel_plus2 : ev mem (Rstd mem) r_plus2 e ↔ Rstd mem .plus2 ((List.range 2).map e) := by
  simp only [r_plus2]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [Plus2]
  done
theorem rel_certificate : ev mem (Rstd mem) r_certificate e ↔ Rstd mem .certificate ((List.range 4).map e) := by
  simp only [r_certificate]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [CertOk, TermOkM, FormOkM, ListOkM, ArgsOk, Infix, At, InCert, Nxt, Prv, Comp, orImp, and_assoc]
  done
theorem rel_formula : ev mem (Rstd mem) r_formula e ↔ Rstd mem .formula ((List.range 1).map e) := by
  simp only [r_formula]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [FormulaM, SeqWith, InCert, and_assoc]
  done
theorem rel_formula_minus : ev mem (Rstd mem) r_formula_minus e ↔ Rstd mem .formula_minus ((List.range 1).map e) := by
  simp only [r_formula_minus]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [FormulaMinusM, SeqWith, InCert, At, and_assoc]
  constructor
  · rintro ⟨K0, h0, K1, h1, h, hn, h2, h3, h4, C, p, hp, ht, hc, hno⟩
    exact ⟨K0, h0, K1, h1, h, hn, h2, h3, h4, ⟨C, ⟨p, hp, ht⟩, hc⟩, hno⟩
  · rintro ⟨K0, h0, K1, h1, h, hn, h2, h3, h4, ⟨C, ⟨p, hp, ht⟩, hc⟩, hno⟩
    exact ⟨K0, h0, K1, h1, h, hn, h2, h3, h4, C, p, hp, ht, hc, hno⟩
theorem rel_assign : ev mem (Rstd mem) r_assign e ↔ Rstd mem .assign ((List.range 3).map e) := by
  simp only [r_assign]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [AssignM, orImp, and_assoc]
  done
theorem rel_update : ev mem (Rstd mem) r_update e ↔ Rstd mem .update ((List.range 6).map e) := by
  simp only [r_update]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [UpdateM, At, orImp, and_assoc]
  done
theorem rel_in_s : ev mem (Rstd mem) r_in_s e ↔ Rstd mem .in_s ((List.range 4).map e) := by
  simp only [r_in_s]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [InS, orImp, and_assoc]
  done
theorem rel_in_pair : ev mem (Rstd mem) r_in_pair e ↔ Rstd mem .in_pair ((List.range 3).map e) := by
  simp only [r_in_pair]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [InPair, orImp, and_assoc]
  done
theorem rel_in_triple : ev mem (Rstd mem) r_in_triple e ↔ Rstd mem .in_triple ((List.range 4).map e) := by
  simp only [r_in_triple]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [InTriple, orImp, and_assoc]
  done
theorem rel_cons : ev mem (Rstd mem) r_cons e ↔ Rstd mem .cons ((List.range 3).map e) := by
  simp only [r_cons]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [ConsM, Nxt, orImp, and_assoc]
  done
theorem rel_term_clause : ev mem (Rstd mem) r_term_clause e ↔ Rstd mem .term_clause ((List.range 8).map e) := by
  simp only [r_term_clause]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [TermClauseM, At, Comp, Nxt, Prv, Tv, orImp, and_assoc]
  done
theorem rel_list_clause : ev mem (Rstd mem) r_list_clause e ↔ Rstd mem .list_clause ((List.range 8).map e) := by
  simp only [r_list_clause]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [ListClauseM, InCert, Tv, orImp, and_assoc]
  done
theorem rel_formula_clause : ev mem (Rstd mem) r_formula_clause e ↔ Rstd mem .formula_clause ((List.range 13).map e) := by
  simp only [r_formula_clause]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [FormClauseM, InfixS, At, Comp, Nxt, Prv, Tv, InCert, orImp, and_assoc]
  done
theorem rel_tv_ok : ev mem (Rstd mem) r_tv_ok e ↔ Rstd mem .tv_ok ((List.range 8).map e) := by
  simp only [r_tv_ok]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [TvOk, Tv, TvAll, orImp, and_assoc]
  done
theorem rel_s_ok : ev mem (Rstd mem) r_s_ok e ↔ Rstd mem .s_ok ((List.range 10).map e) := by
  simp only [r_s_ok]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [SOk, orImp, and_assoc, iff_def]
  done
theorem rel_varset : ev mem (Rstd mem) r_varset e ↔ Rstd mem .varset ((List.range 3).map e) := by
  simp only [r_varset]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [VarSet, At, Comp, orImp, and_assoc]
  done
theorem rel_sat : ev mem (Rstd mem) r_sat e ↔ Rstd mem .sat ((List.range 7).map e) := by
  simp only [r_sat]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [SatM, SatBody, SeqWith, InCert, orImp, and_assoc]
  done
theorem rel_sat_ext : ev mem (Rstd mem) r_sat_ext e ↔ Rstd mem .sat_ext ((List.range 7).map e) := by
  simp only [r_sat_ext]
  tr_raw
  try simp only [L_lookup, L_allpairs, L_parts, L_first, L_triples, L_triple_ex, L_incert, L_allcert]
  simp [SatExtM, SatBody, SeqWith, InCert, orImp, and_assoc]
  done
end
end Tr
