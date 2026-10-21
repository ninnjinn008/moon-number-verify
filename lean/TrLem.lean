/-
  書き写しの検証：TrRel で使う補助の補題（有界量化の書き換え）と tactic tr_raw。
-/
import TrCore
import TrAttr
set_option maxRecDepth 20000
namespace Tr

/-! Rstd の各場合（simp で Rstd を直接展開すると遅いので、場合ごとの等式を使う）。 -/
section
variable {α : Type} (mem : α → α → Prop)
@[rstd_simp] theorem rstd_empty (a : α) : Rstd mem .empty [a] = (Empty mem a) := rfl
@[rstd_simp] theorem rstd_succ (b c : α) : Rstd mem .succ [b, c] = (Succ mem b c) := rfl
@[rstd_simp] theorem rstd_trans (a : α) : Rstd mem .trans [a] = (Trans mem a) := rfl
@[rstd_simp] theorem rstd_pair (p a b : α) : Rstd mem .pair [p, a, b] = (Pair mem p a b) := rfl
@[rstd_simp] theorem rstd_is_one (z : α) : Rstd mem .is_one [z] = (IsOne mem z) := rfl
@[rstd_simp] theorem rstd_numeral0 (v : α) : Rstd mem .numeral0 [v] = (Num mem 0 v) := rfl
@[rstd_simp] theorem rstd_numeral1 (v : α) : Rstd mem .numeral1 [v] = (Num mem 1 v) := rfl
@[rstd_simp] theorem rstd_numeral2 (v : α) : Rstd mem .numeral2 [v] = (Num mem 2 v) := rfl
@[rstd_simp] theorem rstd_numeral3 (v : α) : Rstd mem .numeral3 [v] = (Num mem 3 v) := rfl
@[rstd_simp] theorem rstd_numeral4 (v : α) : Rstd mem .numeral4 [v] = (Num mem 4 v) := rfl
@[rstd_simp] theorem rstd_nat (a : α) : Rstd mem .nat [a] = (NatM mem a) := rfl
@[rstd_simp] theorem rstd_triple (p n b v : α) : Rstd mem .triple [p, n, b, v] = (Triple mem p n b v) := rfl
@[rstd_simp] theorem rstd_hyper_table (t a : α) : Rstd mem .hyper_table [t, a] = (HyperTable mem t a) := rfl
@[rstd_simp] theorem rstd_hyper (n a b c : α) : Rstd mem .hyper [n, a, b, c] = (Hyper mem n a b c) := rfl
@[rstd_simp] theorem rstd_add (a b c : α) : Rstd mem .add [a, b, c] = (Op mem 1 a b c) := rfl
@[rstd_simp] theorem rstd_mul (a b c : α) : Rstd mem .mul [a, b, c] = (Op mem 2 a b c) := rfl
@[rstd_simp] theorem rstd_exp (a b c : α) : Rstd mem .exp [a, b, c] = (Op mem 3 a b c) := rfl
@[rstd_simp] theorem rstd_divides (d m : α) : Rstd mem .divides [d, m] = (Divides mem d m) := rfl
@[rstd_simp] theorem rstd_prime (p : α) : Rstd mem .prime [p] = (PrimeM mem p) := rfl
@[rstd_simp] theorem rstd_prime_table (t : α) : Rstd mem .prime_table [t] = (PrimeTable mem t) := rfl
@[rstd_simp] theorem rstd_nth_prime (i p : α) : Rstd mem .nth_prime [i, p] = (NthPrime mem i p) := rfl
@[rstd_simp] theorem rstd_seqfun (s h : α) : Rstd mem .seqfun [s, h] = (SeqWith mem s h (NatM mem)) := rfl
@[rstd_simp] theorem rstd_prod_table (t s : α) : Rstd mem .prod_table [t, s] = (ProdTable mem t s) := rfl
@[rstd_simp] theorem rstd_encode (s c : α) : Rstd mem .encode [s, c] = (EncodeM mem s c) := rfl
@[rstd_simp] theorem rstd_tuple4 (t : α) : Rstd mem .tuple4 [t] = (Tuple4 mem t) := rfl
@[rstd_simp] theorem rstd_metacode (n s : α) : Rstd mem .metacode [n, s] = (MetaCodeM mem n s) := rfl
@[rstd_simp] theorem rstd_numeral5 (v : α) : Rstd mem .numeral5 [v] = (Num mem 5 v) := rfl
@[rstd_simp] theorem rstd_numeral6 (v : α) : Rstd mem .numeral6 [v] = (Num mem 6 v) := rfl
@[rstd_simp] theorem rstd_numeral7 (v : α) : Rstd mem .numeral7 [v] = (Num mem 7 v) := rfl
@[rstd_simp] theorem rstd_numeral8 (v : α) : Rstd mem .numeral8 [v] = (Num mem 8 v) := rfl
@[rstd_simp] theorem rstd_numeral9 (v : α) : Rstd mem .numeral9 [v] = (Num mem 9 v) := rfl
@[rstd_simp] theorem rstd_punct0 (t : α) : Rstd mem .punct0 [t] = (PunctM mem 0 t) := rfl
@[rstd_simp] theorem rstd_punct1 (t : α) : Rstd mem .punct1 [t] = (PunctM mem 1 t) := rfl
@[rstd_simp] theorem rstd_punct2 (t : α) : Rstd mem .punct2 [t] = (PunctM mem 2 t) := rfl
@[rstd_simp] theorem rstd_punct3 (t : α) : Rstd mem .punct3 [t] = (PunctM mem 3 t) := rfl
@[rstd_simp] theorem rstd_punct4 (t : α) : Rstd mem .punct4 [t] = (PunctM mem 4 t) := rfl
@[rstd_simp] theorem rstd_punct5 (t : α) : Rstd mem .punct5 [t] = (PunctM mem 5 t) := rfl
@[rstd_simp] theorem rstd_symvar (t : α) : Rstd mem .symvar [t] = (SymVar mem t) := rfl
@[rstd_simp] theorem rstd_symconst (t : α) : Rstd mem .symconst [t] = (SymConst mem t) := rfl
@[rstd_simp] theorem rstd_symfunc (t : α) : Rstd mem .symfunc [t] = (SymFunc mem t) := rfl
@[rstd_simp] theorem rstd_symrel (t : α) : Rstd mem .symrel [t] = (SymRel mem t) := rfl
@[rstd_simp] theorem rstd_symelem (t : α) : Rstd mem .symelem [t] = (SymElem mem t) := rfl
@[rstd_simp] theorem rstd_symtheta (t : α) : Rstd mem .symtheta [t] = (SymTheta mem t) := rfl
@[rstd_simp] theorem rstd_plus2 (n k : α) : Rstd mem .plus2 [n, k] = (Plus2 mem n k) := rfl
@[rstd_simp] theorem rstd_certificate (s C K0 K1 : α) : Rstd mem .certificate [s, C, K0, K1] = (CertOk mem s C K0 K1) := rfl
@[rstd_simp] theorem rstd_formula (s : α) : Rstd mem .formula [s] = (FormulaM mem s) := rfl
@[rstd_simp] theorem rstd_formula_minus (s : α) : Rstd mem .formula_minus [s] = (FormulaMinusM mem s) := rfl
@[rstd_simp] theorem rstd_assign (Ns dom sg : α) : Rstd mem .assign [Ns, dom, sg] = (AssignM mem Ns dom sg) := rfl
@[rstd_simp] theorem rstd_update (Ns dom sg k a sg2 : α) : Rstd mem .update [Ns, dom, sg, k, a, sg2] = (UpdateM mem Ns dom sg k a sg2) := rfl
@[rstd_simp] theorem rstd_in_s (S i j sg : α) : Rstd mem .in_s [S, i, j, sg] = (InS mem S i j sg) := rfl
@[rstd_simp] theorem rstd_in_pair (X a b : α) : Rstd mem .in_pair [X, a, b] = (InPair mem X a b) := rfl
@[rstd_simp] theorem rstd_in_triple (X a b c : α) : Rstd mem .in_triple [X, a, b, c] = (InTriple mem X a b c) := rfl
@[rstd_simp] theorem rstd_cons (v w2 w : α) : Rstd mem .cons [v, w2, w] = (ConsM mem v w2 w) := rfl
@[rstd_simp] theorem rstd_term_clause (s Cn Fn TV i j sg v : α) : Rstd mem .term_clause [s, Cn, Fn, TV, i, j, sg, v] = (TermClauseM mem s Cn Fn TV i j sg v) := rfl
@[rstd_simp] theorem rstd_list_clause (C K0 TV i j n sg w : α) : Rstd mem .list_clause [C, K0, TV, i, j, n, sg, w] = (ListClauseM mem C K0 TV i j n sg w) := rfl
@[rstd_simp] theorem rstd_formula_clause (s dom E Rel Ns C K0 K1 TV S i j sg : α) : Rstd mem .formula_clause [s, dom, E, Rel, Ns, C, K0, K1, TV, S, i, j, sg] = (FormClauseM mem s dom E Rel Ns C K0 K1 TV S i j sg) := rfl
@[rstd_simp] theorem rstd_tv_ok (s dom Cn Fn Ns C K0 TV : α) : Rstd mem .tv_ok [s, dom, Cn, Fn, Ns, C, K0, TV] = (TvOk mem s dom Cn Fn Ns C K0 TV) := rfl
@[rstd_simp] theorem rstd_s_ok (s dom E Rel Ns C K0 K1 TV S : α) : Rstd mem .s_ok [s, dom, E, Rel, Ns, C, K0, K1, TV, S] = (SOk mem s dom E Rel Ns C K0 K1 TV S) := rfl
@[rstd_simp] theorem rstd_varset (s h Ns : α) : Rstd mem .varset [s, h, Ns] = (VarSet mem s h Ns) := rfl
@[rstd_simp] theorem rstd_sat (s dom E Cn Fn Rel sg : α) : Rstd mem .sat [s, dom, E, Cn, Fn, Rel, sg] = (SatM mem s dom E Cn Fn Rel sg) := rfl
@[rstd_simp] theorem rstd_sat_ext (s dom E Cn Fn Rel sg : α) : Rstd mem .sat_ext [s, dom, E, Cn, Fn, Rel, sg] = (SatExtM mem s dom E Cn Fn Rel sg) := rfl
@[rstd_simp] theorem rstd_assign_w (W dom sg : α) : Rstd mem .assign_w [W, dom, sg] = (AssignM mem W dom sg) := rfl
@[rstd_simp] theorem rstd_update_w (W dom sg k a sg2 : α) : Rstd mem .update_w [W, dom, sg, k, a, sg2] = (UpdateM mem W dom sg k a sg2) := rfl
@[rstd_simp] theorem rstd_is_definition (s dom E Cn Fn Rel : α) : Rstd mem .is_definition [s, dom, E, Cn, Fn, Rel] = (IsDefM mem s dom E Cn Fn Rel) := rfl
@[rstd_simp] theorem rstd_param_true (s dom E Cn Fn Rel m : α) : Rstd mem .param_true [s, dom, E, Cn, Fn, Rel, m] = (ParamTrueM mem s dom E Cn Fn Rel m) := rfl
@[rstd_simp] theorem rstd_definable_in (s dom E Cn Fn Rel m : α) : Rstd mem .definable_in [s, dom, E, Cn, Fn, Rel, m] = (DefinableInM mem s dom E Cn Fn Rel m) := rfl
@[rstd_simp] theorem rstd_ordinal (x : α) : Rstd mem .ordinal [x] = (OrdinalM mem x) := rfl
@[rstd_simp] theorem rstd_e_restrict (D E : α) : Rstd mem .e_restrict [D, E] = (ERestrict mem D E) := rfl
@[rstd_simp] theorem rstd_func_on (f K X : α) : Rstd mem .func_on [f, K, X] = (AssignM mem K X f) := rfl
@[rstd_simp] theorem rstd_in_pair_l (X a b : α) : Rstd mem .in_pair_l [X, a, b] = (InPair mem X a b) := rfl
@[rstd_simp] theorem rstd_pure (s h : α) : Rstd mem .pure [s, h] = (Pure mem s h) := rfl
@[rstd_simp] theorem rstd_def_code (n : α) : Rstd mem .def_code [n] = (DefCode mem n) := rfl
@[rstd_simp] theorem rstd_defines (n tau X y : α) : Rstd mem .defines [n, tau, X, y] = (DefinesM mem n tau X y) := rfl
@[rstd_simp] theorem rstd_lex_less (tau tau2 Wg : α) : Rstd mem .lex_less [tau, tau2, Wg] = (LexLess mem tau tau2 Wg) := rfl
@[rstd_simp] theorem rstd_def_less (n tau n2 tau2 Wg : α) : Rstd mem .def_less [n, tau, n2, tau2, Wg] = (DefLess mem n tau n2 tau2 Wg) := rfl
@[rstd_simp] theorem rstd_def_table (X DT : α) : Rstd mem .def_table [X, DT] = (DefTable mem X DT) := rfl
@[rstd_simp] theorem rstd_new_less (a b DT Wg : α) : Rstd mem .new_less [a, b, DT, Wg] = (NewLess mem a b DT Wg) := rfl
@[rstd_simp] theorem rstd_step (X Wg X1 W1 : α) : Rstd mem .step [X, Wg, X1, W1] = (StepM mem X Wg X1 W1) := rfl
@[rstd_simp] theorem rstd_l_order (lam D WL : α) : Rstd mem .l_order [lam, D, WL] = (LOrderM mem lam D WL) := rfl
@[rstd_simp] theorem rstd_formula_code_minus (n : α) : Rstd mem .formula_code_minus [n] = (FormulaCodeMinus mem n) := rfl
@[rstd_simp] theorem rstd_theta_value (Fn m v : α) : Rstd mem .theta_value [Fn, m, v] = (ThetaValue mem Fn m v) := rfl
@[rstd_simp] theorem rstd_least_good (s v D E Cn Fn Rel WL : α) : Rstd mem .least_good [s, v, D, E, Cn, Fn, Rel, WL] = (LeastGood mem s v D E Cn Fn Rel WL) := rfl
@[rstd_simp] theorem rstd_theta_l (D E Cn Fn Rel WL : α) : Rstd mem .theta_l [D, E, Cn, Fn, Rel, WL] = (ThetaLM mem D E Cn Fn Rel WL) := rfl
@[rstd_simp] theorem rstd_numeral10 (v : α) : Rstd mem .numeral10 [v] = (Num mem 10 v) := rfl
@[rstd_simp] theorem rstd_numeral11 (v : α) : Rstd mem .numeral11 [v] = (Num mem 11 v) := rfl
@[rstd_simp] theorem rstd_numeral12 (v : α) : Rstd mem .numeral12 [v] = (Num mem 12 v) := rfl
@[rstd_simp] theorem rstd_dec (i a b : α) : Rstd mem .dec [i, a, b] = (DecM mem i a b) := rfl
@[rstd_simp] theorem rstd_row_shape0 (r : α) : Rstd mem .row_shape0 [r] = (RowShape mem 0 r) := rfl
@[rstd_simp] theorem rstd_row_shape1 (r : α) : Rstd mem .row_shape1 [r] = (RowShape mem 1 r) := rfl
@[rstd_simp] theorem rstd_table_ok (T : α) : Rstd mem .table_ok [T] = (TableOk mem T) := rfl
@[rstd_simp] theorem rstd_cnf_cmp (i k c : α) : Rstd mem .cnf_cmp [i, k, c] = (CnfCmp mem i k c) := rfl
@[rstd_simp] theorem rstd_cnf_lt (i k : α) : Rstd mem .cnf_lt [i, k] = (CnfLt mem i k) := rfl
@[rstd_simp] theorem rstd_omega (w : α) : Rstd mem .omega [w] = (OmegaM mem w) := rfl
@[rstd_simp] theorem rstd_func (f A B : α) : Rstd mem .func [f, A, B] = (FuncM mem f A B) := rfl
@[rstd_simp] theorem rstd_bij (f A B : α) : Rstd mem .bij [f, A, B] = (BijM mem f A B) := rfl
@[rstd_simp] theorem rstd_regular (l : α) : Rstd mem .regular [l] = (RegularM mem l) := rfl
@[rstd_simp] theorem rstd_power_of (a b : α) : Rstd mem .power_of [a, b] = (PowerOf mem a b) := rfl
@[rstd_simp] theorem rstd_strong_limit (l : α) : Rstd mem .strong_limit [l] = (StrongLimitM mem l) := rfl
@[rstd_simp] theorem rstd_inaccessible (l : α) : Rstd mem .inaccessible [l] = (InaccM mem l) := rfl
@[rstd_simp] theorem rstd_o_ok (Of W : α) : Rstd mem .o_ok [Of, W] = (OOk mem Of W) := rfl
@[rstd_simp] theorem rstd_ord_of (i x : α) : Rstd mem .ord_of [i, x] = (OrdOf mem i x) := rfl
@[rstd_simp] theorem rstd_lam_ok (Lf E : α) : Rstd mem .lam_ok [Lf, E] = (LamOk mem Lf E) := rfl
@[rstd_simp] theorem rstd_eps0 (E : α) : Rstd mem .eps0 [E] = (Eps0M mem E) := rfl
@[rstd_simp] theorem rstd_lam_of (b l : α) : Rstd mem .lam_of [b, l] = (LamOf mem b l) := rfl
@[rstd_simp] theorem rstd_vstage (l D : α) : Rstd mem .vstage [l, D] = (VStage mem l D) := rfl
@[rstd_simp] theorem rstd_cn_ok (Cn : α) : Rstd mem .cn_ok [Cn] = (CnOk mem Cn) := rfl
@[rstd_simp] theorem rstd_theta_ok (Th D : α) : Rstd mem .theta_ok [Th, D] = (FuncM mem Th D D) := rfl
@[rstd_simp] theorem rstd_fn_ok (Fn D a SU : α) : Rstd mem .fn_ok [Fn, D, a, SU] = (FnOk mem Fn D a SU) := rfl
@[rstd_simp] theorem rstd_struct_rec (a SU : α) : Rstd mem .struct_rec [a, SU] = (StructRec mem a SU) := rfl
@[rstd_simp] theorem rstd_struct_full (i D E Cn Fn Rel : α) : Rstd mem .struct_full [i, D, E, Cn, Fn, Rel] = (StructFull mem i D E Cn Fn Rel) := rfl
@[rstd_simp] theorem rstd_func_on2 (f K : α) : Rstd mem .func_on2 [f, K] = (FuncOn2 mem f K) := rfl
@[rstd_simp] theorem rstd_struct_table (n ST : α) : Rstd mem .struct_table [n, ST] = (StructTable mem n ST) := rfl
@[rstd_simp] theorem rstd_definable_set (n ST S : α) : Rstd mem .definable_set [n, ST, S] = (DefinableSet mem n ST S) := rfl
@[rstd_simp] theorem rstd_finite_sum (S v : α) : Rstd mem .finite_sum [S, v] = (FiniteSum mem S v) := rfl
@[rstd_simp] theorem rstd_f_val (n v : α) : Rstd mem .f_val [n, v] = (FValM mem n v) := rfl
@[rstd_simp] theorem rstd_iterate10 (a x : α) : Rstd mem .iterate10 [a, x] = (Iterate10 mem a x) := rfl
@[rstd_simp] theorem rstd_lngn (x : α) : Rstd mem .lngn [x] = (LngnM mem x) := rfl
end

section
variable {α : Type} (mem : α → α → Prop) (e : Nat → α)

theorem r1 : List.map e (List.range 1) = [e 0] := rfl
theorem r2 : List.map e (List.range 2) = [e 0, e 1] := rfl
theorem r3 : List.map e (List.range 3) = [e 0, e 1, e 2] := rfl
theorem r4 : List.map e (List.range 4) = [e 0, e 1, e 2, e 3] := rfl
theorem r5 : List.map e (List.range 5) = [e 0, e 1, e 2, e 3, e 4] := rfl
theorem r6 : List.map e (List.range 6) = [e 0, e 1, e 2, e 3, e 4, e 5] := rfl
theorem r8 : List.map e (List.range 8) = [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7] := rfl
theorem r10 : List.map e (List.range 10) = [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9] := rfl
theorem r13 : List.map e (List.range 13) = [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9, e 10, e 11, e 12] := rfl
theorem r7 : List.map e (List.range 7) = [e 0, e 1, e 2, e 3, e 4, e 5, e 6] := rfl

theorem L_triples {t : α} {B : α → α → α → α → Prop} :
    (∀ p, mem p t → ∀ s1, mem s1 p → ∀ q, mem q s1 → ∀ v, mem v s1 → ∀ s2, mem s2 q → ∀ n, mem n s2 →
      ∀ b, mem b s2 → Triple mem p n b v → B p n b v) ↔
      ∀ p, mem p t → ∀ n b v, Triple mem p n b v → B p n b v := by
  constructor
  · intro h p hp n b v ht
    obtain ⟨s1, hs1, q, hq, hv, s2, hs2, hn, hb⟩ := triple_path mem ht
    exact h p hp s1 hs1 q hq v hv s2 hs2 n hn b hb ht
  · intro h p hp _ _ _ _ v _ _ _ n _ b _ ht; exact h p hp n b v ht
theorem L_triple_ex {p n b : α} {B : α → Prop} :
    (∃ s, mem s p ∧ ∃ w, mem w s ∧ Triple mem p n b w ∧ B w) ↔ ∃ w, Triple mem p n b w ∧ B w := by
  constructor
  · rintro ⟨s, _, w, _, ht, hb⟩; exact ⟨w, ht, hb⟩
  · rintro ⟨w, ht, hb⟩
    obtain ⟨q, h1, _⟩ := ht
    obtain ⟨s, hs, _, hw⟩ := pair_dbl mem h1
    exact ⟨s, hs, w, hw, ⟨q, h1, by assumption⟩, hb⟩

theorem L_incert {C i j : α} {B : α → Prop} :
    (∃ p, mem p C ∧ ∃ s1, mem s1 p ∧ ∃ q, mem q s1 ∧ ∃ k, mem k s1 ∧ Triple mem p i j k ∧ B k) ↔
      ∃ p, mem p C ∧ ∃ k, Triple mem p i j k ∧ B k := by
  constructor
  · rintro ⟨p, hp, _, _, _, _, k, _, ht, hb⟩; exact ⟨p, hp, k, ht, hb⟩
  · rintro ⟨p, hp, k, ht, hb⟩
    obtain ⟨s1, hs1, q, hq, hk, _⟩ := triple_path mem ht
    exact ⟨p, hp, s1, hs1, q, hq, k, hk, ht, hb⟩
theorem L_allcert {p : α} {B : α → α → α → Prop} :
    (∃ s1, mem s1 p ∧ ∃ q, mem q s1 ∧ ∃ k, mem k s1 ∧ ∃ s2, mem s2 q ∧ ∃ i, mem i s2 ∧ ∃ j, mem j s2 ∧
      Triple mem p i j k ∧ B i j k) ↔ ∃ i j k, Triple mem p i j k ∧ B i j k := by
  constructor
  · rintro ⟨_, _, _, _, k, _, _, _, i, _, j, _, ht, hb⟩; exact ⟨i, j, k, ht, hb⟩
  · rintro ⟨i, j, k, ht, hb⟩
    obtain ⟨s1, hs1, q, hq, hk, s2, hs2, hi, hj⟩ := triple_path mem ht
    exact ⟨s1, hs1, q, hq, k, hk, s2, hs2, i, hi, j, hj, ht, hb⟩

theorem nn_ex {β : Type} {P : β → Prop} : (¬ ∀ x, ¬ P x) ↔ ∃ x, P x := by
  constructor
  · intro h; exact Classical.byContradiction (fun h' => h (fun x hx => h' ⟨x, hx⟩))
  · rintro ⟨x, hx⟩ h; exact h x hx
theorem n_and_n {A B : Prop} : ¬ (A ∧ ¬ B) ↔ (A → B) := by
  constructor
  · intro h a; exact Classical.byContradiction (fun hb => h ⟨a, hb⟩)
  · intro h ⟨a, hb⟩; exact hb (h a)
theorem n_nand_n {A B : Prop} : ¬ (¬ A ∧ ¬ B) ↔ (A ∨ B) := by
  constructor
  · intro h; exact Classical.byContradiction (fun h' => h ⟨fun a => h' (Or.inl a), fun b => h' (Or.inr b)⟩)
  · rintro (a | b) ⟨ha, hb⟩
    · exact ha a
    · exact hb b

macro "tr_raw" : tactic => `(tactic| simp (config := {decide := true}) only [ev, upd, rstd_simp, r1, r2, r3, r4, r5, r6, r7, r8, r10, r13,
  List.map_cons, List.map_nil, ite_true, ite_false, nn_ex, n_and_n, n_nand_n, Classical.not_not])

theorem L_lookup {t i : α} {B : α → Prop} :
    (∃ q, mem q t ∧ ∃ r, mem r q ∧ ∃ a, mem a r ∧ Pair mem q i a ∧ B a) ↔ ∃ q, mem q t ∧ ∃ a, Pair mem q i a ∧ B a := by
  constructor
  · rintro ⟨q, hq, r, _, a, _, hp, hb⟩; exact ⟨q, hq, a, hp, hb⟩
  · rintro ⟨q, hq, a, hp, hb⟩
    obtain ⟨r, hr, _, ha⟩ := pair_dbl mem hp
    exact ⟨q, hq, r, hr, a, ha, hp, hb⟩
theorem L_allpairs {t : α} {B : α → α → α → Prop} :
    (∀ q, mem q t → ∀ r, mem r q → ∀ i, mem i r → ∀ a, mem a r → Pair mem q i a → B q i a) ↔
      ∀ q, mem q t → ∀ i a, Pair mem q i a → B q i a := by
  constructor
  · intro h q hq i a hp
    obtain ⟨r, hr, hi, ha⟩ := pair_dbl mem hp
    exact h q hq r hr i hi a ha hp
  · intro h q hq r _ i _ a _ hp; exact h q hq i a hp
theorem L_parts {q : α} {B : α → α → Prop} :
    (∃ r, mem r q ∧ ∃ i, mem i r ∧ ∃ a, mem a r ∧ Pair mem q i a ∧ B i a) ↔ ∃ i a, Pair mem q i a ∧ B i a := by
  constructor
  · rintro ⟨r, _, i, _, a, _, hp, hb⟩; exact ⟨i, a, hp, hb⟩
  · rintro ⟨i, a, hp, hb⟩
    obtain ⟨r, hr, hi, ha⟩ := pair_dbl mem hp
    exact ⟨r, hr, i, hi, a, ha, hp, hb⟩
theorem L_first {p v : α} {B : α → Prop} :
    (∃ s, mem s p ∧ ∃ q, mem q s ∧ Pair mem p q v ∧ B q) ↔ ∃ q, Pair mem p q v ∧ B q := by
  constructor
  · rintro ⟨s, _, q, _, hp, hb⟩; exact ⟨q, hp, hb⟩
  · rintro ⟨q, hp, hb⟩
    obtain ⟨s, hs, hq, _⟩ := pair_dbl mem hp
    exact ⟨s, hs, q, hq, hp, hb⟩

end
end Tr
