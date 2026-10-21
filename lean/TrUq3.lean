/-
  一意性（改訂53、その 3）：f_val・iterate10・lngn。

  ・definableSet_unique：struct_table の値は struct_full で決まり、定義可能な自然数の集合 S も決まる。
  ・finiteSum_val：finite_sum の値は Σ{ j ∈ S }（上界 K の取り方によらない）。
  ・fval_unique・iterate10_unique・lngn_unique：LNGN_I を満たす x は高々一つ。
  仮定は、モデルの公理（Zax・hM）と、struct_rec の閉包条件 hC（紙の証明の補題：階数の評価）だけ。
-/
import TrUq2
namespace Tr

open Classical in
/-- psum P N = Σ { j < N : P j }。 -/
noncomputable def psum (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | k + 1 => psum P k + if P k then k else 0

theorem psum_stable (P : Nat → Prop) (N : Nat) (h : ∀ j, P j → j < N) : ∀ k, psum P (N + k) = psum P N := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : N + (k + 1) = (N + k) + 1 := by omega
    rw [e, psum, ih, if_neg (fun hp => absurd (h _ hp) (by omega)), Nat.add_zero]

namespace Model
variable {α : Type} (M : Model α)

theorem funcOn2_dom {f K : α} (h : FuncOn2 M.mem f K) : FuncDom M.mem f K := ⟨h.1, h.2.2⟩

theorem at_transfer {f f' K : α} (hf' : FuncOn2 M.mem f' K) {k : α} (hk : M.mem k K)
    (agree : ∀ x x', M.Look f k x → M.Look f' k x' → x = x') {P : α → Prop} (h : At M.mem f k P) :
    At M.mem f' k P := by
  obtain ⟨x, hl, hx⟩ := (M.at_look _ _ _).mp h
  obtain ⟨x', hl', _⟩ := (M.at_look _ _ _).mp (hf'.2.1 k hk)
  rw [agree x x' hl hl'] at hx
  exact (M.at_look _ _ _).mpr ⟨x', hl', hx⟩

theorem finiteSum_val {S v : α} (h : FiniteSum M.mem S v) :
    ∃ N, (∀ j, M.mem (M.num j) S → j < N) ∧ v = M.num (psum (fun j => M.mem (M.num j) S) N) := by
  obtain ⟨K, hK, hsub, K1, hK1, R, hR, ⟨z, hz, hat0⟩, hstep, hatK⟩ := h
  obtain ⟨N, rfl⟩ := (M.nat_iff K).mp hK
  rw [M.succ_num_iff] at hK1; subst hK1
  have hRd := M.funcOn2_dom hR
  have key : ∀ k, k ≤ N → M.Look R (M.num k) (M.num (psum (fun j => M.mem (M.num j) S) k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [(M.empty_iff z).mp hz] at hat0
      obtain ⟨a, hl, ha⟩ := (M.at_look _ _ _).mp hat0
      rw [(M.empty_iff a).mp ha] at hl; exact hl
    | succ k ih =>
      intro hk
      have hl := ih (by omega)
      have h1 := M.at_val hRd (hstep (M.num k) (M.num_lt (by omega)) (M.num (k + 1)) (M.num_lt (by omega))
        ((M.succ_num_iff k _).mpr rfl)) hl
      obtain ⟨b, hlb, hb1, hb2⟩ := (M.at_look _ _ _).mp h1
      by_cases hkS : M.mem (M.num k) S
      · rw [(M.add_iff _ _ _).mp (hb1 hkS)] at hlb
        simp only [psum, if_pos hkS]; exact hlb
      · rw [hb2 hkS] at hlb
        simp only [psum, if_neg hkS, Nat.add_zero]; exact hlb
  refine ⟨N, fun j hj => M.num_mem_iff.mp (hsub _ hj), ?_⟩
  obtain ⟨a, hl, rfl⟩ := (M.at_look _ _ _).mp hatK
  exact M.look_func hRd hl (key N (Nat.le_refl N))

theorem finiteSum_unique {S v v' : α} (h : FiniteSum M.mem S v) (h' : FiniteSum M.mem S v') : v = v' := by
  obtain ⟨N, hN, rfl⟩ := M.finiteSum_val h
  obtain ⟨N', hN', rfl⟩ := M.finiteSum_val h'
  rcases Nat.le_total N N' with hle | hle
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [psum_stable _ N hN k]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [psum_stable _ N' hN' k]

section Main
variable (Zx : M.Zax) (hM : ∀ x y, M.mem x y → M.H x) (hC : ∀ alpha SU, StructRec M.mem alpha SU → M.SUClosed SU)
include Zx hM hC

theorem structTable_agree {n ST ST' : α} (h : StructTable M.mem n ST) (h' : StructTable M.mem n ST') :
    ∀ i, M.mem i n → ∀ x x', M.Look ST i x → M.Look ST' i x' → x = x' := by
  intro i hi x x' hl hl'
  have hp := M.at_val (M.funcOn2_dom h.1) (h.2 i hi) hl
  have hp' := M.at_val (M.funcOn2_dom h'.1) (h'.2 i hi) hl'
  exact M.structParts_eq hM hp hp' (fun _ _ _ _ _ _ _ _ _ _ _ hP hP' => M.structFull_unique Zx hM hC hP hP')

theorem definableSet_unique {n ST ST' S S' : α} (h : StructTable M.mem n ST) (h' : StructTable M.mem n ST')
    (hS : DefinableSet M.mem n ST S) (hS' : DefinableSet M.mem n ST' S') : S = S' := by
  have ag := M.structTable_agree Zx hM hC h h'
  apply M.ext; intro m
  rw [hS m, hS' m]
  constructor
  · rintro ⟨hn, i, hi, hat⟩
    exact ⟨hn, i, hi, M.at_transfer h'.1 hi (ag i hi) hat⟩
  · rintro ⟨hn, i, hi, hat⟩
    exact ⟨hn, i, hi, M.at_transfer h.1 hi (fun x x' h1 h2 => (ag i hi x' x h2 h1).symm) hat⟩

theorem fval_unique {n v v' : α} (h : FValM M.mem n v) (h' : FValM M.mem n v') : v = v' := by
  obtain ⟨ST, hST, S, hS, hsum⟩ := h
  obtain ⟨ST', hST', S', hS', hsum'⟩ := h'
  have e := M.definableSet_unique Zx hM hC hST hST' hS hS'
  rw [← e] at hsum'
  exact M.finiteSum_unique hsum hsum'

theorem iterate10_unique {a x x' : α} (h : Iterate10 M.mem a x) (h' : Iterate10 M.mem a x') : x = x' := by
  obtain ⟨t, ht, t1, ht1, G, hG, ⟨z, hz, hz0⟩, hstep, hatx⟩ := h
  obtain ⟨t', ht', t1', ht1', G', hG', ⟨z', hz', hz0'⟩, hstep', hatx'⟩ := h'
  rw [M.num_iff] at ht ht'; subst ht; subst ht'
  rw [M.succ_num_iff] at ht1 ht1'; subst ht1; subst ht1'
  rw [(M.empty_iff z).mp hz] at hz0
  rw [(M.empty_iff z').mp hz'] at hz0'
  have hGd := M.funcOn2_dom hG
  have hGd' := M.funcOn2_dom hG'
  have key : ∀ k, k ≤ 10 → ∀ y y', M.Look G (M.num k) y → M.Look G' (M.num k) y' → y = y' := by
    intro k
    induction k with
    | zero =>
      intro _ y y' hl hl'
      rw [M.at_val hGd hz0 hl, M.at_val hGd' hz0' hl']
    | succ k ih =>
      intro hk y y' hl hl'
      obtain ⟨u, hu, _⟩ := (M.at_look _ _ _).mp (hG.2.1 (M.num k) (M.num_lt (by omega)))
      obtain ⟨u', hu', _⟩ := (M.at_look _ _ _).mp (hG'.2.1 (M.num k) (M.num_lt (by omega)))
      have e := ih (by omega) u u' hu hu'
      have hs := hstep (M.num k) (M.num_lt (by omega)) (M.num (k + 1)) (M.num_lt (by omega))
        ((M.succ_num_iff k _).mpr rfl)
      have hs' := hstep' (M.num k) (M.num_lt (by omega)) (M.num (k + 1)) (M.num_lt (by omega))
        ((M.succ_num_iff k _).mpr rfl)
      have f1 := M.at_val hGd (M.at_val hGd hs hu) hl
      have f2 := M.at_val hGd' (M.at_val hGd' hs' hu') hl'
      rw [← e] at f2
      exact M.fval_unique Zx hM hC f1 f2
  obtain ⟨y, hl, rfl⟩ := (M.at_look _ _ _).mp hatx
  obtain ⟨y', hl', rfl⟩ := (M.at_look _ _ _).mp hatx'
  exact key 10 (Nat.le_refl 10) _ _ hl hl'

/-- LNGN_I を満たす x は高々一つ。 -/
theorem lngn_unique {x x' : α} (h : LngnM M.mem x) (h' : LngnM M.mem x') : x = x' := by
  obtain ⟨a, ⟨n12, h12, n10, h10, hh⟩, hi⟩ := h
  obtain ⟨a', ⟨n12', h12', n10', h10', hh'⟩, hi'⟩ := h'
  rw [M.num_iff] at h12 h10 h12' h10'
  subst h12; subst h10; subst h12'; subst h10'
  obtain ⟨m, e1, rfl⟩ := (M.hyper_iff 12 10 _ a (Or.inl (by decide))).mp hh
  obtain ⟨m', e1', rfl⟩ := (M.hyper_iff 12 10 _ a' (Or.inl (by decide))).mp hh'
  have em : m = m' := (M.num_inj e1).symm.trans (M.num_inj e1')
  subst em
  exact M.iterate10_unique Zx hM hC hi hi'

/-- 生成した最終式 φ そのもの（full_lngn）について：M で φ(x) を満たす x は高々一つ。 -/
theorem full_lngn_unique (Rr : Nm → List α → Prop) (e e' : Nat → α)
    (h : ev M.mem Rr full_lngn e) (h' : ev M.mem Rr full_lngn e') : e 0 = e' 0 := by
  rw [mean_full_lngn] at h h'
  have h1 : LngnM M.mem (e 0) := h
  have h2 : LngnM M.mem (e' 0) := h'
  exact M.lngn_unique Zx hM hC h1 h2

end Main
end Model

#print axioms Model.finiteSum_unique
#print axioms Model.fval_unique
#print axioms Model.iterate10_unique
#print axioms Model.lngn_unique
#print axioms Model.full_lngn_unique
end Tr
