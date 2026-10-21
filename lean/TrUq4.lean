/-
  一意性（改訂61、その 4）：閉包条件 hC（補題 R）の Lean による証明。

  ・inacc_lim：到達不能な λ では、β ∈ λ なら β+1 ∈ λ（Cantor の対角線論法と強極限性による）。
  ・vs_*：λ が極限の V の段階 D = V_λ は、空集合・数・順序対・有限列・記号の 4 つ組について閉じている。
  ・struct_closed：struct_rec を満たす任意の表 SU は SUClosed（各段の D は 0 を含み、
    x ∈ D が順序数で x ∈ γ なら SU(x) ∈ D）。
  ・lngn_unique'・full_lngn_unique'：仮定 hC なしの一意性。
-/
import TrUq3
namespace Tr

namespace Model
variable {α : Type} (M : Model α)

/-! ### 順序数の後者と、到達不能基数の極限性 -/

theorem succ_ex (Zx : M.Zax) {β : α} (hH : M.H β) : ∃ U, Succ M.mem β U := by
  obtain ⟨s1, hs1H, hs1⟩ := M.fin [β] (fun x hx => by rw [List.mem_singleton.mp hx]; exact hH)
  obtain ⟨P, hPH, hP⟩ := M.fin [β, s1] (fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hH
    · rw [List.mem_singleton.mp hx]; exact hs1H)
  obtain ⟨U, _, hU⟩ := Zx.union P hPH
  refine ⟨U, fun u => ?_⟩
  rw [hU]
  constructor
  · rintro ⟨y, hy, hu⟩
    rcases List.mem_cons.mp ((hP y).mp hy) with rfl | hy
    · exact Or.inl hu
    · rw [List.mem_singleton.mp hy] at hu
      exact Or.inr (List.mem_singleton.mp ((hs1 u).mp hu))
  · rintro (hu | rfl)
    · exact ⟨β, (hP β).mpr (List.mem_cons_self _ _), hu⟩
    · exact ⟨s1, (hP s1).mpr (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        (hs1 _).mpr (List.mem_singleton_self _)⟩

theorem succ_ord {β U : α} (hβ : OrdinalM M.mem β) (hU : Succ M.mem β U) : OrdinalM M.mem U := by
  refine ⟨fun z hz u hu => ?_, fun z hz => ?_⟩
  · rcases (hU z).mp hz with hz | rfl
    · exact (hU u).mpr (Or.inl (hβ.1 z hz u hu))
    · exact (hU u).mpr (Or.inl hu)
  · rcases (hU z).mp hz with hz | rfl
    · exact hβ.2 z hz
    · exact hβ.1

/-- Cantor：P(β) から β の部分集合への単射はない。 -/
theorem cantor (Zx : M.Zax) {β pb g h : α} (hH : M.H β) (hpb : PowerOf M.mem pb β) (hbij : BijM M.mem h pb g)
    (hsub : ∀ u, M.mem u g → M.mem u β) : False := by
  obtain ⟨Z, _, hZ⟩ := Zx.sep β (fun u => ∃ z, At M.mem h z (fun v => v = u) ∧ ¬ M.mem u z) hH
  have hZpb : M.mem Z pb := (hpb.2 Z).mpr (fun u hu => ((hZ u).mp hu).1)
  obtain ⟨q, hq, c, hpq, hcg⟩ := hbij.1.2.1 Z hZpb
  have hcβ := hsub c hcg
  by_cases hc : M.mem c Z
  · obtain ⟨_, z, ⟨q', hq', c', hpq', ec⟩, hcz⟩ := (hZ c).mp hc
    rw [ec] at hpq'
    have ez : z = Z := hbij.2.2 q' hq' _ _ hpq' q hq _ _ hpq rfl
    rw [ez] at hcz; exact hcz hc
  · exact hc ((hZ c).mpr ⟨hcβ, Z, ⟨q, hq, c, hpq, rfl⟩, hc⟩)

/-- 到達不能な λ は後者について閉じている。 -/
theorem inacc_lim (Zx : M.Zax) (hM : ∀ x y, M.mem x y → M.H x) {lam : α} (hi : InaccM M.mem lam) :
    ∀ β, M.mem β lam → ∃ β1, Succ M.mem β β1 ∧ M.mem β1 lam := by
  intro β hβ
  have hord := hi.1
  have hβo := M.ord_mem hord hβ
  have hH := hM β lam hβ
  obtain ⟨pb, hpb, g, hg, h, hbij⟩ := hi.2.2.2 β hβ
  have hgo := M.ord_mem hord hg
  have hβg : M.mem β g := by
    rcases M.ord_trich β g hβo hgo with h1 | h1 | h1
    · exact h1
    · exact (M.cantor Zx hH hpb hbij (fun u hu => by rw [h1]; exact hu)).elim
    · exact (M.cantor Zx hH hpb hbij (fun u hu => hβo.1 g h1 u hu)).elim
  obtain ⟨U, hU⟩ := M.succ_ex Zx hH
  have hUo := M.succ_ord hβo hU
  refine ⟨U, hU, ?_⟩
  rcases M.ord_trich U g hUo hgo with h1 | h1 | h1
  · exact hord.1 g hg U h1
  · rw [h1]; exact hg
  · exfalso
    rcases (hU g).mp h1 with h2 | h2
    · exact M.mem_asymm h2 hβg
    · rw [h2] at hβg; exact M.mem_irrefl _ hβg

/-! ### V の段階の表 -/

/-- 二つの V の段階の表は、共通の定義域で一致する。 -/
theorem vtab_agree {lam l1 R lam' l1' R' : α}
    (hord : OrdinalM M.mem lam) (hl1 : Succ M.mem lam l1) (hf : FuncDom M.mem R l1)
    (hall : ∀ g, M.mem g l1 → At M.mem R g (fun X => VVal M.mem R g X))
    (hord' : OrdinalM M.mem lam') (hl1' : Succ M.mem lam' l1') (hf' : FuncDom M.mem R' l1')
    (hall' : ∀ g, M.mem g l1' → At M.mem R' g (fun X => VVal M.mem R' g X)) :
    ∀ g, M.mem g l1 → M.mem g l1' → ∀ X X', M.Look R g X → M.Look R' g X' → X = X' := by
  have tr : ∀ {lam l1 : α}, OrdinalM M.mem lam → Succ M.mem lam l1 → ∀ g, M.mem g l1 → ∀ w, M.mem w g → M.mem w l1 := by
    intro lam l1 hord hl1 g hg w hw
    rcases (hl1 g).mp hg with hg | rfl
    · exact (hl1 w).mpr (Or.inl (hord.1 g hg w hw))
    · exact (hl1 w).mpr (Or.inl hw)
  intro g
  induction g using M.wf.induction with
  | _ g ih =>
  intro hg hg' X X' hl hl'
  have hv := M.at_val (P := fun X => VVal M.mem R g X) hf (hall g hg) hl
  have hv' := M.at_val (P := fun X => VVal M.mem R' g X) hf' (hall' g hg') hl'
  by_cases he : Empty M.mem g
  · exact M.empty_eq (hv.1 he) (hv'.1 he)
  by_cases hsu : IsSucc M.mem g
  · obtain ⟨w, hw, hsw⟩ := hsu
    obtain ⟨Y, hlY, hpY⟩ := (M.at_look _ _ _).mp (hv.2.1 w hw hsw)
    obtain ⟨Y', hlY', hpY'⟩ := (M.at_look _ _ _).mp (hv'.2.1 w hw hsw)
    have e := ih w hw (tr hord hl1 g hg w hw) (tr hord' hl1' g hg' w hw) Y Y' hlY hlY'
    rw [← e] at hpY'
    exact M.powerOf_unique hpY hpY'
  · obtain ⟨u1, u2⟩ := hv.2.2 ⟨he, hsu⟩
    obtain ⟨u1', u2'⟩ := hv'.2.2 ⟨he, hsu⟩
    apply M.ext; intro y; constructor
    · intro hy
      obtain ⟨b, hb, hat⟩ := u1 y hy
      obtain ⟨Y, hlY, hyY⟩ := (M.at_look _ _ _).mp hat
      obtain ⟨Y', hlY', hsub⟩ := (M.at_look _ _ _).mp (u2' b hb)
      rw [ih b hb (tr hord hl1 g hg b hb) (tr hord' hl1' g hg' b hb) Y Y' hlY hlY'] at hyY
      exact hsub y hyY
    · intro hy
      obtain ⟨b, hb, hat⟩ := u1' y hy
      obtain ⟨Y', hlY', hyY⟩ := (M.at_look _ _ _).mp hat
      obtain ⟨Y, hlY, hsub⟩ := (M.at_look _ _ _).mp (u2 b hb)
      rw [← ih b hb (tr hord hl1 g hg b hb) (tr hord' hl1' g hg' b hb) Y Y' hlY hlY'] at hyY
      exact hsub y hyY

section Stage
variable {lam l1 R D : α} (hord : OrdinalM M.mem lam) (hl1 : Succ M.mem lam l1) (hf : FuncDom M.mem R l1)
  (hall : ∀ g, M.mem g l1 → At M.mem R g (fun X => VVal M.mem R g X)) (hD : M.Look R lam D)
  (hlim : ∀ β, M.mem β lam → ∃ β1, Succ M.mem β β1 ∧ M.mem β1 lam) (hne : ∃ β, M.mem β lam)
include hord hl1 hf hall hD hlim hne

theorem vs_l1tr {g w : α} (hg : M.mem g l1) (hw : M.mem w g) : M.mem w l1 := by
  rcases (hl1 g).mp hg with hg | rfl
  · exact (hl1 w).mpr (Or.inl (hord.1 g hg w hw))
  · exact (hl1 w).mpr (Or.inl hw)

theorem vs_val {g : α} (hg : M.mem g l1) : ∃ X, M.Look R g X := by
  obtain ⟨X, hl, _⟩ := (M.at_look _ _ _).mp (hall g hg)
  exact ⟨X, hl⟩

theorem vs_tm : ∀ γ, M.mem γ l1 → ∀ X, M.Look R γ X →
    Trans M.mem X ∧ ∀ β, M.mem β γ → ∀ Y, M.Look R β Y → ∀ y, M.mem y Y → M.mem y X := by
  intro γ
  induction γ using M.wf.induction with
  | _ γ ih =>
  intro hγ X hl
  have hv := M.at_val (P := fun X => VVal M.mem R γ X) hf (hall γ hγ) hl
  by_cases he : Empty M.mem γ
  · have hX := hv.1 he
    exact ⟨fun z hz => absurd hz (hX z), fun β hβ => absurd hβ (he β)⟩
  by_cases hs : IsSucc M.mem γ
  · obtain ⟨δ, hδ, hsδ⟩ := hs
    have hδl := M.vs_l1tr hord hl1 hf hall hD hlim hne hγ hδ
    obtain ⟨Yδ, hlδ⟩ := M.vs_val hord hl1 hf hall hD hlim hne hδl
    have hpow : PowerOf M.mem X Yδ := M.at_val (P := fun Y => PowerOf M.mem X Y) hf (hv.2.1 δ hδ hsδ) hlδ
    obtain ⟨htδ, hmδ⟩ := ih δ hδ hδl Yδ hlδ
    have inX : ∀ y, M.mem y Yδ → M.mem y X := fun y hy => (hpow.2 y).mpr (fun u hu => htδ y hy u hu)
    refine ⟨fun z hz u hu => inX u (((hpow.2 z).mp hz) u hu), fun β hβ Y hlβ y hy => ?_⟩
    rcases (hsδ β).mp hβ with hβ | hβ
    · exact inX y (hmδ β hβ Y hlβ y hy)
    · rw [hβ] at hlβ; rw [M.look_func hf hlβ hlδ] at hy; exact inX y hy
  · obtain ⟨u1, u2⟩ := hv.2.2 ⟨he, hs⟩
    refine ⟨fun z hz u hu => ?_, fun β hβ Y hlβ y hy => ?_⟩
    · obtain ⟨b, hb, hat⟩ := u1 z hz
      obtain ⟨Yb, hlb, hzY⟩ := (M.at_look _ _ _).mp hat
      have hbl := M.vs_l1tr hord hl1 hf hall hD hlim hne hγ hb
      have hu' := (ih b hb hbl Yb hlb).1 z hzY u hu
      exact M.at_val (P := fun Y => ∀ y, M.mem y Y → M.mem y X) hf (u2 b hb) hlb u hu'
    · exact M.at_val (P := fun Y => ∀ y, M.mem y Y → M.mem y X) hf (u2 β hβ) hlβ y hy

theorem vs_memD (z : α) : M.mem z D ↔ ∃ β Y, M.mem β lam ∧ M.Look R β Y ∧ M.mem z Y := by
  have hlam : M.mem lam l1 := (hl1 lam).mpr (Or.inr rfl)
  have hv := M.at_val (P := fun X => VVal M.mem R lam X) hf (hall lam hlam) hD
  have hnE : ¬ Empty M.mem lam := fun he => let ⟨β, hβ⟩ := hne; he β hβ
  have hnS : ¬ IsSucc M.mem lam := by
    rintro ⟨w, hw, hsw⟩
    obtain ⟨w1, hs1, hw1⟩ := hlim w hw
    have e : w1 = lam := M.ext _ _ (fun u => by rw [hs1 u, hsw u])
    rw [e] at hw1; exact M.mem_irrefl _ hw1
  obtain ⟨u1, u2⟩ := hv.2.2 ⟨hnE, hnS⟩
  constructor
  · intro hz
    obtain ⟨b, hb, hat⟩ := u1 z hz
    obtain ⟨Y, hl, hzY⟩ := (M.at_look _ _ _).mp hat
    exact ⟨b, Y, hb, hl, hzY⟩
  · rintro ⟨b, Y, hb, hl, hzY⟩
    exact M.at_val (P := fun Y => ∀ y, M.mem y Y → M.mem y D) hf (u2 b hb) hl z hzY

/-- β < λ の段 R(β) の部分集合は D に属する。 -/
theorem vs_up {β Y z : α} (hβ : M.mem β lam) (hl : M.Look R β Y) (hz : ∀ u, M.mem u z → M.mem u Y) :
    M.mem z D := by
  obtain ⟨β1, hs1, hβ1⟩ := hlim β hβ
  have h1 : M.mem β1 l1 := (hl1 β1).mpr (Or.inl hβ1)
  obtain ⟨X, hlX⟩ := M.vs_val hord hl1 hf hall hD hlim hne h1
  have hv := M.at_val (P := fun X => VVal M.mem R β1 X) hf (hall β1 h1) hlX
  have hp : PowerOf M.mem X Y :=
    M.at_val (P := fun Y => PowerOf M.mem X Y) hf (hv.2.1 β ((hs1 β).mpr (Or.inr rfl)) hs1) hl
  exact (M.vs_memD hord hl1 hf hall hD hlim hne z).mpr ⟨β1, X, hβ1, hlX, (hp.2 z).mpr hz⟩

theorem vs_join {β β' Y Y' : α} (hβ : M.mem β lam) (hβ' : M.mem β' lam) (hl : M.Look R β Y) (hl' : M.Look R β' Y') :
    ∃ γ Z, M.mem γ lam ∧ M.Look R γ Z ∧ (∀ y, M.mem y Y → M.mem y Z) ∧ (∀ y, M.mem y Y' → M.mem y Z) := by
  have l1of : ∀ b, M.mem b lam → M.mem b l1 := fun b hb => (hl1 b).mpr (Or.inl hb)
  rcases M.ord_trich β β' (M.ord_mem hord hβ) (M.ord_mem hord hβ') with h | h | h
  · exact ⟨β', Y', hβ', hl',
      (M.vs_tm hord hl1 hf hall hD hlim hne β' (l1of β' hβ') Y' hl').2 β h Y hl, fun y hy => hy⟩
  · rw [h] at hl
    rw [M.look_func hf hl' hl]
    exact ⟨β', Y, hβ', hl, fun y hy => hy, fun y hy => hy⟩
  · exact ⟨β, Y, hβ, hl, fun y hy => hy,
      (M.vs_tm hord hl1 hf hall hD hlim hne β (l1of β hβ) Y hl).2 β' h Y' hl'⟩

theorem vs_boundL (l : List α) (hl : ∀ a, a ∈ l → M.mem a D) :
    ∃ β Y, M.mem β lam ∧ M.Look R β Y ∧ ∀ a, a ∈ l → M.mem a Y := by
  induction l with
  | nil =>
    obtain ⟨β, hβ⟩ := id hne
    obtain ⟨Y, hlY⟩ := M.vs_val hord hl1 hf hall hD hlim hne ((hl1 β).mpr (Or.inl hβ))
    exact ⟨β, Y, hβ, hlY, fun a ha => absurd ha (List.not_mem_nil a)⟩
  | cons a l ih =>
    obtain ⟨β, Y, hβ, hlY, hY⟩ := ih (fun b hb => hl b (List.mem_cons_of_mem a hb))
    obtain ⟨β', Y', hβ', hlY', haY⟩ := (M.vs_memD hord hl1 hf hall hD hlim hne a).mp (hl a (List.mem_cons_self a l))
    obtain ⟨γ, Z, hγ, hlZ, s1, s2⟩ := M.vs_join hord hl1 hf hall hD hlim hne hβ hβ' hlY hlY'
    refine ⟨γ, Z, hγ, hlZ, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with hb | hb
    · rw [hb]; exact s2 a haY
    · exact s1 b (hY b hb)

/-- 元がリスト l に含まれ、l の元がすべて D に属するなら、D に属する。 -/
theorem vs_subL {z : α} (l : List α) (hz : ∀ u, M.mem u z → u ∈ l) (hl : ∀ a, a ∈ l → M.mem a D) :
    M.mem z D := by
  obtain ⟨β, Y, hβ, hlY, hY⟩ := M.vs_boundL hord hl1 hf hall hD hlim hne l hl
  exact M.vs_up hord hl1 hf hall hD hlim hne hβ hlY (fun u hu => hY u (hz u hu))

theorem vs_empty {z : α} (hz : Empty M.mem z) : M.mem z D :=
  M.vs_subL hord hl1 hf hall hD hlim hne [] (fun u hu => absurd hu (hz u)) (fun a ha => absurd ha (List.not_mem_nil a))

theorem vs_num (n : Nat) : M.mem (M.num n) D := by
  have key : ∀ k, ∀ n, n < k → M.mem (M.num n) D := by
    intro k
    induction k with
    | zero => intro n hn; omega
    | succ k ihk =>
    intro n hn
    apply M.vs_subL hord hl1 hf hall hD hlim hne ((List.range n).map M.num)
    · intro u hu
      obtain ⟨m, hm, rfl⟩ := (M.num_mem n u).mp hu
      exact List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩
    · intro a ha
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ha
      exact ihk m (by have := List.mem_range.mp hm; omega)
  exact key (n + 1) n (by omega)

theorem vs_pair {p a b : α} (hp : Pair M.mem p a b) (ha : M.mem a D) (hb : M.mem b D) : M.mem p D := by
  obtain ⟨hall', ⟨S0, _, hsS⟩, ⟨T0, _, hdT⟩⟩ := hp
  have hSD : M.mem S0 D := M.vs_subL hord hl1 hf hall hD hlim hne [a]
    (fun u hu => by rw [hsS.2 u hu]; exact List.mem_singleton_self a)
    (fun x hx => by rw [List.mem_singleton.mp hx]; exact ha)
  have hTD : M.mem T0 D := M.vs_subL hord hl1 hf hall hD hlim hne [a, b]
    (fun u hu => by
      rcases hdT.2.2 u hu with e | e
      · rw [e]; exact List.mem_cons_self _ _
      · rw [e]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (fun x hx => by
      rcases List.mem_cons.mp hx with e | hx
      · rw [e]; exact ha
      · rw [List.mem_singleton.mp hx]; exact hb)
  apply M.vs_subL hord hl1 hf hall hD hlim hne [S0, T0] _ (fun x hx => by
    rcases List.mem_cons.mp hx with e | hx
    · rw [e]; exact hSD
    · rw [List.mem_singleton.mp hx]; exact hTD)
  intro s hs
  rcases hall' s hs with hss | hsd
  · have e : s = S0 := M.ext _ _ (fun x => ⟨fun h => by rw [hss.2 x h]; exact hsS.1,
      fun h => by rw [hsS.2 x h]; exact hss.1⟩)
    rw [e]; exact List.mem_cons_self _ _
  · have e : s = T0 := M.ext _ _ (fun x => ⟨fun h => by
        rcases hsd.2.2 x h with e | e
        · rw [e]; exact hdT.1
        · rw [e]; exact hdT.2.1,
      fun h => by
        rcases hdT.2.2 x h with e | e
        · rw [e]; exact hsd.1
        · rw [e]; exact hsd.2.1⟩)
    rw [e]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

open Classical in
theorem vs_seq {z : α} (n : Nat) (A B : Nat → α) (hz : ∀ u, M.mem u z → ∃ i, i < n ∧ Pair M.mem u (A i) (B i))
    (hA : ∀ i, i < n → M.mem (A i) D) (hB : ∀ i, i < n → M.mem (B i) D) : M.mem z D := by
  let pick : Nat → α := fun i => if h : ∃ u, M.mem u z ∧ Pair M.mem u (A i) (B i) then Classical.choose h else A i
  apply M.vs_subL hord hl1 hf hall hD hlim hne ((List.range n).map pick)
  · intro u hu
    obtain ⟨i, hi, hp⟩ := hz u hu
    have hex : ∃ u, M.mem u z ∧ Pair M.mem u (A i) (B i) := ⟨u, hu, hp⟩
    have e : pick i = u := by
      simp only [pick, dif_pos hex]
      exact M.pair_ext (Classical.choose_spec hex).2 hp
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, e⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    by_cases hex : ∃ u, M.mem u z ∧ Pair M.mem u (A i) (B i)
    · simp only [pick, dif_pos hex]
      exact M.vs_pair hord hl1 hf hall hD hlim hne (Classical.choose_spec hex).2 (hA i hi') (hB i hi')
    · simp only [pick, dif_neg hex]; exact hA i hi'

theorem vs_tuple {t : α} (ht : Tuple4 M.mem t) : M.mem t D := by
  obtain ⟨g, hg⟩ := (M.tuple4_iff t).mp ht
  exact M.vs_seq hord hl1 hf hall hD hlim hne 4 M.num (fun i => M.num (g i)) hg.1
    (fun i _ => M.vs_num hord hl1 hf hall hD hlim hne i) (fun i _ => M.vs_num hord hl1 hf hall hD hlim hne _)

theorem vs_repL {w : α} {l : List α} (hw : M.RepL w l) (hl : ∀ a, a ∈ l → M.mem a D) : M.mem w D := by
  apply M.vs_seq hord hl1 hf hall hD hlim hne l.length M.num (fun i => (l.get? i).getD (M.num 0))
  · intro u hu
    obtain ⟨i, a, hi, hp⟩ := hw.1 u hu
    refine ⟨i, get?_lt hi, ?_⟩
    simp only [hi, Option.getD_some]; exact hp
  · intro i _; exact M.vs_num hord hl1 hf hall hD hlim hne i
  · intro i hi
    obtain ⟨a, ha⟩ := get?_ex hi
    simp only [ha, Option.getD_some]
    exact hl a (List.get?_mem ha)

end Stage

/-! ### 閉包条件 -/

theorem lamOf_inacc {b l : α} (h : LamOf M.mem b l) : InaccM M.mem l := by
  obtain ⟨E, _, Lf, hL, hat⟩ := h
  obtain ⟨v, hl, rfl⟩ := (M.at_look _ _ _).mp hat
  exact (M.at_val (P := fun lam => InaccM M.mem lam ∧ (∀ g, M.mem g b → At M.mem Lf g (fun lg => M.mem lg lam)) ∧
    ∀ mu, M.mem mu lam → InaccM M.mem mu → ∃ g, M.mem g b ∧ At M.mem Lf g (fun lg => M.mem mu lg ∨ mu = lg))
    hL.1 (hL.2 b (M.look_dom hL.1 hl)) hl).1

theorem lamOf_lt {y g l l' : α} (hy : M.mem y g) (h : LamOf M.mem g l) (h' : LamOf M.mem y l') : M.mem l' l := by
  obtain ⟨E, hE, Lf, hL, hat⟩ := h
  obtain ⟨E', hE', Lf', hL', hat'⟩ := h'
  have e := M.eps0_unique hE hE'
  rw [← e] at hL'
  obtain ⟨v, hl, rfl⟩ := (M.at_look _ _ _).mp hat
  obtain ⟨v', hl', rfl⟩ := (M.at_look _ _ _).mp hat'
  have hgE := M.look_dom hL.1 hl
  have hyE := M.look_dom hL'.1 hl'
  obtain ⟨_, hab, _⟩ := M.at_val (P := fun lam => InaccM M.mem lam ∧ (∀ g', M.mem g' g → At M.mem Lf g' (fun lg => M.mem lg lam)) ∧
    ∀ mu, M.mem mu lam → InaccM M.mem mu → ∃ g', M.mem g' g ∧ At M.mem Lf g' (fun lg => M.mem mu lg ∨ mu = lg))
    hL.1 (hL.2 g hgE) hl
  obtain ⟨w, hlw, hw⟩ := (M.at_look _ _ _).mp (hab y hy)
  rw [M.lamOk_unique hL' hL (M.eps0_trans hE) y hyE _ _ hl' hlw]; exact hw

theorem structParts_mono {x : α} {P Q : α → α → α → α → α → Prop} (h : StructParts M.mem x P)
    (hpq : ∀ D E Cn Fn Rel, P D E Cn Fn Rel → Q D E Cn Fn Rel) : StructParts M.mem x Q := by
  obtain ⟨de, rest, hp, D, E, hde, Cn, fr, hrest, Fn, Rel, hfr, hP⟩ := h
  exact ⟨de, rest, hp, D, E, hde, Cn, fr, hrest, Fn, Rel, hfr, hpq _ _ _ _ _ hP⟩

section Closed
variable (Zx : M.Zax) (hM : ∀ x y, M.mem x y → M.H x)
include Zx hM

/-- 段 y の成分は、どれも D′ = V_{λ_y} の部分集合（Rel は空）。 -/
theorem level_sub {SU y D E Cn Fn lam l1 R : α} (hE : ERestrict M.mem D E) (hCn : CnOk M.mem Cn)
    (hFn : FnOk M.mem Fn D y SU)
    (hU : ∀ x s, M.mem x D → OrdinalM M.mem x → M.mem x y → At M.mem SU x (fun s' => s' = s) → M.mem s D)
    (hord : OrdinalM M.mem lam) (hl1 : Succ M.mem lam l1) (hf : FuncDom M.mem R l1)
    (hall : ∀ g, M.mem g l1 → At M.mem R g (fun X => VVal M.mem R g X)) (hD : M.Look R lam D)
    (hlim : ∀ β, M.mem β lam → ∃ β1, Succ M.mem β β1 ∧ M.mem β1 lam) (hne : ∃ β, M.mem β lam) :
    (∀ q, M.mem q E → M.mem q D) ∧ (∀ q, M.mem q Cn → M.mem q D) ∧ (∀ q, M.mem q Fn → M.mem q D) := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨a, b, hp, ha, hb, _⟩ := hE.1 q hq
    exact M.vs_pair hord hl1 hf hall hD hlim hne hp ha hb
  · obtain ⟨t, v, hp, ht, _, hv⟩ := hCn.1 q hq
    exact M.vs_pair hord hl1 hf hall hD hlim hne hp (M.vs_tuple hord hl1 hf hall hD hlim hne ht)
      (M.vs_empty hord hl1 hf hall hD hlim hne hv)
  · obtain ⟨tw, v, hp, t, w, hp2, ht4, hcase⟩ := hFn.1 q hq
    have htD := M.vs_tuple hord hl1 hf hall hD hlim hne ht4
    have hsing : ∀ x, M.mem x D → SingSeq M.mem w x → M.mem w D := fun x hx hs =>
      M.vs_repL hord hl1 hf hall hD hlim hne ((M.singSeq_iff w x).mp hs)
        (fun a ha => by rw [List.mem_singleton.mp ha]; exact hx)
    have hwv : M.mem w D ∧ M.mem v D := by
      rcases hcase with (⟨_, har, hv⟩ | ⟨_, x, hx, hsx, huv⟩) | ⟨_, x, hx, hsx, hv⟩
      · obtain ⟨g4, hg4⟩ := (M.tuple4_iff t).mp ht4
        rw [M.comp_iff hg4 (by decide)] at har
        obtain ⟨l, hrep, _, hlD⟩ := M.repL_of_seqWith har
        exact ⟨M.vs_repL hord hl1 hf hall hD hlim hne hrep hlD, M.vs_empty hord hl1 hf hall hD hlim hne hv⟩
      · refine ⟨hsing x hx hsx, ?_⟩
        rcases huv with ⟨ho, hxy, hat⟩ | ⟨_, he⟩
        · exact hU x v hx ho hxy hat
        · exact M.vs_empty hord hl1 hf hall hD hlim hne he
      · exact ⟨hsing x hx hsx, hv⟩
    have htw := M.vs_pair hord hl1 hf hall hD hlim hne hp2 htD hwv.1
    exact M.vs_pair hord hl1 hf hall hD hlim hne hp htw hwv.2

/-- 補題 R（Lean 版）：struct_rec を満たす任意の表は閉包条件を満たす。 -/
theorem struct_closed : ∀ alpha SU, StructRec M.mem alpha SU → M.SUClosed SU := by
  intro alpha SU hsr
  obtain ⟨a1, _, hf, hall⟩ := hsr
  unfold SUClosed
  intro g
  induction g using M.wf.induction with
  | _ g ih =>
  intro x hl
  have hg := M.look_dom hf hl
  have hP := M.at_val (P := fun x => StructParts M.mem x (fun D E Cn Fn Rel => LevelM M.mem SU g D E Cn Fn Rel))
    hf (hall g hg) hl
  refine M.structParts_mono hP (fun D E Cn Fn Rel hlev => ?_)
  obtain ⟨lam, hlam, ⟨hord, l1, hl1, R, hfR, hallR, hatD⟩, _⟩ := hlev
  have hi := M.lamOf_inacc hlam
  obtain ⟨D0, hD, e0⟩ := (M.at_look _ _ _).mp hatD
  rw [← e0]
  have hlim := M.inacc_lim Zx hM hi
  have hne : ∃ β, M.mem β lam := let ⟨w, _, hw⟩ := hi.2.1; ⟨w, hw⟩
  refine ⟨M.vs_num hord hl1 hfR hallR hD hlim hne 0, fun y s hyD hyo hyg hat => ?_⟩
  obtain ⟨s0, hls, es⟩ := (M.at_look _ _ _).mp hat
  rw [← es]
  have hy1 := M.look_dom hf hls
  have hq := M.structParts_and (M.at_val (P := fun x => StructParts M.mem x
      (fun D E Cn Fn Rel => LevelM M.mem SU y D E Cn Fn Rel)) hf (hall y hy1) hls) (ih y hyg s0 hls)
  obtain ⟨de, rest, hp, D', E', hde, Cn', fr, hrest, Fn', Rel', hfr, hlev', _, hU'⟩ := hq
  obtain ⟨lam', hlam', ⟨hord', l1', hl1', R', hfR', hallR', hatD'⟩, hE', hCn', hRel', hFn', _⟩ := hlev'
  obtain ⟨D1, hD', e1⟩ := (M.at_look _ _ _).mp hatD'
  rw [← e1] at hE' hFn' hU' hde
  have hi' := M.lamOf_inacc hlam'
  have hlim' := M.inacc_lim Zx hM hi'
  have hne' : ∃ β, M.mem β lam' := let ⟨w, _, hw⟩ := hi'.2.1; ⟨w, hw⟩
  have hlt : M.mem lam' lam := M.lamOf_lt hyg hlam hlam'
  -- D′ ⊆ D の段：R(λ′) = D′
  have hl'1 : M.mem lam' l1 := (hl1 lam').mpr (Or.inl hlt)
  obtain ⟨X, hlX⟩ := M.vs_val hord hl1 hfR hallR hD hlim hne hl'1
  have eX : X = D1 := M.vtab_agree hord hl1 hfR hallR hord' hl1' hfR' hallR' lam' hl'1
    ((hl1' lam').mpr (Or.inr rfl)) X D1 hlX hD'
  rw [eX] at hlX
  have into : ∀ z, (∀ u, M.mem u z → M.mem u D1) → M.mem z D0 := fun z hz =>
    M.vs_up hord hl1 hfR hallR hD hlim hne hlt hlX hz
  obtain ⟨sE, sCn, sFn⟩ := M.level_sub Zx hM hE' hCn' hFn' hU' hord' hl1' hfR' hallR' hD' hlim' hne'
  have hD1 := into D1 (fun u hu => hu)
  have hE1 := into E' sE
  have hCn1 := into Cn' sCn
  have hFn1 := into Fn' sFn
  have hRel1 := M.vs_empty hord hl1 hfR hallR hD hlim hne hRel'
  have hfr1 := M.vs_pair hord hl1 hfR hallR hD hlim hne hfr hFn1 hRel1
  have hrest1 := M.vs_pair hord hl1 hfR hallR hD hlim hne hrest hCn1 hfr1
  have hde1 := M.vs_pair hord hl1 hfR hallR hD hlim hne hde hD1 hE1
  exact M.vs_pair hord hl1 hfR hallR hD hlim hne hp hde1 hrest1

/-- 仮定 hC なしの一意性。 -/
theorem lngn_unique' {x x' : α} (h : LngnM M.mem x) (h' : LngnM M.mem x') : x = x' :=
  M.lngn_unique Zx hM (M.struct_closed Zx hM) h h'

/-- 生成した最終式 φ について：M で φ(x) を満たす x は高々一つ（仮定はモデルの公理 Zax・hM だけ）。 -/
theorem full_lngn_unique' (Rr : Nm → List α → Prop) (e e' : Nat → α)
    (h : ev M.mem Rr full_lngn e) (h' : ev M.mem Rr full_lngn e') : e 0 = e' 0 :=
  M.full_lngn_unique Zx hM (M.struct_closed Zx hM) Rr e e' h h'

end Closed
end Model

#print axioms Model.inacc_lim
#print axioms Model.vs_pair
#print axioms Model.struct_closed
#print axioms Model.full_lngn_unique'
end Tr
