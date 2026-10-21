/-
  書き写しの検証（改訂48）：L の段階の層（lorder.py）のうち、定義可能性 defines を Tarski の意味論につなぐ。

  (n, τ) は X 上で y を定義する（DefinesM）⟺ n が純粋な Formula₋ の式 φ の番号で、τ は φ の変数（x_0 以外）への
  割当て ρ の制限で、y = { z ∈ X : (X, ∈) ⊨ φ [x_0 := z, 他は ρ] }。

  ・純粋な式（定数・関数・関係記号を含まない）では、Cn = Fn = Rel = ∅ でも Rep5T（TrSem）が成り立つ（rep5_pure）。
  ・式の番号 n から記号列が一意に決まる（Enc.metacode_inj）ので、DefinesM の ∃ s は与えた s に帰着する。
-/
import TrDef
namespace Tr
open G5 (Form Occ Tok)

namespace Model
variable {α : Type} (M : Model α)

/-- 記号列 S（長さ h）は定数・関数・関係記号を含まない。 -/
def PureS (S : Nat → Nat → Nat) (h : Nat) : Prop :=
  ∀ i, i < h → (∀ k, tok (S i) ≠ some (.cst k)) ∧ (∀ f a, tok (S i) ≠ some (.fn f a)) ∧
    (∀ r a, tok (S i) ≠ some (.rel r a))

theorem pure_iff {s : α} {h : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 s h S) :
    Pure M.mem s (M.num h) ↔ PureS S h := by
  constructor
  · intro hp i hi
    have := hp (M.num i) (M.num_lt hi)
    rw [M.at_iff hs] at this
    obtain ⟨_, t, ht, hc, hf, hr⟩ := this
    refine ⟨fun k e => hc ((M.const_iff ht).mpr ⟨k, e⟩), fun f a e => hf ((M.func_iff ht).mpr ⟨f, ?_⟩),
      fun r a e => hr ((M.rel_iff ht).mpr ⟨r, ?_⟩)⟩
    · have := tok_fn_arity e; subst this; exact e
    · have := tok_rel_arity e; subst this; exact e
  · intro hp p hpm
    obtain ⟨i, hi, rfl⟩ := (M.num_mem h p).mp hpm
    rw [M.at_iff hs]
    obtain ⟨_, _, t, _, ht⟩ := hs.2 i hi
    refine ⟨hi, t, ht, fun hc => ?_, fun hf => ?_, fun hr => ?_⟩
    · obtain ⟨k, e⟩ := (M.const_iff ht).mp hc; exact (hp i hi).1 k e
    · obtain ⟨f, e⟩ := (M.func_iff ht).mp hf; exact (hp i hi).2.1 f _ e
    · obtain ⟨r, e⟩ := (M.rel_iff ht).mp hr; exact (hp i hi).2.2 r _ e

/-- X 上の ∈ の構造（定数・関数・関係記号の解釈は使われないので既定値）。 -/
def eModel (X : α) (d : {x // M.mem x X}) : G5.Model {x // M.mem x X} :=
  ⟨fun a b => M.mem a.1 b.1, fun _ => d, fun _ _ _ => d, fun _ _ _ => False⟩

/-- 純粋な式では、Cn = Fn = Rel = ∅（Z）で構造の表し方の条件が成り立つ。 -/
theorem rep5_pure (Zx : M.Zax) {X E Z : α} (hX : M.H X) (d : {x // M.mem x X}) (hE : ERestrict M.mem X E)
    (hZ : Empty M.mem Z) {S : Nat → Nat → Nat} {h : Nat} (hp : PureS S h) :
    M.Rep5T X E Z Z Z (M.eModel X d) S h := by
  refine ⟨fun x hx => Zx.H_trans x X hX hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    show InPair M.mem E a.1 b.1 ↔ M.mem a.1 b.1
    constructor
    · rintro ⟨q, hq, hpq⟩
      obtain ⟨a', b', hp', _, _, hab⟩ := hE.1 q hq
      obtain ⟨rfl, rfl⟩ := M.pair_unique hpq hp'
      exact hab
    · intro hab
      exact hE.2 b.1 b.2 a.1 hab
  · rintro t g k ⟨i, hi, rfl⟩ _ hk
    exact absurd hk ((hp i hi).1 k)
  · rintro t g f a ⟨i, hi, rfl⟩ _ hk
    exact absurd hk ((hp i hi).2.1 f a)
  · rintro t w v ⟨q, hq, _⟩
    exact absurd hq (hZ q)
  · rintro t g r a ⟨i, hi, rfl⟩ _ hk
    exact absurd hk ((hp i hi).2.2 r a)

/-- 4 つ組の列から記号列を取り出す。 -/
theorem seq4_extract {s h' : α} (hsw : SeqWith M.mem s h' (Tuple4 M.mem)) :
    ∃ n S, h' = M.num n ∧ M.SeqRep4 s n S := by
  obtain ⟨hnat, helem, htot, hfun⟩ := hsw
  obtain ⟨n, rfl⟩ := (M.nat_iff h').mp hnat
  have hex : ∀ i, ∃ g : Nat → Nat, i < n → ∃ x, M.mem x s ∧ ∃ t, Pair M.mem x (M.num i) t ∧ M.SeqRep t 4 g := by
    intro i
    by_cases hi : i < n
    · obtain ⟨q, hq, a, hp⟩ := htot (M.num i) (M.num_lt hi)
      obtain ⟨i', a', hp', _, ha'⟩ := helem q hq
      obtain ⟨_, e2⟩ := M.pair_unique hp hp'
      obtain ⟨g, hg⟩ := (M.tuple4_iff a').mp ha'
      exact ⟨g, fun _ => ⟨q, hq, a, hp, e2 ▸ hg⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hi⟩
  refine ⟨n, fun i => Classical.choose (hex i), rfl, ?_, fun i hi => Classical.choose_spec (hex i) hi⟩
  intro x hx
  obtain ⟨i, a, hp, hi, _⟩ := helem x hx
  obtain ⟨j, hj, rfl⟩ := (M.num_mem n i).mp hi
  refine ⟨j, hj, a, hp, ?_⟩
  obtain ⟨x', hx', t', hp', ht'⟩ := Classical.choose_spec (hex j) hj
  have := hfun x hx _ _ hp x' hx' _ _ hp' rfl
  rw [this]; exact ht'

theorem seqRep_ext' {t t' : α} {g g' : Nat → Nat} {n : Nat} (h : M.SeqRep t n g) (h' : M.SeqRep t' n g')
    (e : ∀ j, j < n → g j = g' j) : t = t' := by
  have h2 : M.SeqRep t' n g :=
    ⟨fun x hx => by obtain ⟨i, hi, hp⟩ := h'.1 x hx; exact ⟨i, hi, by rw [e i hi]; exact hp⟩,
     fun i hi => by obtain ⟨x, hx, hp⟩ := h'.2 i hi; exact ⟨x, hx, by rw [e i hi]; exact hp⟩⟩
  exact M.seqRep_ext h h2

theorem seqRep4_ext {s s' : α} {n : Nat} {S S' : Nat → Nat → Nat} (h : M.SeqRep4 s n S) (h' : M.SeqRep4 s' n S')
    (e : ∀ i, i < n → ∀ j, j < 4 → S i j = S' i j) : s = s' := by
  apply M.ext; intro x; constructor
  · intro hx
    obtain ⟨i, hi, t, hp, ht⟩ := h.1 x hx
    obtain ⟨x', hx', t', hp', ht'⟩ := h'.2 i hi
    have := M.seqRep_ext' ht ht' (e i hi); subst this
    rw [M.pair_ext hp hp']; exact hx'
  · intro hx
    obtain ⟨i, hi, t, hp, ht⟩ := h'.1 x hx
    obtain ⟨x', hx', t', hp', ht'⟩ := h.2 i hi
    have := M.seqRep_ext' ht' ht (e i hi); subst this
    rw [M.pair_ext hp hp']; exact hx'

/-- φ の x_0 以外の変数の列。 -/
def KL (S : Nat → Nat → Nat) (h : Nat) : List Nat := (NsL S h).filter (fun k => k ≠ 0)

theorem mem_KL (S : Nat → Nat → Nat) (h k : Nat) : k ∈ KL S h ↔ k ∈ NsL S h ∧ k ≠ 0 := by
  simp [KL, List.mem_filter]

/-- σ = τ ∪ {(0, z)} は、0 :: KL の上の割当て ρ[0 := z]。 -/
theorem sigma_iff (hH : ∀ x, M.mem x X → M.H x) (L : List Nat) (hL0 : (0 : Nat) ∉ L)
    (ρ : Nat → {x // M.mem x X}) (z : {x // M.mem x X}) (sg : α) :
    SigmaIs M.mem (M.sgOf L (fun k => (ρ k).1)) z.1 sg ↔
      sg = M.sgOf (0 :: L) (fun k => (G5.upd ρ 0 z k).1) := by
  have hρ : ∀ k, M.H (ρ k).1 := fun k => hH _ (ρ k).2
  have hρ' : ∀ k, M.H (G5.upd ρ 0 z k).1 := fun k => hH _ (G5.upd ρ 0 z k).2
  have v0 : (G5.upd ρ 0 z 0).1 = z.1 := by simp [G5.upd]
  have vk : ∀ k, k ∈ L → (G5.upd ρ 0 z k).1 = (ρ k).1 := by
    intro k hk
    have : k ≠ 0 := fun e => hL0 (e ▸ hk)
    simp [G5.upd, this]
  have hz := hH _ z.2
  have p0 := (M.pr_spec (M.H_num 0) hz).2
  constructor
  · rintro ⟨c1, c2, ⟨q0, hq0, k0, a0, hp0, he0, rfl⟩⟩
    rw [M.empty_iff] at he0; subst he0
    apply M.ext; intro q
    rw [M.sgOf_spec _ _ hρ']
    constructor
    · intro hq
      rcases c1 q hq with hq | ⟨k, a, hp, he, rfl⟩
      · obtain ⟨k, hk, rfl⟩ := (M.sgOf_spec L _ hρ q).mp hq
        exact ⟨k, List.mem_cons_of_mem _ hk, by rw [vk k hk]⟩
      · rw [M.empty_iff] at he; subst he
        exact ⟨0, List.mem_cons_self _ _, by rw [v0]; exact M.pair_ext hp p0⟩
    · rintro ⟨k, hk, rfl⟩
      rcases List.mem_cons.mp hk with rfl | hk
      · rw [v0, ← M.pair_ext hp0 p0]; exact hq0
      · rw [vk k hk]; exact c2 _ ((M.sgOf_spec L _ hρ _).mpr ⟨k, hk, rfl⟩)
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨k, hk, rfl⟩ := (M.sgOf_spec _ _ hρ' q).mp hq
      rcases List.mem_cons.mp hk with rfl | hk
      · exact Or.inr ⟨M.num 0, z.1, by rw [v0]; exact p0, (M.empty_iff _).mpr rfl, rfl⟩
      · exact Or.inl ((M.sgOf_spec L _ hρ _).mpr ⟨k, hk, by rw [vk k hk]⟩)
    · intro q hq
      obtain ⟨k, hk, rfl⟩ := (M.sgOf_spec L _ hρ q).mp hq
      exact (M.sgOf_spec _ _ hρ' _).mpr ⟨k, List.mem_cons_of_mem _ hk, by rw [vk k hk]⟩
    · exact ⟨_, (M.sgOf_spec _ _ hρ' _).mpr ⟨0, List.mem_cons_self _ _, rfl⟩, M.num 0, z.1, by rw [v0]; exact p0,
        (M.empty_iff _).mpr rfl, rfl⟩

/-- ∈ の X への制限は H の中にある（X が推移的なとき ERestrict）。 -/
theorem erestrict_ex (Zx : M.Zax) {X : α} (hX : M.H X) (hXt : Trans M.mem X) : ∃ E, ERestrict M.mem X E := by
  obtain ⟨P, hP, hPm⟩ := M.prod_ex Zx X X hX hX
  obtain ⟨E, _, hEm⟩ := Zx.sep P (fun p => ∃ a b, Pair M.mem p a b ∧ M.mem a b) hP
  refine ⟨E, ?_, ?_⟩
  · intro q hq
    obtain ⟨hqP, a, b, hp, hab⟩ := (hEm q).mp hq
    obtain ⟨x, y, hx, hy, rfl⟩ := (hPm _).mp hqP
    obtain ⟨rfl, rfl⟩ := M.pair_unique hp (M.pr_spec (Zx.H_trans x X hX hx) (Zx.H_trans y X hX hy)).2
    exact ⟨a, b, hp, hx, hy, hab⟩
  · intro b hb a hab
    have ha : M.mem a X := hXt b hb a hab
    have hpr := (M.pr_spec (Zx.H_trans a X hX ha) (Zx.H_trans b X hX hb)).2
    exact ⟨_, (hEm _).mpr ⟨(hPm _).mpr ⟨a, b, ha, hb, rfl⟩, a, b, hpr, hab⟩, hpr⟩

section Defines
variable (Zx : M.Zax) {X : α} (hX : M.H X) (hXt : Trans M.mem X) (d : {x // M.mem x X})
  {s : α} {h : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 s h S)
  (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
  (hθ : ∀ n, n < h → str S h n ≠ some (.fn 1 1)) (hp : PureS S h)
include Zx hX hXt hs hw ho hl hθ hp

/-- L の段階の層の主定理：(n, τ) が X 上で y を定義する ⟺ τ は x_0 以外の変数への割当て ρ の制限で、
    y = { z ∈ X : (X, ∈) ⊨ φ [x_0 := z, 他は ρ] }。n は純粋な Formula₋ の式 φ の番号。 -/
theorem defines_iff (tau y : α) :
    DefinesM M.mem (M.num (Enc.metacode h S)) tau X y ↔
      ∃ ρ : Nat → {x // M.mem x X}, tau = M.sgOf (KL S h) (fun k => (ρ k).1) ∧
        (∀ z, M.mem z y → M.mem z X) ∧
        ∀ z (hz : M.mem z X), (M.mem z y ↔ φ.sat (M.eModel X d) (G5.upd ρ 0 ⟨z, hz⟩)) := by
  have hH : ∀ x, M.mem x X → M.H x := fun x hx => Zx.H_trans x X hX hx
  have hL0 : (0 : Nat) ∉ KL S h := fun h0 => ((mem_KL S h 0).mp h0).2 rfl
  have hL : ∀ k, k ∈ NsL S h → k ∈ 0 :: KL S h := by
    intro k hk
    by_cases e : k = 0
    · subst e; exact List.mem_cons_self _ _
    · exact List.mem_cons_of_mem _ ((mem_KL S h k).mpr ⟨hk, e⟩)
  -- z ∈ y の条件の読み替え
  have key : ∀ E Z, ERestrict M.mem X E → Empty M.mem Z → ∀ (ρ : Nat → {x // M.mem x X}) z (hz : M.mem z X),
      (∃ sg, SigmaIs M.mem (M.sgOf (KL S h) (fun k => (ρ k).1)) z sg ∧ SatExtM M.mem s X E Z Z Z sg) ↔
        φ.sat (M.eModel X d) (G5.upd ρ 0 ⟨z, hz⟩) := by
    intro E Z hE hZ ρ z hz
    have R := M.rep5_pure Zx hX d hE hZ hp
    rw [← M.satExt_iff R Zx hX hs φ hw ho hl _ (0 :: KL S h) hL]
    constructor
    · rintro ⟨sg, hsig, hsat⟩
      rw [M.sigma_iff hH _ hL0 ρ ⟨z, hz⟩] at hsig
      subst hsig; exact hsat
    · intro hsat
      exact ⟨_, (M.sigma_iff hH _ hL0 ρ ⟨z, hz⟩ _).mpr rfl, hsat⟩
  constructor
  · rintro ⟨s', hfm, hmc, h', hsw, hpure, Ns, hvs, K, ⟨hK1, hK2⟩, hA, Z, hZ, E, hE, hsub, hiff⟩
    obtain ⟨_, _, _, _, h'', ⟨hsw4, _⟩, _⟩ := hfm
    obtain ⟨n', S', rfl, hs'⟩ := M.seq4_extract hsw4
    have e := (M.metacode_iff hs' _).mp hmc
    obtain ⟨eh, eS⟩ := Enc.metacode_inj _ _ _ _ (M.num_inj e)
    subst eh
    have es := M.seqRep4_ext hs' hs (fun i hi j hj => (eS i hi j hj).symm)
    subst es
    have eh' := M.seqWith_dom (SeqRep4.dom M hs) hsw; subst eh'
    have hNs := (M.varset_iff hs Ns).mp hvs
    have hK : ∀ x, M.mem x K ↔ ∃ k, k ∈ KL S h ∧ x = M.num k := by
      intro x
      constructor
      · intro hx
        obtain ⟨hxN, hne⟩ := hK1 x hx
        obtain ⟨k, hk, rfl⟩ := (hNs x).mp hxN
        refine ⟨k, (mem_KL S h k).mpr ⟨hk, fun e0 => hne ((M.empty_iff _).mpr (by rw [e0]))⟩, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        obtain ⟨hkN, hk0⟩ := (mem_KL S h k).mp hk
        rcases hK2 _ ((hNs _).mpr ⟨k, hkN, rfl⟩) with he | hm
        · exact absurd (M.num_inj ((M.empty_iff _).mp he)) hk0
        · exact hm
    have eτ := M.assignW_inv hH (KL S h) d hK hA
    refine ⟨_, eτ, hsub, fun z hz => ?_⟩
    rw [hiff z hz, ← key E Z hE hZ _ z hz, ← eτ]
  · rintro ⟨ρ, rfl, hsub, hiff⟩
    obtain ⟨_, hNs⟩ := M.Ns0_spec S h
    obtain ⟨K, hK⟩ := M.W_ex (KL S h)
    obtain ⟨E, hE⟩ := M.erestrict_ex Zx hX hXt
    have hsw4 := M.seqWith4 hs
    refine ⟨s, (M.formula_minus_iff hs).mpr ⟨⟨φ, hw, ho, hl⟩, hθ⟩, (M.metacode_iff hs _).mpr rfl, M.num h,
      ⟨hsw4.1, fun q hq => by obtain ⟨i, a, hpq, hi, _⟩ := hsw4.2.1 q hq; exact ⟨i, a, hpq, hi, trivial⟩,
        hsw4.2.2.1, hsw4.2.2.2⟩,
      (M.pure_iff hs).mpr hp, M.Ns0 S h, (M.varset_iff hs _).mpr hNs, K, ⟨?_, ?_⟩,
      M.assign_sgOf _ _ (fun k => hH _ (ρ k).2) K X hK (fun k => (ρ k).2),
      M.num 0, (M.empty_iff _).mpr rfl, E, hE, hsub, fun z hz => ?_⟩
    · intro k hk
      obtain ⟨k', hk', rfl⟩ := (hK k).mp hk
      obtain ⟨hkN, hk0⟩ := (mem_KL S h k').mp hk'
      exact ⟨(hNs _).mpr ⟨k', hkN, rfl⟩, fun he => hk0 (M.num_inj ((M.empty_iff _).mp he))⟩
    · intro k hk
      obtain ⟨k', hkN, rfl⟩ := (hNs k).mp hk
      by_cases e0 : k' = 0
      · subst e0; exact Or.inl ((M.empty_iff _).mpr rfl)
      · exact Or.inr ((hK _).mpr ⟨k', (mem_KL S h k').mpr ⟨hkN, e0⟩, rfl⟩)
    · rw [hiff z hz, key E (M.num 0) hE ((M.empty_iff _).mpr rfl) ρ z hz]

/-- 生成プログラムの式 full_defines（Python の出力との一致は tr_expand_check.py）について。 -/
theorem full_defines_nat (tau y : α) (Rr : Nm → List α → Prop) (e : Nat → α)
    (e0 : e 0 = M.num (Enc.metacode h S)) (e1 : e 1 = tau) (e2 : e 2 = X) (e3 : e 3 = y) :
    ev M.mem Rr full_defines e ↔
      ∃ ρ : Nat → {x // M.mem x X}, tau = M.sgOf (KL S h) (fun k => (ρ k).1) ∧
        (∀ z, M.mem z y → M.mem z X) ∧
        ∀ z (hz : M.mem z X), (M.mem z y ↔ φ.sat (M.eModel X d) (G5.upd ρ 0 ⟨z, hz⟩)) := by
  rw [mean_full_defines]
  show DefinesM M.mem (e 0) (e 1) (e 2) (e 3) ↔ _
  rw [e0, e1, e2, e3]
  exact M.defines_iff Zx hX hXt d hs φ hw ho hl hθ hp tau y

end Defines

end Model

#print axioms Model.defines_iff
#print axioms Model.full_defines_nat
end Tr
