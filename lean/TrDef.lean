/-
  書き写しの検証（改訂46）：定義可能性の層（definable.py の is_definition・param_true・definable_in）を、
  G6 の isDefSem・definable（G5 の Tarski の意味論で読んだ IsDefinition と Definable）までつなぐ。

  ・W = Ns ∪ {0, 1} の上の割当ては、変数の列 L = 0 :: 1 :: NsL S h の上の sgOf L τ の形（assignW_inv）。
  ・更新 sg[k := a] は sgOf L (τ[k := a])（update_sgOf）。sat_ext は satExt_iff で Tarski の充足になる。
  ・isDef_iff：IsDefM ⟺ G6.isDefSem M5 φ。param_iff：ParamTrueM m ⟺ ∀ σ, φ.sat M5 σ[0 := m]。
  ・definableIn_iff：DefinableInM m ⟺ m ∈ dom ∧ G6.definable M5 m φ。
-/
import TrSem
import G6
namespace Tr
open G5 (Form Occ)

namespace Model
variable {α : Type} (M : Model α)

section DefMain
variable {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}}
  {s : α} {h : Nat} {S : Nat → Nat → Nat}

open Classical in
/-- 変数の列 L の上の割当て sg から、G5 の割当てを作る（L の外は d）。 -/
noncomputable def τL (L : List Nat) (d : {x // M.mem x dom}) (sg : α) : Nat → {x // M.mem x dom} := fun k =>
  if hk : k ∈ L ∧ ∃ a : {x // M.mem x dom}, At M.mem sg (M.num k) (fun x => x = a.1) then Classical.choose hk.2
  else d

theorem τL_at (L : List Nat) (d : {x // M.mem x dom}) (sg : α) (k : Nat) (hk : k ∈ L)
    (hex : ∃ a : {x // M.mem x dom}, At M.mem sg (M.num k) (fun x => x = a.1)) :
    At M.mem sg (M.num k) (fun x => x = (M.τL L d sg k).1) := by
  unfold τL; rw [dif_pos ⟨hk, hex⟩]; exact Classical.choose_spec hex

/-- W 上の割当ては sgOf L τ の形。 -/
theorem assignW_inv (hH : ∀ x, M.mem x dom → M.H x) (L : List Nat) (d : {x // M.mem x dom})
    {W sg : α} (hW : ∀ x, M.mem x W ↔ ∃ k, k ∈ L ∧ x = M.num k) (hA : AssignM M.mem W dom sg) :
    sg = M.sgOf L (fun k => (M.τL L d sg k).1) := by
  have hτ : ∀ k, M.H (M.τL L d sg k).1 := fun k => hH _ (M.τL L d sg k).2
  have val : ∀ k, k ∈ L → ∃ a : {x // M.mem x dom}, At M.mem sg (M.num k) (fun x => x = a.1) := by
    intro k hk
    obtain ⟨q, hq, a, hp⟩ := hA.2.1 (M.num k) ((hW _).mpr ⟨k, hk, rfl⟩)
    obtain ⟨k', a', hp', _, ha'⟩ := hA.1 q hq
    obtain ⟨_, rfl⟩ := M.pair_unique hp hp'
    exact ⟨⟨a, ha'⟩, q, hq, a, hp, rfl⟩
  apply M.ext
  intro q
  rw [M.sgOf_spec _ _ hτ]
  constructor
  · intro hq
    obtain ⟨kk, a, hp, hkk, _⟩ := hA.1 q hq
    obtain ⟨k, hk, rfl⟩ := (hW kk).mp hkk
    obtain ⟨q', hq', b, hp', hb⟩ := M.τL_at L d sg k hk (val k hk)
    have := M.assign_func hA hq hp hq' hp'
    subst this
    refine ⟨k, hk, ?_⟩
    rw [hb] at hp
    exact M.pair_ext hp (M.pr_spec (M.H_num k) (hτ k)).2
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨q', hq', b, hp', hb⟩ := M.τL_at L d sg k hk (val k hk)
    rw [hb] at hp'
    rw [← M.pair_ext hp' (M.pr_spec (M.H_num k) (hτ k)).2]; exact hq'

theorem upd_val (τ : Nat → {x // M.mem x dom}) (k : Nat) (a : {x // M.mem x dom}) :
    Tr.upd (fun k => (τ k).1) k a.1 = fun k' => (G5.upd τ k a k').1 := by
  funext k'; simp only [Tr.upd, G5.upd]; split <;> rfl

/-- sgOf L τ の更新。 -/
theorem update_sgOfT (hH : ∀ x, M.mem x dom → M.H x) (L : List Nat) {W : α}
    (hW : ∀ x, M.mem x W ↔ ∃ k, k ∈ L ∧ x = M.num k) (τ : Nat → {x // M.mem x dom})
    (k : Nat) (hk : k ∈ L) (a : {x // M.mem x dom}) (sg2 : α) :
    UpdateM M.mem W dom (M.sgOf L (fun k => (τ k).1)) (M.num k) a.1 sg2 ↔
      sg2 = M.sgOf L (fun k' => (G5.upd τ k a k').1) := by
  rw [M.update_sgOf L _ (fun k => hH _ (τ k).2) W dom hW (fun k => (τ k).2) k hk a.1 sg2 a.2 (hH _ a.2),
    upd_val]

theorem W_ex (L : List Nat) : ∃ W, ∀ x, M.mem x W ↔ ∃ k, k ∈ L ∧ x = M.num k := by
  have := M.set_spec (L.map M.num)
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨k, _, rfl⟩ := hx; exact M.H_num k)
  refine ⟨M.set (L.map M.num), fun x => ?_⟩
  rw [this.2, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

/-- _common の部分：Z = 0, O = 1, h = |s|, W = {0, 1} ∪ NsL。 -/
theorem defCommon_iff (hs : M.SeqRep4 s h S) (body : α → α → α → Prop) :
    DefCommon M.mem s body ↔ ∃ W, (∀ x, M.mem x W ↔ ∃ k, k ∈ 0 :: 1 :: NsL S h ∧ x = M.num k) ∧
      body W (M.num 0) (M.num 1) := by
  constructor
  · rintro ⟨Z, hZ, O, hO, h', hsw, Ns, hvs, W, ⟨w1, w2, w3, w4⟩, hb⟩
    rw [M.empty_iff] at hZ; subst hZ
    rw [M.succ_num_iff] at hO; subst hO
    have eh := M.seqWith_dom (SeqRep4.dom M hs) hsw; subst eh
    have hNs := (M.varset_iff hs Ns).mp hvs
    refine ⟨W, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hb⟩
    · rcases w1 x hx with hx | rfl | rfl
      · obtain ⟨k, hk, rfl⟩ := (hNs x).mp hx; exact ⟨k, by simp [hk], rfl⟩
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, rfl⟩
    · obtain ⟨k, hk, rfl⟩ := hx
      simp only [List.mem_cons] at hk
      rcases hk with rfl | rfl | hk
      · exact w3
      · exact w4
      · exact w2 _ ((hNs _).mpr ⟨k, hk, rfl⟩)
  · rintro ⟨W, hW, hb⟩
    obtain ⟨_, hNs⟩ := M.Ns0_spec S h
    refine ⟨M.num 0, (M.empty_iff _).mpr rfl, M.num 1, (M.succ_num_iff 0 _).mpr rfl, M.num h, M.seqWith4 hs,
      M.Ns0 S h, (M.varset_iff hs _).mpr hNs, W, ⟨?_, ?_, ?_, ?_⟩, hb⟩
    · intro q hq
      obtain ⟨k, hk, rfl⟩ := (hW q).mp hq
      simp only [List.mem_cons] at hk
      rcases hk with rfl | rfl | hk
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ((hNs _).mpr ⟨k, hk, rfl⟩)
    · intro q hq
      obtain ⟨k, hk, rfl⟩ := (hNs q).mp hq
      exact (hW _).mpr ⟨k, by simp [hk], rfl⟩
    · exact (hW _).mpr ⟨0, by simp, rfl⟩
    · exact (hW _).mpr ⟨1, by simp, rfl⟩

section Main
variable (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Z : M.Zax) (hdom : M.H dom) (hs : M.SeqRep4 s h S)
  (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
include R Z hdom hs hw ho hl

/-- W 上の割当てでの sat_ext。 -/
theorem satW (τ : Nat → {x // M.mem x dom}) :
    SatExtM M.mem s dom E Cn Fn Rel (M.sgOf (0 :: 1 :: NsL S h) (fun k => (τ k).1)) ↔ φ.sat M5 τ :=
  M.satExt_iff R Z hdom hs φ hw ho hl τ _ (fun k hk => by simp [hk])

/-- 定義可能性の層の主定理（1）：is_definition の意図した条件 ⟺ G6 の isDefSem。 -/
theorem isDef_iff : IsDefM M.mem s dom E Cn Fn Rel ↔ G5.isDefSem M5 φ := by
  have hH := R.domH
  have m0 : (0 : Nat) ∈ 0 :: 1 :: NsL S h := by simp
  have m1 : (1 : Nat) ∈ 0 :: 1 :: NsL S h := by simp
  unfold IsDefM
  rw [M.defCommon_iff hs]
  constructor
  · rintro ⟨W, hW, hb⟩ σ
    have hA := M.assign_sgOf _ (fun k => (σ k).1) (fun k => hH _ (σ k).2) W dom hW (fun k => (σ k).2)
    obtain ⟨a, ha, ⟨sa, hsa, hsat⟩, huniq⟩ := hb _ hA
    rw [M.update_sgOfT hH _ hW σ 0 m0 ⟨a, ha⟩] at hsa
    subst hsa
    refine ⟨⟨a, ha⟩, (M.satW R Z hdom hs φ hw ho hl _).mp hsat, fun b hb' => ?_⟩
    apply Subtype.ext
    apply huniq b.1 b.2
    refine ⟨_, (M.update_sgOfT hH _ hW σ 0 m0 b _).mpr rfl, _, (M.update_sgOfT hH _ hW _ 1 m1 b _).mpr rfl, ?_⟩
    rw [M.satW R Z hdom hs φ hw ho hl]
    have e : G5.upd (G5.upd σ 0 b) 1 b = G5.upd (G5.upd (G5.upd σ 0 ⟨a, ha⟩) 1 b) 0 b := by
      funext n; simp only [G5.upd]
      by_cases h0 : n = 0
      · subst h0; simp
      · by_cases h1 : n = 1
        · subst h1; simp
        · simp [h0, h1]
    rw [e]; exact hb'
  · intro hdef
    obtain ⟨W, hW⟩ := M.W_ex (0 :: 1 :: NsL S h)
    refine ⟨W, hW, fun sg hA => ?_⟩
    -- sg の 0 での値を既定値にする
    obtain ⟨q0, hq0, a0, hp0⟩ := hA.2.1 (M.num 0) ((hW _).mpr ⟨0, m0, rfl⟩)
    obtain ⟨_, a0', hp0', _, ha0⟩ := hA.1 q0 hq0
    obtain ⟨_, rfl⟩ := M.pair_unique hp0 hp0'
    have esg := M.assignW_inv hH _ ⟨a0, ha0⟩ hW hA
    generalize M.τL (0 :: 1 :: NsL S h) ⟨a0, ha0⟩ sg = τ at esg
    rw [esg]
    obtain ⟨a, hsa, huniq⟩ := hdef τ
    refine ⟨a.1, a.2, ⟨_, (M.update_sgOfT hH _ hW τ 0 m0 a _).mpr rfl, (M.satW R Z hdom hs φ hw ho hl _).mpr hsa⟩, ?_⟩
    rintro b hb ⟨sb1, hsb1, sb, hsb, hsat⟩
    rw [M.update_sgOfT hH _ hW τ 0 m0 ⟨b, hb⟩] at hsb1
    subst hsb1
    rw [M.update_sgOfT hH _ hW _ 1 m1 ⟨b, hb⟩] at hsb
    subst hsb
    rw [M.satW R Z hdom hs φ hw ho hl] at hsat
    have e : G5.upd (G5.upd (G5.upd τ 0 a) 1 ⟨b, hb⟩) 0 ⟨b, hb⟩ = G5.upd (G5.upd τ 0 ⟨b, hb⟩) 1 ⟨b, hb⟩ := by
      funext n; simp only [G5.upd]
      by_cases h0 : n = 0
      · subst h0; simp
      · by_cases h1 : n = 1
        · subst h1; simp
        · simp [h0, h1]
    have := huniq ⟨b, hb⟩ (by rw [e]; exact hsat)
    exact congrArg Subtype.val this

/-- 定義可能性の層の主定理（2）：param_true の意図した条件 ⟺ x_0 に m を割り当てて φ が常に真。 -/
theorem paramTrue_iff (m : α) (hm : M.mem m dom) :
    ParamTrueM M.mem s dom E Cn Fn Rel m ↔ ∀ σ : Nat → {x // M.mem x dom}, φ.sat M5 (G5.upd σ 0 ⟨m, hm⟩) := by
  have hH := R.domH
  have m0 : (0 : Nat) ∈ 0 :: 1 :: NsL S h := by simp
  unfold ParamTrueM
  rw [M.defCommon_iff hs]
  constructor
  · rintro ⟨W, hW, hb⟩ σ
    have hτ : ∀ k, M.H (G5.upd σ 0 ⟨m, hm⟩ k).1 := fun k => hH _ (G5.upd σ 0 ⟨m, hm⟩ k).2
    have hA := M.assign_sgOf _ _ hτ W dom hW (fun k => (G5.upd σ 0 ⟨m, hm⟩ k).2)
    have hat := (M.at_sgOf _ _ hτ 0 m0 (fun v => v = m)).mpr (by simp [G5.upd])
    exact (M.satW R Z hdom hs φ hw ho hl _).mp (hb _ ⟨hA, hat⟩)
  · intro hall
    obtain ⟨W, hW⟩ := M.W_ex (0 :: 1 :: NsL S h)
    refine ⟨W, hW, fun sg ⟨hA, hat⟩ => ?_⟩
    have esg := M.assignW_inv hH _ ⟨m, hm⟩ hW hA
    generalize M.τL (0 :: 1 :: NsL S h) ⟨m, hm⟩ sg = τ at esg
    have hτ : ∀ k, M.H (τ k).1 := fun k => hH _ (τ k).2
    rw [esg] at hat ⊢
    have h0 : τ 0 = ⟨m, hm⟩ := Subtype.ext ((M.at_sgOf _ _ hτ 0 m0 (fun v => v = m)).mp hat)
    have e : G5.upd τ 0 ⟨m, hm⟩ = τ := by rw [← h0]; exact G5.upd_self τ 0
    rw [M.satW R Z hdom hs φ hw ho hl, ← e]
    exact hall τ

/-- 定義可能性の層の主定理（3）：definable_in の意図した条件 ⟺ m ∈ dom かつ G6 の definable。 -/
theorem definableIn_iff (m : α) :
    DefinableInM M.mem s dom E Cn Fn Rel m ↔ ∃ hm : M.mem m dom, G5.definable M5 ⟨m, hm⟩ φ := by
  unfold DefinableInM
  constructor
  · rintro ⟨hm, hd, hp⟩
    exact ⟨hm, (G5.isDef_iff M5 φ).mpr ((M.isDef_iff R Z hdom hs φ hw ho hl).mp hd),
      (M.paramTrue_iff R Z hdom hs φ hw ho hl m hm).mp hp⟩
  · rintro ⟨hm, hd, hp⟩
    exact ⟨hm, (M.isDef_iff R Z hdom hs φ hw ho hl).mpr ((G5.isDef_iff M5 φ).mp hd),
      (M.paramTrue_iff R Z hdom hs φ hw ho hl m hm).mpr hp⟩

/-- 生成プログラムの式 full_definable_in（Python の出力との一致は tr_expand_check.py）について。 -/
theorem full_definable_in_nat (m : α) (Rr : Nm → List α → Prop) (e : Nat → α)
    (e0 : e 0 = s) (e1 : e 1 = dom) (e2 : e 2 = E) (e3 : e 3 = Cn) (e4 : e 4 = Fn) (e5 : e 5 = Rel) (e6 : e 6 = m) :
    ev M.mem Rr full_definable_in e ↔ ∃ hm : M.mem m dom, G5.definable M5 ⟨m, hm⟩ φ := by
  rw [mean_full_definable_in]
  show DefinableInM M.mem (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) ↔ _
  rw [e0, e1, e2, e3, e4, e5, e6]
  exact M.definableIn_iff R Z hdom hs φ hw ho hl m
end Main

end DefMain
end Model

#print axioms Model.definableIn_iff
#print axioms Model.full_definable_in_nat
end Tr
