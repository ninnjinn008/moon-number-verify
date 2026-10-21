/-
  書き写しの検証（改訂49）：step の順序 <_{β+1} が整列順序であること（G13 の succ_wf への接続）。

  集合の定義 (n, τ)（n は純粋な式の番号、τ は変数 x_k（k ∈ K, K = Ns ∖ {0}）への割当て）を、
  G13 の (式の番号, パラメータの列) に移す：enc(n, τ) = (m, [τ(k) : k ∈ Ks n])（Ks n は K を小さい順に並べた列）。
  ・lexLess_iff：集合の辞書式比較 LexLess は、Ks に沿った値の列の辞書式順序 G13.lexR と同値。
  ・defLess_iff：DefLess (n, τ) (n′, τ′) ⟺ G13.defLt (enc …) (enc …)。
  ・step_wo：< が X 上の狭義の整列順序なら、step の W1 は X1 = Def(X) 上の狭義の整列順序
    （整礎・非反射・推移・全順序）で、X の上では < と一致し、X は始切片。
-/
import TrLO
import G13
namespace Tr

/-- Ks の上で、最初に値が異なる添字 k で R (f k) (g k)。 -/
def lexAt {β : Type} (R : β → β → Prop) (Ks : List Nat) (f g : Nat → β) : Prop :=
  ∃ k, k ∈ Ks ∧ R (f k) (g k) ∧ ∀ j, j ∈ Ks → j < k → f j = g j

theorem lexAt_iff {β : Type} (R : β → β → Prop) :
    ∀ (Ks : List Nat), Ks.Pairwise (· < ·) → ∀ f g, lexAt R Ks f g ↔ G13.lexR R (Ks.map f) (Ks.map g) := by
  intro Ks
  induction Ks with
  | nil => intro _ f g; simp [lexAt, G13.lexR]
  | cons a t ih =>
    intro hp f g
    rw [List.pairwise_cons] at hp
    obtain ⟨ha, ht⟩ := hp
    simp only [List.map_cons, G13.lexR]
    rw [← ih ht f g]
    constructor
    · rintro ⟨k, hk, hr, hlt⟩
      rcases List.mem_cons.mp hk with rfl | hk
      · exact Or.inl hr
      · have hak := ha k hk
        exact Or.inr ⟨hlt a (List.mem_cons_self _ _) hak,
          k, hk, hr, fun j hj hjk => hlt j (List.mem_cons_of_mem _ hj) hjk⟩
    · rintro (hr | ⟨e, k, hk, hr, hlt⟩)
      · refine ⟨a, List.mem_cons_self _ _, hr, fun j hj hja => ?_⟩
        rcases List.mem_cons.mp hj with rfl | hj
        · exact absurd hja (Nat.lt_irrefl _)
        · exact absurd (ha j hj) (by omega)
      · refine ⟨k, List.mem_cons_of_mem _ hk, hr, fun j hj hjk => ?_⟩
        rcases List.mem_cons.mp hj with rfl | hj
        · exact e
        · exact hlt j hj hjk

theorem lexAt_congr {β : Type} (R : β → β → Prop) (Ks : List Nat) {f f' g g' : Nat → β}
    (ef : ∀ k, k ∈ Ks → f k = f' k) (eg : ∀ k, k ∈ Ks → g k = g' k) : lexAt R Ks f g ↔ lexAt R Ks f' g' := by
  constructor
  · rintro ⟨k, hk, hr, hlt⟩
    exact ⟨k, hk, by rw [← ef k hk, ← eg k hk]; exact hr,
      fun j hj hjk => by rw [← ef j hj, ← eg j hj]; exact hlt j hj hjk⟩
  · rintro ⟨k, hk, hr, hlt⟩
    exact ⟨k, hk, by rw [ef k hk, eg k hk]; exact hr,
      fun j hj hjk => by rw [ef j hj, eg j hj]; exact hlt j hj hjk⟩

/-- 自然数の列の要素の上界。 -/
def bnd (l : List Nat) : Nat := l.foldr (fun a b => a + b + 1) 0

theorem lt_bnd : ∀ (l : List Nat) (k : Nat), k ∈ l → k < bnd l := by
  intro l
  induction l with
  | nil => intro k hk; simp at hk
  | cons a t ih =>
    intro k hk
    simp only [bnd, List.foldr_cons] at *
    rcases List.mem_cons.mp hk with rfl | hk
    · omega
    · have := ih k hk; unfold bnd at this; omega

/-- 列 l の要素を小さい順に重複なく並べた列。 -/
def sortL (l : List Nat) : List Nat := (List.range (bnd l)).filter (fun k => decide (k ∈ l))

theorem mem_sortL (l : List Nat) (k : Nat) : k ∈ sortL l ↔ k ∈ l := by
  simp only [sortL, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨lt_bnd l k h, h⟩⟩

theorem sortL_pairwise (l : List Nat) : (sortL l).Pairwise (· < ·) :=
  List.Pairwise.sublist (List.filter_sublist _) (List.pairwise_lt_range _)

namespace Model
variable {α : Type} (M : Model α)

/-! ### 割当ての値 -/

open Classical in
/-- τ の添字 k での値（なければ 0）。 -/
noncomputable def valAt (τ : α) (k : Nat) : α :=
  if h : ∃ v, At M.mem τ (M.num k) (fun x => x = v) then Classical.choose h else M.num 0

theorem valAt_sgOf (L : List Nat) (f : Nat → α) (hf : ∀ k, M.H (f k)) (k : Nat) (hk : k ∈ L) :
    M.valAt (M.sgOf L f) k = f k := by
  have hex : ∃ v, At M.mem (M.sgOf L f) (M.num k) (fun x => x = v) := ⟨f k, (M.at_sgOf L f hf k hk _).mpr rfl⟩
  unfold valAt; rw [dif_pos hex]
  exact ((M.at_sgOf L f hf k hk _).mp (Classical.choose_spec hex)).symm

theorem sgOf_congr (L : List Nat) {f g : Nat → α} (e : ∀ k, k ∈ L → f k = g k) : M.sgOf L f = M.sgOf L g := by
  unfold sgOf
  rw [List.map_congr_left (fun k hk => by rw [e k hk])]

/-- 列 L の上の関数（K の元は L の番号）は sgOf L f の形。 -/
theorem assign_sgOf_ex (Zx : M.Zax) {X K τ : α} (hX : M.H X) (L : List Nat)
    (hK : ∀ x, M.mem x K ↔ ∃ k, k ∈ L ∧ x = M.num k) (hA : AssignM M.mem K X τ) :
    ∃ f : Nat → α, (∀ k, M.H (f k)) ∧ (∀ k, k ∈ L → M.mem (f k) X) ∧ τ = M.sgOf L f := by
  have hH : ∀ x, M.mem x X → M.H x := fun x hx => Zx.H_trans x X hX hx
  by_cases hne : ∃ x, M.mem x X
  · obtain ⟨x0, hx0⟩ := hne
    refine ⟨fun k => (M.τL L ⟨x0, hx0⟩ τ k).1, fun k => hH _ (M.τL L ⟨x0, hx0⟩ τ k).2,
      fun k _ => (M.τL L ⟨x0, hx0⟩ τ k).2, M.assignW_inv hH L ⟨x0, hx0⟩ hK hA⟩
  · have hL : ∀ k, k ∉ L := by
      intro k hk
      obtain ⟨q, hq, a, hp⟩ := hA.2.1 (M.num k) ((hK _).mpr ⟨k, hk, rfl⟩)
      obtain ⟨k', a', hp', _, ha'⟩ := hA.1 q hq
      exact hne ⟨a', ha'⟩
    refine ⟨fun _ => M.num 0, fun _ => M.H_num 0, fun k hk => absurd hk (hL k), ?_⟩
    apply M.ext; intro q
    rw [M.sgOf_spec L _ (fun _ => M.H_num 0)]
    constructor
    · intro hq
      obtain ⟨k, a, hp, hk, _⟩ := hA.1 q hq
      obtain ⟨j, hj, rfl⟩ := (hK k).mp hk
      exact absurd hj (hL j)
    · rintro ⟨k, hk, _⟩; exact absurd hk (hL k)

/-! ### 記号列の一意性 -/

theorem metacode_unique {n s s' : α} (h : MetaCodeM M.mem n s) (h' : MetaCodeM M.mem n s') :
    s = s' ∧ ∃ len S, M.SeqRep4 s len S ∧ n = M.num (Enc.metacode len S) := by
  have hc := h
  have hc' := h'
  obtain ⟨h1, hsw, _⟩ := hc
  obtain ⟨h1', hsw', _⟩ := hc'
  obtain ⟨len, S, rfl, hs⟩ := M.seq4_extract hsw
  obtain ⟨len', S', rfl, hs'⟩ := M.seq4_extract hsw'
  have e := (M.metacode_iff hs n).mp h
  have e' := (M.metacode_iff hs' n).mp h'
  obtain ⟨el, eS⟩ := Enc.metacode_inj _ _ _ _ (M.num_inj (e.symm.trans e'))
  subst el
  exact ⟨M.seqRep4_ext hs hs' eS, len, S, hs, e⟩

theorem erestrict_unique {X E E' : α} (h : ERestrict M.mem X E) (h' : ERestrict M.mem X E') : E = E' := by
  have side : ∀ E E', ERestrict M.mem X E → ERestrict M.mem X E' → ∀ q, M.mem q E → M.mem q E' := by
    intro E E' h h' q hq
    obtain ⟨a, b, hp, _, hb, hab⟩ := h.1 q hq
    obtain ⟨q', hq', hp'⟩ := h'.2 b hb a hab
    rw [M.pair_ext hp hp']; exact hq'
  exact M.ext _ _ (fun q => ⟨side E E' h h' q, side E' E h' h q⟩)

/-- (n, τ) が定義する集合は一つ。 -/
theorem defines_unique {n τ X y y' : α} (h : DefinesM M.mem n τ X y) (h' : DefinesM M.mem n τ X y') : y = y' := by
  obtain ⟨s, _, hmc, _, _, _, _, _, _, _, _, Z, hZ, E, hE, hsub, hiff⟩ := h
  obtain ⟨s', _, hmc', _, _, _, _, _, _, _, _, Z', hZ', E', hE', hsub', hiff'⟩ := h'
  obtain ⟨rfl, _⟩ := M.metacode_unique hmc hmc'
  have eZ := M.empty_eq hZ hZ'; subst eZ
  have eE := M.erestrict_unique hE hE'; subst eE
  apply M.ext; intro z
  constructor
  · intro hz; have hzX := hsub z hz; exact (hiff' z hzX).mpr ((hiff z hzX).mp hz)
  · intro hz; have hzX := hsub' z hz; exact (hiff z hzX).mpr ((hiff' z hzX).mp hz)

/-! ### 式の番号と添字の列 -/

/-- L は、番号 n の式の x_0 以外の変数の添字を小さい順に並べた列。 -/
def IdxL (n : α) (L : List Nat) : Prop :=
  L.Pairwise (· < ·) ∧ ∃ s h' Ns, MetaCodeM M.mem n s ∧ SeqWith M.mem s h' (fun _ => True) ∧ VarSet M.mem s h' Ns ∧
    ∀ k, k ∈ L ↔ (M.mem (M.num k) Ns ∧ k ≠ 0)

open Classical in
noncomputable def Ks (n : α) : List Nat := if h : ∃ L, M.IdxL n L then Classical.choose h else []

open Classical in
noncomputable def mOf (n : α) : Nat := if h : ∃ m, n = M.num m then Classical.choose h else 0

theorem mOf_num (m : Nat) : M.mOf (M.num m) = m := by
  have hex : ∃ m', M.num m = M.num m' := ⟨m, rfl⟩
  unfold mOf; rw [dif_pos hex]
  exact (M.num_inj (Classical.choose_spec hex)).symm

/-- (n, τ) が X 上で y を定義するとき：n は式の番号 num m、τ は Ks n の上の割当て。 -/
theorem defines_shape (Zx : M.Zax) {n τ X y : α} (hX : M.H X) (h : DefinesM M.mem n τ X y) :
    (∃ m, n = M.num m) ∧ (M.Ks n).Pairwise (· < ·) ∧
    ∃ f : Nat → α, (∀ k, M.H (f k)) ∧ (∀ k, k ∈ M.Ks n → M.mem (f k) X) ∧ τ = M.sgOf (M.Ks n) f := by
  obtain ⟨s, hfm, hmc, h', hsw, _, Ns, hvs, K, ⟨hK1, hK2⟩, hA, _⟩ := h
  obtain ⟨_, len, S, hs, en⟩ := M.metacode_unique hmc hmc
  have eh := M.seqWith_dom (SeqRep4.dom M hs) hsw; subst eh
  have hNs := (M.varset_iff hs Ns).mp hvs
  -- 列 Ks n の存在と、その特徴づけ
  have hIdx : M.IdxL n (sortL (KL S len)) := by
    refine ⟨sortL_pairwise _, s, M.num len, Ns, hmc, hsw, hvs, fun k => ?_⟩
    rw [mem_sortL, mem_KL]
    constructor
    · rintro ⟨hk, hk0⟩; exact ⟨(hNs _).mpr ⟨k, hk, rfl⟩, hk0⟩
    · rintro ⟨hk, hk0⟩
      obtain ⟨k', hk', e⟩ := (hNs _).mp hk
      rw [M.num_inj e]; exact ⟨hk', by rw [← M.num_inj e]; exact hk0⟩
  have hex : ∃ L, M.IdxL n L := ⟨_, hIdx⟩
  have hKs : M.IdxL n (M.Ks n) := by unfold Ks; rw [dif_pos hex]; exact Classical.choose_spec hex
  obtain ⟨hpw, s', h'', Ns', hmc', hsw', hvs', hmem⟩ := hKs
  obtain ⟨es, _⟩ := M.metacode_unique hmc hmc'
  subst es
  have eh' := M.seqWith_dom (SeqRep4.dom M hs) hsw'; subst eh'
  have hNs' := (M.varset_iff hs Ns').mp hvs'
  have hK : ∀ x, M.mem x K ↔ ∃ k, k ∈ M.Ks n ∧ x = M.num k := by
    intro x
    constructor
    · intro hx
      obtain ⟨hxN, hne⟩ := hK1 x hx
      obtain ⟨k, hk, rfl⟩ := (hNs x).mp hxN
      refine ⟨k, (hmem k).mpr ⟨(hNs' _).mpr ⟨k, hk, rfl⟩, fun e0 => hne ((M.empty_iff _).mpr (by rw [e0]))⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨hkN, hk0⟩ := (hmem k).mp hk
      obtain ⟨k', hk', e⟩ := (hNs' _).mp hkN
      rcases hK2 _ ((hNs _).mpr ⟨k', hk', e⟩) with he | hm
      · exact absurd (M.num_inj ((M.empty_iff _).mp he)) hk0
      · exact hm
  exact ⟨⟨_, en⟩, hpw, M.assign_sgOf_ex Zx hX (M.Ks n) hK hA⟩

/-- 集合の定義 (n, τ) を G13 の (番号, 値の列) に移す。 -/
noncomputable def enc (n τ : α) : Nat × List α := (M.mOf n, (M.Ks n).map (M.valAt τ))

/-! ### 辞書式比較 -/

theorem lexLess_sgOf (Wg : α) (L : List Nat) (f g : Nat → α) (hf : ∀ k, M.H (f k)) (hg : ∀ k, M.H (g k)) :
    LexLess M.mem (M.sgOf L f) (M.sgOf L g) Wg ↔ lexAt (InPair M.mem Wg) L f g := by
  constructor
  · rintro ⟨q, hq, k, u, hp, q2, hq2, k2, u2, hp2, rfl, hw, hall⟩
    obtain ⟨k0, hk0, rfl, rfl⟩ := M.sgOf_pair L f hf hq hp
    obtain ⟨k1, _, e1, rfl⟩ := M.sgOf_pair L g hg hq2 hp2
    have := M.num_inj e1; subst this
    refine ⟨k0, hk0, hw, fun j hj hjk => ?_⟩
    obtain ⟨j', v, hpj, himp⟩ := hall _ ((M.sgOf_spec L f hf _).mpr ⟨j, hj, rfl⟩)
    obtain ⟨e2, rfl⟩ := M.pair_unique hpj (M.pr_spec (M.H_num j) (hf j)).2
    subst e2
    obtain ⟨q3, hq3, hp3⟩ := himp (M.num_lt hjk)
    obtain ⟨j3, _, e3, e4⟩ := M.sgOf_pair L g hg hq3 hp3
    rw [← M.num_inj e3] at e4; exact e4
  · rintro ⟨k, hk, hw, hall⟩
    refine ⟨_, (M.sgOf_spec L f hf _).mpr ⟨k, hk, rfl⟩, M.num k, f k, (M.pr_spec (M.H_num k) (hf k)).2,
      _, (M.sgOf_spec L g hg _).mpr ⟨k, hk, rfl⟩, M.num k, g k, (M.pr_spec (M.H_num k) (hg k)).2, rfl, hw, ?_⟩
    intro r hr
    obtain ⟨j, hj, rfl⟩ := (M.sgOf_spec L f hf r).mp hr
    refine ⟨M.num j, f j, (M.pr_spec (M.H_num j) (hf j)).2, fun hjk => ?_⟩
    have hjk' : j < k := M.num_mem_iff.mp hjk
    refine ⟨_, (M.sgOf_spec L g hg _).mpr ⟨j, hj, rfl⟩, ?_⟩
    rw [hall j hj hjk']; exact (M.pr_spec (M.H_num j) (hg j)).2

section Enc
variable (Zx : M.Zax) {X Wg : α} (hX : M.H X)
include Zx hX

theorem defLess_iff {n τ n2 τ2 y y2 : α} (hd : DefinesM M.mem n τ X y) (hd2 : DefinesM M.mem n2 τ2 X y2) :
    DefLess M.mem n τ n2 τ2 Wg ↔ G13.defLt (InPair M.mem Wg) (M.enc n τ) (M.enc n2 τ2) := by
  obtain ⟨⟨m, rfl⟩, hpw, f, hf, _, rfl⟩ := M.defines_shape Zx hX hd
  obtain ⟨⟨m2, rfl⟩, hpw2, f2, hf2, _, rfl⟩ := M.defines_shape Zx hX hd2
  simp only [enc, mOf_num, DefLess, G13.defLt]
  apply or_congr (M.num_mem_iff)
  constructor
  · rintro ⟨e, hl⟩
    have em := M.num_inj e; subst em
    refine ⟨rfl, by simp, ?_⟩
    rw [← lexAt_iff _ _ hpw, lexAt_congr _ _ (fun k hk => M.valAt_sgOf _ f hf k hk)
      (fun k hk => M.valAt_sgOf _ f2 hf2 k hk)]
    exact (M.lexLess_sgOf Wg _ f f2 hf hf2).mp hl
  · rintro ⟨em, _, hl⟩
    subst em
    refine ⟨rfl, (M.lexLess_sgOf Wg _ f f2 hf hf2).mpr ?_⟩
    rw [← lexAt_iff _ _ hpw, lexAt_congr _ _ (fun k hk => M.valAt_sgOf _ f hf k hk)
      (fun k hk => M.valAt_sgOf _ f2 hf2 k hk)] at hl
    exact hl

/-- G13 の「(番号, 値の列) が a を定義する」。 -/
def definesL (d : Nat × List α) (a : α) : Prop :=
  ∃ n τ, DefCode M.mem n ∧ DefinesM M.mem n τ X a ∧ d = M.enc n τ

omit Zx hX in
theorem newLessD_iff (a b : α)
    (hcmp : ∀ n τ n2 τ2 y y2, DefinesM M.mem n τ X y → DefinesM M.mem n2 τ2 X y2 →
      (DefLess M.mem n τ n2 τ2 Wg ↔ G13.defLt (InPair M.mem Wg) (M.enc n τ) (M.enc n2 τ2))) :
    M.NewLessD X Wg a b ↔ G13.newLess (InPair M.mem Wg) (M.definesL (X := X)) a b := by
  constructor
  · rintro ⟨n, t, hc, hd, hall⟩
    refine ⟨M.enc n t, ⟨n, t, hc, hd, rfl⟩, ?_⟩
    rintro d' ⟨n2, t2, hc2, hd2, rfl⟩
    exact (hcmp n t n2 t2 a b hd hd2).mp (hall n2 t2 hc2 hd2)
  · rintro ⟨d, ⟨n, t, hc, hd, rfl⟩, hall⟩
    exact ⟨n, t, hc, hd, fun n2 t2 hc2 hd2 => (hcmp n t n2 t2 a b hd hd2).mpr (hall _ ⟨n2, t2, hc2, hd2, rfl⟩)⟩

theorem dfun : ∀ d y y', M.definesL (X := X) d y → M.definesL (X := X) d y' → y = y' := by
  rintro d y y' ⟨n, t, _, hd, rfl⟩ ⟨n', t', _, hd', e⟩
  obtain ⟨⟨m, rfl⟩, _, f, hf, _, rfl⟩ := M.defines_shape Zx hX hd
  obtain ⟨⟨m', rfl⟩, _, f', hf', _, rfl⟩ := M.defines_shape Zx hX hd'
  simp only [enc, mOf_num, Prod.mk.injEq] at e
  obtain ⟨em, el⟩ := e
  subst em
  rw [List.map_inj_left] at el
  have ef : ∀ k, k ∈ M.Ks (M.num m) → f k = f' k := by
    intro k hk
    have := el k hk
    rwa [M.valAt_sgOf _ f hf k hk, M.valAt_sgOf _ f' hf' k hk] at this
  rw [M.sgOf_congr _ ef] at hd
  exact M.defines_unique hd hd'

theorem dok : ∀ d y, M.definesL (X := X) d y →
    d.2.length = (M.Ks (M.num d.1)).length ∧ ∀ x, x ∈ d.2 → M.mem x X := by
  rintro d y ⟨n, t, _, hd, rfl⟩
  obtain ⟨⟨m, rfl⟩, _, f, hf, hfX, rfl⟩ := M.defines_shape Zx hX hd
  simp only [enc, mOf_num, List.length_map, true_and]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  rw [M.valAt_sgOf _ f hf k hk]; exact hfX k hk

end Enc

/-! ### 次の段の順序は整列順序 -/

section Succ
variable (Zx : M.Zax) {X Wg X1 W1 : α} (hX : M.H X) (hs : StepM M.mem X Wg X1 W1)
  (irr : ∀ a, ¬ InPair M.mem Wg a a)
  (tr : ∀ a b c, InPair M.mem Wg a b → InPair M.mem Wg b c → InPair M.mem Wg a c)
  (tot : ∀ a b, M.mem a X → M.mem b X → a ≠ b → InPair M.mem Wg a b ∨ InPair M.mem Wg b a)
  (wf : WellFounded (InPair M.mem Wg))
include Zx hX hs

theorem hasDef {a : α} (ha : M.mem a X1) : ∃ d, M.definesL (X := X) d a := by
  obtain ⟨n, t, hc, hd⟩ := (M.step_mem hs a).mp ha
  exact ⟨_, n, t, hc, hd, rfl⟩

/-- W1 は、G13 の次の段の順序 succLt と一致する。 -/
theorem step_succLt (a b : α) (ha : M.mem a X1) (hb : M.mem b X1) :
    InPair M.mem W1 a b ↔ G13.succLt (InPair M.mem Wg) (fun x => M.mem x X) (M.definesL (X := X)) a b := by
  rw [M.step_rule hs a b ha hb]
  unfold G13.succLt G13.NL
  rw [M.newLessD_iff a b (fun n τ n2 τ2 y y2 hd hd2 => M.defLess_iff Zx hX hd hd2)]
  have h1 := M.hasDef Zx hX hs ha
  have h2 := M.hasDef Zx hX hs hb
  simp only [h1, h2, and_true]

include irr tr tot wf in
/-- 次の段の順序 W1 は X1 上の狭義の整列順序で、X の上では < と一致し、X は始切片。 -/
theorem step_wo :
    WellFounded (InPair M.mem W1) ∧
    (∀ a, ¬ InPair M.mem W1 a a) ∧
    (∀ a b c, InPair M.mem W1 a b → InPair M.mem W1 b c → InPair M.mem W1 a c) ∧
    (∀ a b, M.mem a X1 → M.mem b X1 → a ≠ b → InPair M.mem W1 a b ∨ InPair M.mem W1 b a) ∧
    (∀ a b, M.mem a X → M.mem b X → M.mem a X1 → M.mem b X1 → (InPair M.mem W1 a b ↔ InPair M.mem Wg a b)) ∧
    (∀ a b, M.mem b X → InPair M.mem W1 a b → M.mem a X) := by
  let R := InPair M.mem Wg
  let Xp := fun x => M.mem x X
  let len := fun m => (M.Ks (M.num m)).length
  have hdok := M.dok Zx hX (X := X)
  have hdfun := M.dfun Zx hX (X := X)
  have inX1 : ∀ a b, InPair M.mem W1 a b → M.mem a X1 ∧ M.mem b X1 := by
    rintro a b ⟨q, hq, hp⟩
    obtain ⟨a', b', hp', ha, hb⟩ := M.step_shape hs hq
    obtain ⟨rfl, rfl⟩ := M.pair_unique hp hp'
    exact ⟨ha, hb⟩
  have conv : ∀ a b, InPair M.mem W1 a b ↔ (M.mem a X1 ∧ M.mem b X1 ∧ G13.succLt R Xp (M.definesL (X := X)) a b) := by
    intro a b
    constructor
    · intro h
      obtain ⟨ha, hb⟩ := inX1 a b h
      exact ⟨ha, hb, (M.step_succLt Zx hX hs a b ha hb).mp h⟩
    · rintro ⟨ha, hb, h⟩; exact (M.step_succLt Zx hX hs a b ha hb).mpr h
  have swf := G13.succ_wf R Xp irr tr tot wf len (M.definesL (X := X)) hdok
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subrelation.wf (fun h => ((conv _ _).mp h).2.2) swf
  · intro a h
    obtain ⟨_, _, h⟩ := (conv a a).mp h
    rcases h with ⟨_, _, h⟩ | ⟨ha, hna⟩ | ⟨_, _, hnl, _⟩
    · exact irr a h
    · exact hna ha
    · exact G13.newLess_irrefl R irr tr (M.definesL (X := X)) hdfun a hnl
  · intro a b c hab hbc
    obtain ⟨ha, hb, hab⟩ := (conv a b).mp hab
    obtain ⟨_, hc, hbc⟩ := (conv b c).mp hbc
    refine (conv a c).mpr ⟨ha, hc, ?_⟩
    rcases hab with ⟨xa, xb, r1⟩ | ⟨xa, nxb⟩ | ⟨nxa, nxb, nl1⟩ <;>
      rcases hbc with ⟨xb', xc, r2⟩ | ⟨xb', nxc⟩ | ⟨nxb', nxc, nl2⟩
    · exact Or.inl ⟨xa, xc, tr a b c r1 r2⟩
    · exact Or.inr (Or.inl ⟨xa, nxc⟩)
    · exact absurd xb nxb'
    · exact absurd xb' nxb
    · exact absurd xb' nxb
    · exact Or.inr (Or.inl ⟨xa, nxc⟩)
    · exact absurd xb' nxb
    · exact absurd xb' nxb
    · exact Or.inr (Or.inr ⟨nxa, nxc, G13.newLess_trans R tr (M.definesL (X := X)) a b c nl1.2.2 nl1.1 nl2.1,
        nl1.2.1, nl2.2.2⟩)
  · intro a b ha hb hne
    have da := M.hasDef Zx hX hs ha
    have db := M.hasDef Zx hX hs hb
    rw [conv, conv]
    by_cases xa : M.mem a X <;> by_cases xb : M.mem b X
    · rcases tot a b xa xb hne with h | h
      · exact Or.inl ⟨ha, hb, Or.inl ⟨xa, xb, h⟩⟩
      · exact Or.inr ⟨hb, ha, Or.inl ⟨xb, xa, h⟩⟩
    · exact Or.inl ⟨ha, hb, Or.inr (Or.inl ⟨xa, xb⟩)⟩
    · exact Or.inr ⟨hb, ha, Or.inr (Or.inl ⟨xb, xa⟩)⟩
    · rcases G13.newLess_total R Xp irr tr tot wf len (M.definesL (X := X)) hdfun hdok a b hne da db with h | h
      · exact Or.inl ⟨ha, hb, Or.inr (Or.inr ⟨xa, xb, h, da, db⟩)⟩
      · exact Or.inr ⟨hb, ha, Or.inr (Or.inr ⟨xb, xa, h, db, da⟩)⟩
  · intro a b xa xb ha hb
    rw [conv]
    constructor
    · rintro ⟨_, _, ⟨_, _, h⟩ | ⟨_, nxb⟩ | ⟨nxa, _⟩⟩
      · exact h
      · exact absurd xb nxb
      · exact absurd xa nxa
    · intro h; exact ⟨ha, hb, Or.inl ⟨xa, xb, h⟩⟩
  · intro a b xb h
    obtain ⟨_, _, h⟩ := (conv a b).mp h
    rcases h with ⟨xa, _, _⟩ | ⟨xa, _⟩ | ⟨_, nxb, _⟩
    · exact xa
    · exact xa
    · exact absurd xb nxb

end Succ

end Model

#print axioms Model.step_succLt
#print axioms Model.step_wo
end Tr
