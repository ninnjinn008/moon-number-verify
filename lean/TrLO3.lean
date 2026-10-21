/-
  書き写しの検証（改訂49）：l_order(λ, D, WL) の WL は D 上の狭義の整列順序（G13 の主張）。

  ・self_def：X が推移的なら、X の各元 x は「x_0 ∈ x_1」（パラメータ x）で X 上定義される。よって X ⊆ Def(X)。
  ・ord_trich：順序数（推移的で、元も推移的）の ∈ は三分律を満たす。
  ・lorder_wo：段階の表の各値 (X_γ, W_γ) は狭義の整列順序で、γ₁ ∈ γ なら (X_γ, W_γ) は (X_γ₁, W_γ₁) の終延長。
    後者の段は step_wo（TrLO2）、極限の段は G13.union_wf による。
  仮定：M = V_{κ+1}、H = V_κ では、M の元の元は H に属する（hM）。
-/
import TrLO2
namespace Tr

/-- 「x_0 ∈ x_1」の記号列：( x_0 ∈ x_1 )。 -/
def tab01 : List (List Nat) := [[4, 0, 0, 0], [7, 1, 0, 0], [9, 5, 0, 2], [7, 1, 1, 0], [5, 0, 0, 0]]
def S01 (i j : Nat) : Nat := (tab01.getD i []).getD j 0
def φ01 : G5.Form := .elem (.var 0) (.var 1)

theorem φ01_wf : φ01.wf := by simp [φ01, G5.Form.wf, G5.Term.wf]
theorem φ01_occ : G5.Occ (str S01 5) 0 φ01.toks := by
  simp only [φ01, G5.Form.toks, G5.Term.toks, List.cons_append, List.nil_append, G5.Occ]
  decide
theorem φ01_len : 5 = φ01.toks.length := by simp [φ01, G5.Form.toks, G5.Term.toks]
theorem φ01_θ : ∀ n, n < 5 → str S01 5 n ≠ some (.fn 1 1) := by
  intro n hn
  rcases n with _ | _ | _ | _ | _ | n
  all_goals first | decide | omega
theorem φ01_pure : Model.PureS S01 5 := by
  intro i hi
  rcases i with _ | _ | _ | _ | _ | i
  all_goals first | omega | (refine ⟨fun k => ?_, fun f a => ?_, fun r a => ?_⟩ <;> simp [S01, tab01, tok, decode, punctTok])

namespace Model
variable {α : Type} (M : Model α)

theorem seq4_ex (h : Nat) (S : Nat → Nat → Nat) : ∃ s, M.SeqRep4 s h S := by
  have hel : ∀ x, x ∈ (List.range h).map (fun i => M.pr (M.num i) (M.sset 4 (S i))) → M.H x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact (M.pr_spec (M.H_num i) (M.sset_spec 4 (S i)).1).1
  have := M.set_spec _ hel
  refine ⟨M.set ((List.range h).map (fun i => M.pr (M.num i) (M.sset 4 (S i)))), fun x hx => ?_, fun i hi => ?_⟩
  · rw [this.2, List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, List.mem_range.mp hi, _, (M.pr_spec (M.H_num i) (M.sset_spec 4 (S i)).1).2, (M.sset_spec 4 (S i)).2⟩
  · exact ⟨_, (this.2 _).mpr (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩), _,
      (M.pr_spec (M.H_num i) (M.sset_spec 4 (S i)).1).2, (M.sset_spec 4 (S i)).2⟩

theorem defCode_of {n τ X y : α} (h : DefinesM M.mem n τ X y) : DefCode M.mem n := by
  obtain ⟨s, hfm, hmc, h', hsw, hp, _⟩ := h
  exact ⟨s, hfm, hmc, h', hsw, hp⟩

/-- X が推移的なら、X の元 x は「x_0 ∈ x_1」（x_1 = x）で X 上定義される。 -/
theorem self_def (Zx : M.Zax) {X x : α} (hX : M.H X) (hXt : Trans M.mem X) (hx : M.mem x X) :
    ∃ n t, DefCode M.mem n ∧ DefinesM M.mem n t X x := by
  obtain ⟨s, hs⟩ := M.seq4_ex 5 S01
  let ρ : Nat → {z // M.mem z X} := fun _ => ⟨x, hx⟩
  have hd := (M.defines_iff Zx hX hXt ⟨x, hx⟩ hs φ01 φ01_wf φ01_occ φ01_len φ01_θ φ01_pure
    (M.sgOf (KL S01 5) (fun k => (ρ k).1)) x).mpr
    ⟨ρ, rfl, fun z hz => hXt x hx z hz, fun z hz => by
      show M.mem z x ↔ M.mem (G5.upd ρ 0 ⟨z, hz⟩ 0).1 (G5.upd ρ 0 ⟨z, hz⟩ 1).1
      simp [G5.upd, ρ]⟩
  exact ⟨_, _, M.defCode_of hd, hd⟩

/-! ### 順序数の三分律 -/

theorem ord_mem {a z : α} (ha : OrdinalM M.mem a) (hz : M.mem z a) : OrdinalM M.mem z :=
  ⟨ha.2 z hz, fun w hw => ha.2 w (ha.1 z hz w hw)⟩

theorem ord_trich : ∀ a b : α, OrdinalM M.mem a → OrdinalM M.mem b → M.mem a b ∨ a = b ∨ M.mem b a := by
  intro a
  induction a using M.wf.induction with
  | _ a iha =>
  intro b
  induction b using M.wf.induction with
  | _ b ihb =>
  intro ha hb
  by_cases h1 : M.mem b a
  · exact Or.inr (Or.inr h1)
  by_cases h2 : M.mem a b
  · exact Or.inl h2
  refine Or.inr (Or.inl (M.ext _ _ (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)))
  · rcases iha x hx b (M.ord_mem ha hx) hb with h | rfl | h
    · exact h
    · exact absurd hx h1
    · exact absurd (ha.1 x hx b h) h1
  · rcases ihb x hx ha (M.ord_mem hb hx) with h | rfl | h
    · exact absurd (hb.1 x hx a h) h2
    · exact absurd hx h2
    · exact h

/-! ### 整列順序と終延長 -/

/-- (X, W) は狭義の整列順序（W の元は X の元の順序対）。 -/
def WO (X W : α) : Prop :=
  (∀ q, M.mem q W → ∃ a b, Pair M.mem q a b ∧ M.mem a X ∧ M.mem b X) ∧
  WellFounded (InPair M.mem W) ∧ (∀ a, ¬ InPair M.mem W a a) ∧
  (∀ a b c, InPair M.mem W a b → InPair M.mem W b c → InPair M.mem W a c) ∧
  (∀ a b, M.mem a X → M.mem b X → a ≠ b → InPair M.mem W a b ∨ InPair M.mem W b a)

/-- (X1, W1) は (X, W) の終延長。 -/
def Ext (X W X1 W1 : α) : Prop :=
  (∀ a, M.mem a X → M.mem a X1) ∧ (∀ a b, M.mem a X → M.mem b X → (InPair M.mem W1 a b ↔ InPair M.mem W a b)) ∧
  (∀ a b, M.mem b X → InPair M.mem W1 a b → M.mem a X)

theorem inPair_shape {X W a b : α} (hw : ∀ q, M.mem q W → ∃ a b, Pair M.mem q a b ∧ M.mem a X ∧ M.mem b X)
    (h : InPair M.mem W a b) : M.mem a X ∧ M.mem b X := by
  obtain ⟨q, hq, hp⟩ := h
  obtain ⟨a', b', hp', ha, hb⟩ := hw q hq
  obtain ⟨rfl, rfl⟩ := M.pair_unique hp hp'
  exact ⟨ha, hb⟩

theorem ext_refl {X W : α} (hw : ∀ q, M.mem q W → ∃ a b, Pair M.mem q a b ∧ M.mem a X ∧ M.mem b X) :
    M.Ext X W X W :=
  ⟨fun _ h => h, fun _ _ _ _ => Iff.rfl, fun a b _ h => (M.inPair_shape hw h).1⟩

theorem ext_trans {X W X1 W1 X2 W2 : α} (h1 : M.Ext X W X1 W1) (h2 : M.Ext X1 W1 X2 W2) : M.Ext X W X2 W2 := by
  refine ⟨fun a ha => h2.1 a (h1.1 a ha), fun a b ha hb => ?_, fun a b hb h => ?_⟩
  · rw [h2.2.1 a b (h1.1 a ha) (h1.1 b hb), h1.2.1 a b ha hb]
  · have ha1 := h2.2.2 a b (h1.1 b hb) h
    exact h1.2.2 a b hb ((h2.2.1 a b ha1 (h1.1 b hb)).mp h)

theorem empty_wo {X W : α} (hX : Empty M.mem X) (hW : Empty M.mem W) : M.WO X W := by
  have nw : ∀ a b, ¬ InPair M.mem W a b := fun a b ⟨q, hq, _⟩ => hW q hq
  refine ⟨fun q hq => absurd hq (hW q), ⟨fun a => ⟨a, fun b h => absurd h (nw b a)⟩⟩, fun a => nw a a,
    fun a b _ h => absurd h (nw a b), fun a _ ha => absurd ha (hX a)⟩

/-! ### 段階の表の値 -/

section Main
variable (Zx : M.Zax) (hM : ∀ x y, M.mem x y → M.H x)
include Zx hM

theorem look_H {T g X W : α} (h : M.LookT T g X W) : M.H X := by
  obtain ⟨_, _, p, _, hXW⟩ := h
  obtain ⟨s, _, hXs, _⟩ := Tr.pair_dbl M.mem hXW
  exact hM X s hXs

/-- 次の段：(X, W) が推移的な整列順序なら、step の結果も推移的な整列順序で、終延長。 -/
theorem step_good {X W X1 W1 : α} (hX : M.H X) (hXt : Trans M.mem X) (hwo : M.WO X W)
    (hs : StepM M.mem X W X1 W1) : Trans M.mem X1 ∧ M.WO X1 W1 ∧ M.Ext X W X1 W1 := by
  obtain ⟨hsh, hwf, hirr, htr, htot⟩ := hwo
  obtain ⟨wf1, irr1, tr1, tot1, agree, init⟩ := M.step_wo Zx hX hs hirr htr htot hwf
  have sub : ∀ a, M.mem a X → M.mem a X1 := fun a ha => (M.step_mem hs a).mpr (M.self_def Zx hX hXt ha)
  refine ⟨?_, ⟨fun q hq => M.step_shape hs hq, wf1, irr1, tr1, tot1⟩, sub,
    fun a b ha hb => agree a b ha hb (sub a ha) (sub b hb), init⟩
  intro y hy z hz
  obtain ⟨n, t, _, hd⟩ := (M.step_mem hs y).mp hy
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsub, _⟩ := hd
  exact sub z (hsub z hz)

/-- 段階の表の各値は推移的な狭義の整列順序で、前の段の値の終延長。 -/
theorem lorder_wo {lam D WL : α} (h : LOrderM M.mem lam D WL) : Trans M.mem D ∧ M.WO D WL := by
  obtain ⟨hord, l1, hl1, T, ⟨_, hf⟩, hall, hlam⟩ := h
  have l1tr : ∀ g, M.mem g l1 → ∀ w, M.mem w g → M.mem w l1 := by
    intro g hg w hw
    rcases (hl1 g).mp hg with hg | rfl
    · exact (hl1 w).mpr (Or.inl (hord.1 g hg w hw))
    · exact (hl1 w).mpr (Or.inl hw)
  have l1ord : ∀ g, M.mem g l1 → OrdinalM M.mem g := by
    intro g hg
    rcases (hl1 g).mp hg with hg | rfl
    · exact M.ord_mem hord hg
    · exact hord
  have vok : ∀ g, M.mem g l1 → ∀ X W, M.LookT T g X W → ValueOk M.mem T g X W := by
    intro g hg X W hl
    obtain ⟨X0, W0, hl0, hv⟩ := (M.atT_iff T g _).mp (hall g hg)
    obtain ⟨rfl, rfl⟩ := M.look_unique hf hl0 hl
    exact hv
  have lex : ∀ g, M.mem g l1 → ∃ X W, M.LookT T g X W := by
    intro g hg
    obtain ⟨X, W, hl, _⟩ := (M.atT_iff T g _).mp (hall g hg)
    exact ⟨X, W, hl⟩
  -- 主張 Q(g)
  have key : ∀ g, M.mem g l1 → ∀ X W, M.LookT T g X W →
      Trans M.mem X ∧ M.WO X W ∧ ∀ g1, M.mem g1 g → ∀ X1 W1, M.LookT T g1 X1 W1 → M.Ext X1 W1 X W := by
    intro g
    induction g using M.wf.induction with
    | _ g ih =>
    intro hg X W hl
    have hv := vok g hg X W hl
    by_cases he : Empty M.mem g
    · obtain ⟨eX, eW⟩ := hv.1 he
      exact ⟨fun z hz => absurd hz (eX z), M.empty_wo eX eW, fun g1 hg1 => absurd hg1 (he g1)⟩
    by_cases hsu : IsSucc M.mem g
    · obtain ⟨w, hw, hsw⟩ := hsu
      obtain ⟨X0, W0, hl0, hst⟩ := (M.atT_iff T w _).mp (hv.2.1 w hw hsw)
      obtain ⟨ht0, hwo0, hext0⟩ := ih w hw (l1tr g hg w hw) X0 W0 hl0
      obtain ⟨ht, hwo, hext⟩ := M.step_good Zx hM (M.look_H Zx hM hl0) ht0 hwo0 hst
      refine ⟨ht, hwo, fun g1 hg1 X1 W1 hl1' => ?_⟩
      rcases (hsw g1).mp hg1 with h | rfl
      · exact M.ext_trans (hext0 g1 h X1 W1 hl1') hext
      · obtain ⟨rfl, rfl⟩ := M.look_unique hf hl0 hl1'
        exact hext
    -- 極限の段
    have hu := hv.2.2 ⟨he, hsu⟩
    have ihg : ∀ g1, M.mem g1 g → ∀ X1 W1, M.LookT T g1 X1 W1 →
        Trans M.mem X1 ∧ M.WO X1 W1 ∧ ∀ g2, M.mem g2 g1 → ∀ X2 W2, M.LookT T g2 X2 W2 → M.Ext X2 W2 X1 W1 :=
      fun g1 hg1 => ih g1 hg1 (l1tr g hg g1 hg1)
    have comp : ∀ g1 g2, M.mem g1 g → M.mem g2 g → ∀ X1 W1 X2 W2, M.LookT T g1 X1 W1 → M.LookT T g2 X2 W2 →
        M.Ext X1 W1 X2 W2 ∨ M.Ext X2 W2 X1 W1 := by
      intro g1 g2 hg1 hg2 X1 W1 X2 W2 h1 h2
      rcases M.ord_trich g1 g2 (l1ord g1 (l1tr g hg g1 hg1)) (l1ord g2 (l1tr g hg g2 hg2)) with e | rfl | e
      · exact Or.inl ((ihg g2 hg2 X2 W2 h2).2.2 g1 e X1 W1 h1)
      · obtain ⟨rfl, rfl⟩ := M.look_unique hf h1 h2; exact Or.inl (M.ext_refl (ihg g1 hg1 X1 W1 h1).2.1.1)
      · exact Or.inr ((ihg g1 hg1 X1 W1 h1).2.2 g2 e X2 W2 h2)
    -- 和の元
    have memX : ∀ a, M.mem a X ↔ ∃ g1 X1 W1, M.mem g1 g ∧ M.LookT T g1 X1 W1 ∧ M.mem a X1 := by
      intro a; constructor
      · intro ha
        obtain ⟨g1, hg1, hat⟩ := hu.1.1 a ha
        obtain ⟨X1, W1, h1, ha1⟩ := (M.atT_iff T g1 _).mp hat
        exact ⟨g1, X1, W1, hg1, h1, ha1⟩
      · rintro ⟨g1, X1, W1, hg1, h1, ha1⟩
        obtain ⟨X1', W1', h1', hsub⟩ := (M.atT_iff T g1 _).mp (hu.1.2 g1 hg1)
        obtain ⟨rfl, rfl⟩ := M.look_unique hf h1 h1'
        exact hsub a ha1
    have memW : ∀ q, M.mem q W ↔ ∃ g1 X1 W1, M.mem g1 g ∧ M.LookT T g1 X1 W1 ∧ M.mem q W1 := by
      intro q; constructor
      · intro hq
        obtain ⟨g1, hg1, hat⟩ := hu.2.1 q hq
        obtain ⟨X1, W1, h1, hq1⟩ := (M.atT_iff T g1 _).mp hat
        exact ⟨g1, X1, W1, hg1, h1, hq1⟩
      · rintro ⟨g1, X1, W1, hg1, h1, hq1⟩
        obtain ⟨X1', W1', h1', hsub⟩ := (M.atT_iff T g1 _).mp (hu.2.2 g1 hg1)
        obtain ⟨rfl, rfl⟩ := M.look_unique hf h1 h1'
        exact hsub q hq1
    have inW : ∀ a b, InPair M.mem W a b ↔ ∃ g1 X1 W1, M.mem g1 g ∧ M.LookT T g1 X1 W1 ∧ InPair M.mem W1 a b := by
      intro a b; constructor
      · rintro ⟨q, hq, hp⟩
        obtain ⟨g1, X1, W1, hg1, h1, hq1⟩ := (memW q).mp hq
        exact ⟨g1, X1, W1, hg1, h1, q, hq1, hp⟩
      · rintro ⟨g1, X1, W1, hg1, h1, q, hq1, hp⟩
        exact ⟨q, (memW q).mpr ⟨g1, X1, W1, hg1, h1, hq1⟩, hp⟩
    -- 段の値の終延長
    have extg : ∀ g1, M.mem g1 g → ∀ X1 W1, M.LookT T g1 X1 W1 → M.Ext X1 W1 X W := by
      intro g1 hg1 X1 W1 h1
      have wo1 := (ihg g1 hg1 X1 W1 h1).2.1
      refine ⟨fun a ha => (memX a).mpr ⟨g1, X1, W1, hg1, h1, ha⟩, fun a b ha hb => ?_, fun a b hb hab => ?_⟩
      · rw [inW]
        constructor
        · rintro ⟨g2, X2, W2, hg2, h2, h⟩
          have wo2 := (ihg g2 hg2 X2 W2 h2).2.1
          rcases comp g1 g2 hg1 hg2 X1 W1 X2 W2 h1 h2 with e | e
          · exact (e.2.1 a b ha hb).mp h
          · obtain ⟨ha2, hb2⟩ := M.inPair_shape wo2.1 h
            exact (e.2.1 a b ha2 hb2).mpr h
        · intro h; exact ⟨g1, X1, W1, hg1, h1, h⟩
      · obtain ⟨g2, X2, W2, hg2, h2, h⟩ := (inW a b).mp hab
        have wo2 := (ihg g2 hg2 X2 W2 h2).2.1
        rcases comp g1 g2 hg1 hg2 X1 W1 X2 W2 h1 h2 with e | e
        · exact e.2.2 a b hb h
        · exact e.1 a (M.inPair_shape wo2.1 h).1
    refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, extg⟩
    · intro y hy z hz
      obtain ⟨g1, X1, W1, hg1, h1, hy1⟩ := (memX y).mp hy
      exact (memX z).mpr ⟨g1, X1, W1, hg1, h1, (ihg g1 hg1 X1 W1 h1).1 y hy1 z hz⟩
    · intro q hq
      obtain ⟨g1, X1, W1, hg1, h1, hq1⟩ := (memW q).mp hq
      obtain ⟨a, b, hp, ha, hb⟩ := (ihg g1 hg1 X1 W1 h1).2.1.1 q hq1
      exact ⟨a, b, hp, (extg g1 hg1 X1 W1 h1).1 a ha, (extg g1 hg1 X1 W1 h1).1 b hb⟩
    · -- 整礎性：G13.union_wf
      let ι := {x // M.mem x g}
      have hex : ∀ β : ι, ∃ XW : α × α, M.LookT T β.1 XW.1 XW.2 := by
        intro β; obtain ⟨X1, W1, h1⟩ := lex β.1 (l1tr g hg β.1 β.2); exact ⟨(X1, W1), h1⟩
      let V : ι → α × α := fun β => Classical.choose (hex β)
      have hV : ∀ β, M.LookT T β.1 (V β).1 (V β).2 := fun β => Classical.choose_spec (hex β)
      have wfu := G13.union_wf (fun β γ : ι => M.Ext (V β).1 (V β).2 (V γ).1 (V γ).2)
        (fun β γ => comp β.1 γ.1 β.2 γ.2 _ _ _ _ (hV β) (hV γ))
        (fun β a => M.mem a (V β).1) (fun β a b => InPair M.mem (V β).2 a b)
        (fun β a b h => M.inPair_shape (ihg β.1 β.2 _ _ (hV β)).2.1.1 h)
        (fun β => (ihg β.1 β.2 _ _ (hV β)).2.1.2.1)
        (fun β γ e => e.1) (fun β γ e => e.2.1) (fun β γ e => e.2.2)
      apply Subrelation.wf _ wfu
      intro a b h
      obtain ⟨g1, X1, W1, hg1, h1, h⟩ := (inW a b).mp h
      obtain ⟨rfl, rfl⟩ := M.look_unique hf h1 (hV ⟨g1, hg1⟩)
      exact ⟨⟨g1, hg1⟩, h⟩
    · intro a h
      obtain ⟨g1, X1, W1, hg1, h1, h⟩ := (inW a a).mp h
      exact (ihg g1 hg1 X1 W1 h1).2.1.2.2.1 a h
    · intro a b c hab hbc
      obtain ⟨g1, X1, W1, hg1, h1, hab⟩ := (inW a b).mp hab
      obtain ⟨g2, X2, W2, hg2, h2, hbc⟩ := (inW b c).mp hbc
      have wo1 := (ihg g1 hg1 X1 W1 h1).2.1
      have wo2 := (ihg g2 hg2 X2 W2 h2).2.1
      rw [inW]
      rcases comp g1 g2 hg1 hg2 X1 W1 X2 W2 h1 h2 with e | e
      · obtain ⟨ha, hb⟩ := M.inPair_shape wo1.1 hab
        exact ⟨g2, X2, W2, hg2, h2, wo2.2.2.2.1 a b c ((e.2.1 a b ha hb).mpr hab) hbc⟩
      · obtain ⟨hb, hc⟩ := M.inPair_shape wo2.1 hbc
        exact ⟨g1, X1, W1, hg1, h1, wo1.2.2.2.1 a b c hab ((e.2.1 b c hb hc).mpr hbc)⟩
    · intro a b ha hb hne
      obtain ⟨g1, X1, W1, hg1, h1, ha1⟩ := (memX a).mp ha
      obtain ⟨g2, X2, W2, hg2, h2, hb2⟩ := (memX b).mp hb
      have wo1 := (ihg g1 hg1 X1 W1 h1).2.1
      have wo2 := (ihg g2 hg2 X2 W2 h2).2.1
      rw [inW, inW]
      rcases comp g1 g2 hg1 hg2 X1 W1 X2 W2 h1 h2 with e | e
      · rcases wo2.2.2.2.2 a b (e.1 a ha1) hb2 hne with h | h
        · exact Or.inl ⟨g2, X2, W2, hg2, h2, h⟩
        · exact Or.inr ⟨g2, X2, W2, hg2, h2, h⟩
      · rcases wo1.2.2.2.2 a b ha1 (e.1 b hb2) hne with h | h
        · exact Or.inl ⟨g1, X1, W1, hg1, h1, h⟩
        · exact Or.inr ⟨g1, X1, W1, hg1, h1, h⟩
  have hlam1 : M.mem lam l1 := (hl1 lam).mpr (Or.inr rfl)
  obtain ⟨X, W, hl, rfl, rfl⟩ := (M.atT_iff T lam _).mp hlam
  obtain ⟨ht, hwo, _⟩ := key lam hlam1 X W hl
  exact ⟨ht, hwo⟩

end Main
end Model

#print axioms Model.self_def
#print axioms Model.lorder_wo
end Tr
