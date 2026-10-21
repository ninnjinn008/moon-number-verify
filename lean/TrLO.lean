/-
  書き写しの検証（改訂49）：L の段階の層（lorder.py）の step と l_order の意味。

  ・step_mem：step(X, <, X1, W1) なら X1 = Def(X) = { y : ある純粋な式の番号 n とパラメータ τ について (n, τ) が X 上で y を定義する }。
    （defines の中身は TrL.lean の defines_iff で Tarski の意味論に置き換わる。）
  ・step_rule：W1 の順序は、古い元どうしは <、古い元は新しい元より前、新しい元どうしは
    「a のある定義が b のどの定義よりも ≺ で小さい」（DT によらない形 NewLessD）。
  ・step_unique：X と < が同じなら、step の X1, W1 は一つに定まる。
  ・lorder_unique：l_order(λ, D, WL) を満たす D, WL は λ ごとに一つに定まる（段階の表 T についての ∈ に関する帰納法）。
-/
import TrL
namespace Tr

namespace Model
variable {α : Type} (M : Model α)

/-! ### 定義の表の行 -/

theorem defEntry_iff {q nt y n t : α} (h1 : Pair M.mem q nt y) (h2 : Pair M.mem nt n t) (P : α → α → α → Prop) :
    DefEntry M.mem q P ↔ P n t y := by
  constructor
  · rintro ⟨nt', y', h1', n', t', h2', hP⟩
    obtain ⟨rfl, rfl⟩ := M.pair_unique h1 h1'
    obtain ⟨rfl, rfl⟩ := M.pair_unique h2 h2'
    exact hP
  · intro hP; exact ⟨nt, y, h1, n, t, h2, hP⟩

/-- 新しい元の比較（表 DT によらない形）。 -/
def NewLessD (X Wg a b : α) : Prop :=
  ∃ n t, DefCode M.mem n ∧ DefinesM M.mem n t X a ∧
    ∀ n2 t2, DefCode M.mem n2 → DefinesM M.mem n2 t2 X b → DefLess M.mem n t n2 t2 Wg

section Table
variable {X DT : α} (hDT : DefTable M.mem X DT)
include hDT

theorem entry_ok {q : α} (hq : M.mem q DT) :
    DefEntry M.mem q (fun n t y => DefCode M.mem n ∧ DefinesM M.mem n t X y) := by
  obtain ⟨nt, y, h1, n, t, h2, hc⟩ := hDT.1 q hq
  exact ⟨nt, y, h1, n, t, h2, hc, (hDT.2 n hc t y).mpr ⟨q, hq, nt, h1, h2⟩⟩

theorem entry_ex {n t y : α} (hc : DefCode M.mem n) (hd : DefinesM M.mem n t X y) :
    ∃ q, M.mem q DT ∧ ∃ nt, Pair M.mem q nt y ∧ Pair M.mem nt n t := by
  obtain ⟨r, hr, nt, h1, h2⟩ := (hDT.2 n hc t y).mp hd
  exact ⟨r, hr, nt, h1, h2⟩

theorem newLess_iff (Wg a b : α) : NewLess M.mem a b DT Wg ↔ M.NewLessD X Wg a b := by
  constructor
  · rintro ⟨q, hq, nt, y, h1, n, t, h2, rfl, hall⟩
    have hok := (M.defEntry_iff h1 h2 _).mp (M.entry_ok hDT hq)
    refine ⟨n, t, hok.1, hok.2, fun n2 t2 hc2 hd2 => ?_⟩
    obtain ⟨r, hr, nt2, h1', h2'⟩ := M.entry_ex hDT hc2 hd2
    exact (M.defEntry_iff h1' h2' _).mp (hall r hr) rfl
  · rintro ⟨n, t, hc, hd, hall⟩
    obtain ⟨q, hq, nt, h1, h2⟩ := M.entry_ex hDT hc hd
    refine ⟨q, hq, nt, a, h1, n, t, h2, rfl, fun q2 hq2 => ?_⟩
    obtain ⟨nt2, y2, h1', n2, t2, h2', hc2, hd2⟩ := M.entry_ok hDT hq2
    exact ⟨nt2, y2, h1', n2, t2, h2', fun e => by subst e; exact hall n2 t2 hc2 hd2⟩

end Table

section Step
variable {X Wg X1 W1 : α}

/-- step の X1 は Def(X)。 -/
theorem step_mem (hs : StepM M.mem X Wg X1 W1) (y : α) :
    M.mem y X1 ↔ ∃ n t, DefCode M.mem n ∧ DefinesM M.mem n t X y := by
  obtain ⟨DT, hDT, ⟨hd1, hd2⟩, _, _⟩ := hs
  constructor
  · intro hy
    obtain ⟨q, hq, nt, y', h1, n, t, h2, rfl⟩ := hd1 y hy
    exact ⟨n, t, (M.defEntry_iff h1 h2 _).mp (M.entry_ok hDT hq)⟩
  · rintro ⟨n, t, hc, hd⟩
    obtain ⟨q, hq, nt, h1, h2⟩ := M.entry_ex hDT hc hd
    exact (M.defEntry_iff h1 h2 _).mp (hd2 q hq)

/-- step の W1 の規則（DT によらない形）。 -/
theorem step_rule (hs : StepM M.mem X Wg X1 W1) (a b : α) (ha : M.mem a X1) (hb : M.mem b X1) :
    InPair M.mem W1 a b ↔ ((M.mem a X ∧ M.mem b X ∧ InPair M.mem Wg a b) ∨ (M.mem a X ∧ ¬ M.mem b X) ∨
      (¬ M.mem a X ∧ ¬ M.mem b X ∧ M.NewLessD X Wg a b)) := by
  obtain ⟨DT, hDT, _, _, hrule⟩ := hs
  rw [hrule a ha b hb, M.newLess_iff hDT]

theorem step_shape (hs : StepM M.mem X Wg X1 W1) {q : α} (hq : M.mem q W1) :
    ∃ a b, Pair M.mem q a b ∧ M.mem a X1 ∧ M.mem b X1 := by
  obtain ⟨_, _, _, hsh, _⟩ := hs
  exact hsh q hq

end Step

/-- step の結果は一つに定まる。 -/
theorem step_unique {X Wg X1 W1 X1' W1' : α} (hs : StepM M.mem X Wg X1 W1) (hs' : StepM M.mem X Wg X1' W1') :
    X1 = X1' ∧ W1 = W1' := by
  have eX : X1 = X1' := M.ext _ _ (fun y => by rw [M.step_mem hs, M.step_mem hs'])
  subst eX
  refine ⟨rfl, M.ext _ _ (fun q => ?_)⟩
  have side : ∀ W W', StepM M.mem X Wg X1 W → StepM M.mem X Wg X1 W' → M.mem q W → M.mem q W' := by
    intro W W' h h' hq
    obtain ⟨a, b, hp, ha, hb⟩ := M.step_shape h hq
    have : InPair M.mem W' a b := by
      rw [M.step_rule h' a b ha hb, ← M.step_rule h a b ha hb]; exact ⟨q, hq, hp⟩
    obtain ⟨q', hq', hp'⟩ := this
    rw [M.pair_ext hp hp']; exact hq'
  exact ⟨side W1 W1' hs hs', side W1' W1 hs' hs⟩

/-! ### 段階の表 T -/

/-- T(g) = (X, W)。 -/
def LookT (T g X W : α) : Prop := ∃ q, M.mem q T ∧ ∃ p, Pair M.mem q g p ∧ Pair M.mem p X W

theorem atT_iff (T g : α) (body : α → α → Prop) : AtT M.mem T g body ↔ ∃ X W, M.LookT T g X W ∧ body X W := by
  constructor
  · rintro ⟨q, hq, p, hp, X, W, hXW, hb⟩; exact ⟨X, W, ⟨q, hq, p, hp, hXW⟩, hb⟩
  · rintro ⟨X, W, ⟨q, hq, p, hp, hXW⟩, hb⟩; exact ⟨q, hq, p, hp, X, W, hXW, hb⟩

def FuncT (T : α) : Prop :=
  ∀ q1, M.mem q1 T → ∀ a1 b1, Pair M.mem q1 a1 b1 → ∀ q2, M.mem q2 T → ∀ a2 b2, Pair M.mem q2 a2 b2 → a1 = a2 → b1 = b2

theorem look_unique {T g X W X' W' : α} (hf : M.FuncT T) (h : M.LookT T g X W) (h' : M.LookT T g X' W') :
    X = X' ∧ W = W' := by
  obtain ⟨q, hq, p, hp, hXW⟩ := h
  obtain ⟨q', hq', p', hp', hXW'⟩ := h'
  have := hf q hq _ _ hp q' hq' _ _ hp' rfl
  subst this
  exact M.pair_unique hXW hXW'

theorem empty_eq {a b : α} (ha : Empty M.mem a) (hb : Empty M.mem b) : a = b :=
  M.ext _ _ (fun x => ⟨fun h => absurd h (ha x), fun h => absurd h (hb x)⟩)

/-- l_order(λ, D, WL) の D と WL は λ ごとに一つに定まる。 -/
theorem lorder_unique {lam D WL D' WL' : α} (h : LOrderM M.mem lam D WL) (h' : LOrderM M.mem lam D' WL') :
    D = D' ∧ WL = WL' := by
  obtain ⟨⟨htr, _⟩, l1, hl1, T, ⟨_, hf⟩, hall, hlam⟩ := h
  obtain ⟨_, l1', hl1', T', ⟨_, hf'⟩, hall', hlam'⟩ := h'
  have el : l1 = l1' := M.ext _ _ (fun u => by rw [hl1 u, hl1' u])
  subst el
  -- l1 = λ + 1 は推移的
  have l1tr : ∀ g, M.mem g l1 → ∀ w, M.mem w g → M.mem w l1 := by
    intro g hg w hw
    rcases (hl1 g).mp hg with hg | rfl
    · exact (hl1 w).mpr (Or.inl (htr g hg w hw))
    · exact (hl1 w).mpr (Or.inl hw)
  -- 表の値は ValueOk を満たす
  have vok : ∀ (T : α), M.FuncT T → (∀ g, M.mem g l1 → AtT M.mem T g (fun X W => ValueOk M.mem T g X W)) →
      ∀ g, M.mem g l1 → ∀ X W, M.LookT T g X W → ValueOk M.mem T g X W := by
    intro T hf hall g hg X W hl
    obtain ⟨X0, W0, hl0, hv⟩ := (M.atT_iff T g _).mp (hall g hg)
    obtain ⟨rfl, rfl⟩ := M.look_unique hf hl0 hl
    exact hv
  have key : ∀ g, M.mem g l1 → ∀ X W X' W', M.LookT T g X W → M.LookT T' g X' W' → X = X' ∧ W = W' := by
    intro g
    induction g using M.wf.induction with
    | _ g ih =>
    intro hg X W X' W' hl hl'
    have hv := vok T hf hall g hg X W hl
    have hv' := vok T' hf' hall' g hg X' W' hl'
    by_cases he : Empty M.mem g
    · exact ⟨M.empty_eq (hv.1 he).1 (hv'.1 he).1, M.empty_eq (hv.1 he).2 (hv'.1 he).2⟩
    by_cases hsu : IsSucc M.mem g
    · obtain ⟨w, hw, hsw⟩ := hsu
      obtain ⟨X0, W0, hl0, hst⟩ := (M.atT_iff T w _).mp (hv.2.1 w hw hsw)
      obtain ⟨X0', W0', hl0', hst'⟩ := (M.atT_iff T' w _).mp (hv'.2.1 w hw hsw)
      obtain ⟨rfl, rfl⟩ := ih w hw (l1tr g hg w hw) X0 W0 X0' W0' hl0 hl0'
      exact M.step_unique hst hst'
    · have hu := hv.2.2 ⟨he, hsu⟩
      have hu' := hv'.2.2 ⟨he, hsu⟩
      -- 和の各成分は、前の段の値の和
      have union_eq : ∀ (Y Y' : α) (sel : α → α → α),
          (∀ g1, M.mem g1 g → ∀ X0 W0 X0' W0', M.LookT T g1 X0 W0 → M.LookT T' g1 X0' W0' → sel X0 W0 = sel X0' W0') →
          UnionOk M.mem T g Y sel → UnionOk M.mem T' g Y' sel → Y = Y' := by
        intro Y Y' sel hsel hY hY'
        apply M.ext; intro x; constructor
        · intro hx
          obtain ⟨g1, hg1, hat⟩ := hY.1 x hx
          obtain ⟨X0, W0, hl0, hx0⟩ := (M.atT_iff T g1 _).mp hat
          obtain ⟨X0', W0', hl0', hsub⟩ := (M.atT_iff T' g1 _).mp (hY'.2 g1 hg1)
          exact hsub x (hsel g1 hg1 X0 W0 X0' W0' hl0 hl0' ▸ hx0)
        · intro hx
          obtain ⟨g1, hg1, hat⟩ := hY'.1 x hx
          obtain ⟨X0', W0', hl0', hx0⟩ := (M.atT_iff T' g1 _).mp hat
          obtain ⟨X0, W0, hl0, hsub⟩ := (M.atT_iff T g1 _).mp (hY.2 g1 hg1)
          exact hsub x ((hsel g1 hg1 X0 W0 X0' W0' hl0 hl0').symm ▸ hx0)
      have ihg : ∀ g1, M.mem g1 g → ∀ X0 W0 X0' W0', M.LookT T g1 X0 W0 → M.LookT T' g1 X0' W0' →
          X0 = X0' ∧ W0 = W0' :=
        fun g1 hg1 => ih g1 hg1 (l1tr g hg g1 hg1)
      exact ⟨union_eq X X' (fun X0 _ => X0) (fun g1 hg1 a b c d h1 h2 => (ihg g1 hg1 a b c d h1 h2).1) hu.1 hu'.1,
        union_eq W W' (fun _ W0 => W0) (fun g1 hg1 a b c d h1 h2 => (ihg g1 hg1 a b c d h1 h2).2) hu.2 hu'.2⟩
  have hlam1 : M.mem lam l1 := (hl1 lam).mpr (Or.inr rfl)
  obtain ⟨X, W, hl, rfl, rfl⟩ := (M.atT_iff T lam _).mp hlam
  obtain ⟨X', W', hl', rfl, rfl⟩ := (M.atT_iff T' lam _).mp hlam'
  exact key lam hlam1 X W X' W' hl hl'

end Model

#print axioms Model.step_mem
#print axioms Model.step_unique
#print axioms Model.lorder_unique
end Tr
