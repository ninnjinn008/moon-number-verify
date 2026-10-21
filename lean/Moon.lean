/-
  月絶天葬数・別紙 G の原理の形式化（Lean 4 コアのみ、Mathlib なし）

  ・式 Fml は、生成プログラム（fol.py）と同じ原始記号 ∈, =, ¬, ∧, ∀ だけをもつ。
  ・evalU mem U φ e：二項関係 mem をもつ型 α の上で、量化子をクラス U に制限して φ を評価する。
    U = (fun _ => True) とすれば、制限のない評価（外側の宇宙 L での評価）になる。
  ・原理 A（absolute）：U が mem について推移的なら、Δ0 式は U と全体で真偽が一致する。
  ・原理 B（guarded_all, iff_all, pinned_ex）：有界でない量化子の三つの型について、
    動く範囲を U に制限しても全体に広げても真偽が変わらないための条件。
  ・原理 C（table_unique）：整礎な添字の上で、局所的な条件を満たす表は一意。
-/
namespace Moon

inductive Fml where
  | mem  : Nat → Nat → Fml
  | eq   : Nat → Nat → Fml
  | neg  : Fml → Fml
  | conj : Fml → Fml → Fml
  | all  : Nat → Fml → Fml

def upd {α : Type} (e : Nat → α) (v : Nat) (x : α) : Nat → α :=
  fun n => if n = v then x else e n

def evalU {α : Type} (mem : α → α → Prop) (U : α → Prop) : Fml → (Nat → α) → Prop
  | .mem a b, e  => mem (e a) (e b)
  | .eq a b, e   => e a = e b
  | .neg p, e    => ¬ evalU mem U p e
  | .conj p q, e => evalU mem U p e ∧ evalU mem U q e
  | .all v p, e  => ∀ x, U x → evalU mem U p (upd e v x)

/-- Δ0 式：量化子はすべて ∀v ¬(v ∈ a ∧ p) の形（a ≠ v）。
    fol.py の AllIn(v, a, q) = All(v, Not(And(In(v, a), Not(q)))) と
    ExIn(v, a, p) = Not(All(v, Not(And(In(v, a), p)))) はどちらもこの形を含む。 -/
inductive IsD0 : Fml → Prop where
  | mem  (a b : Nat) : IsD0 (.mem a b)
  | eq   (a b : Nat) : IsD0 (.eq a b)
  | neg  {p : Fml} : IsD0 p → IsD0 (.neg p)
  | conj {p q : Fml} : IsD0 p → IsD0 q → IsD0 (.conj p q)
  | ball (v a : Nat) {p : Fml} : a ≠ v → IsD0 p → IsD0 (.all v (.neg (.conj (.mem v a) p)))

theorem upd_ne {α : Type} (e : Nat → α) {v n : Nat} (x : α) (h : n ≠ v) : upd e v x n = e n := by
  simp [upd, h]

theorem upd_eq {α : Type} (e : Nat → α) (v : Nat) (x : α) : upd e v x v = x := by
  simp [upd]

theorem upd_in {α : Type} (U : α → Prop) (e : Nat → α) (v : Nat) (x : α)
    (he : ∀ n, U (e n)) (hx : U x) : ∀ n, U (upd e v x n) := by
  intro n
  by_cases h : n = v
  · simp [upd, h, hx]
  · simp [upd, h, he n]

/-- 原理 A：推移的なクラス U の上で、Δ0 式は絶対的。割当ての値はすべて U に属するとする。 -/
theorem absolute {α : Type} (mem : α → α → Prop) (U : α → Prop)
    (trans : ∀ x y, U y → mem x y → U x) :
    ∀ {φ : Fml}, IsD0 φ → ∀ (e : Nat → α), (∀ n, U (e n)) →
      (evalU mem U φ e ↔ evalU mem (fun _ => True) φ e) := by
  intro φ hφ
  induction hφ with
  | mem a b => intro e _; exact Iff.rfl
  | eq a b => intro e _; exact Iff.rfl
  | neg _ ih =>
    intro e he
    simp only [evalU]
    exact not_congr (ih e he)
  | conj _ _ ihp ihq =>
    intro e he
    simp only [evalU]
    exact and_congr (ihp e he) (ihq e he)
  | ball v a hav _ ih =>
    intro e he
    simp only [evalU]
    have hea : ∀ x, upd e v x a = e a := fun x => upd_ne e x hav
    have hev : ∀ x, upd e v x v = x := fun x => upd_eq e v x
    constructor
    · intro hU x _ hcon
      have hm : mem x (e a) := by
        have := hcon.1; rw [hev x, hea x] at this; exact this
      have hxU : U x := trans x (e a) (he a) hm
      apply hU x hxU
      exact ⟨by rw [hev x, hea x]; exact hm, (ih (upd e v x) (upd_in U e v x he hxU)).mpr hcon.2⟩
    · intro hF x hxU hcon
      exact hF x trivial ⟨hcon.1, (ih (upd e v x) (upd_in U e v x he hxU)).mp hcon.2⟩


/-- 原理 B を式の形で表したもの（改訂36）：Δ0 の部分、有界量化、および
    「U の外の値では本体が（制限のない評価で）真になる」全称量化（空集合・後者の判定など）からなる式。 -/
inductive AbsF {α : Type} (mem : α → α → Prop) (U : α → Prop) : Fml → Prop where
  | d0   {φ : Fml} : IsD0 φ → AbsF mem U φ
  | neg  {p : Fml} : AbsF mem U p → AbsF mem U (.neg p)
  | conj {p q : Fml} : AbsF mem U p → AbsF mem U q → AbsF mem U (.conj p q)
  | ball (v a : Nat) {p : Fml} : a ≠ v → AbsF mem U p → AbsF mem U (.all v (.neg (.conj (.mem v a) p)))
  | outside (v : Nat) {p : Fml} : AbsF mem U p →
      (∀ (e : Nat → α) (x : α), (∀ n, U (e n)) → ¬ U x → evalU mem (fun _ => True) p (upd e v x)) →
      AbsF mem U (.all v p)

theorem absoluteF {α : Type} (mem : α → α → Prop) (U : α → Prop)
    (trans : ∀ x y, U y → mem x y → U x) :
    ∀ {φ : Fml}, AbsF mem U φ → ∀ (e : Nat → α), (∀ n, U (e n)) →
      (evalU mem U φ e ↔ evalU mem (fun _ => True) φ e) := by
  intro φ hφ
  induction hφ with
  | d0 h => intro e he; exact absolute mem U trans h e he
  | neg _ ih => intro e he; simp only [evalU]; exact not_congr (ih e he)
  | conj _ _ ihp ihq => intro e he; simp only [evalU]; exact and_congr (ihp e he) (ihq e he)
  | ball v a hav _ ih =>
    intro e he
    simp only [evalU]
    have hea : ∀ x, upd e v x a = e a := fun x => upd_ne e x hav
    have hev : ∀ x, upd e v x v = x := fun x => upd_eq e v x
    constructor
    · intro hU x _ hcon
      have hm : mem x (e a) := by
        have := hcon.1; rw [hev x, hea x] at this; exact this
      have hxU : U x := trans x (e a) (he a) hm
      exact hU x hxU ⟨by rw [hev x, hea x]; exact hm, (ih (upd e v x) (upd_in U e v x he hxU)).mpr hcon.2⟩
    · intro hF x hxU hcon
      exact hF x trivial ⟨hcon.1, (ih (upd e v x) (upd_in U e v x he hxU)).mp hcon.2⟩
  | outside v _ side ih =>
    intro e he
    simp only [evalU]
    constructor
    · intro hU x _
      cases Classical.em (U x) with
      | inl hxU => exact (ih (upd e v x) (upd_in U e v x he hxU)).mp (hU x hxU)
      | inr hxU => exact side e x he hxU
    · intro hF x hxU
      exact (ih (upd e v x) (upd_in U e v x he hxU)).mpr (hF x trivial)

/-- 原理 B (B1)：ガードつきの全称量化。ガード G を満たすものはすべて U に属し、
    U の元についてはガードと本体の真偽が U での評価と一致するなら、量化子の真偽は一致する。 -/
theorem guarded_all {α : Type} (U G GU χ χU : α → Prop)
    (hG : ∀ w, G w → U w) (hGU : ∀ w, U w → (GU w ↔ G w)) (hχ : ∀ w, U w → (χU w ↔ χ w)) :
    (∀ w, U w → (GU w → χU w)) ↔ (∀ w, G w → χ w) := by
  constructor
  · intro h w hg
    have hu := hG w hg
    exact (hχ w hu).mp (h w hu ((hGU w hu).mpr hg))
  · intro h w hu hgu
    exact (hχ w hu).mpr (h w ((hGU w hu).mp hgu))

/-- 原理 B (B2)：同値型の全称量化。両辺とも U の外では偽なら、量化子の真偽は一致する。 -/
theorem iff_all {α : Type} (U A AU B BU : α → Prop)
    (hA : ∀ w, A w → U w) (hB : ∀ w, B w → U w)
    (hAU : ∀ w, U w → (AU w ↔ A w)) (hBU : ∀ w, U w → (BU w ↔ B w)) :
    (∀ w, U w → (AU w ↔ BU w)) ↔ (∀ w, (A w ↔ B w)) := by
  constructor
  · intro h w
    constructor
    · intro ha
      have hu := hA w ha
      exact (hBU w hu).mp ((h w hu).mp ((hAU w hu).mpr ha))
    · intro hb
      have hu := hB w hb
      exact (hAU w hu).mp ((h w hu).mpr ((hBU w hu).mpr hb))
  · intro h w hu
    rw [hAU w hu, hBU w hu]
    exact h w

/-- 原理 B (B0) と原理 C の存在の部分：条件 P を満たすものがただ一つ w0 で、w0 が U に属するなら、
    存在量化の真偽は一致する。 -/
theorem pinned_ex {α : Type} (U P PU χ χU : α → Prop) (w0 : α)
    (huniq : ∀ w, P w → w = w0) (hP0 : P w0) (hU0 : U w0)
    (hPU : ∀ w, U w → (PU w ↔ P w)) (hχ : ∀ w, U w → (χU w ↔ χ w)) :
    (∃ w, U w ∧ PU w ∧ χU w) ↔ (∃ w, P w ∧ χ w) := by
  constructor
  · intro ⟨w, hu, hp, hc⟩
    exact ⟨w, (hPU w hu).mp hp, (hχ w hu).mp hc⟩
  · intro ⟨w, hp, hc⟩
    have hw := huniq w hp
    subst hw
    exact ⟨w, hU0, (hPU w hU0).mpr hp, (hχ w hU0).mpr hc⟩

/-- 原理 C（一意性）：整礎な関係 r の上で、各添字 i での条件 Ψ が
    「より小さい添字で一致する二つの表は i でも一致する」性質をもつなら、Ψ を満たす表は一意。 -/
theorem table_unique {I β : Type} {r : I → I → Prop} (wf : WellFounded r)
    (Ψ : (I → β) → I → Prop)
    (loc : ∀ (T T' : I → β) (i : I), (∀ j, r j i → T j = T' j) → Ψ T i → Ψ T' i → T i = T' i)
    (T T' : I → β) (hT : ∀ i, Ψ T i) (hT' : ∀ i, Ψ T' i) : T = T' := by
  funext i
  exact wf.induction i (fun i ih => loc T T' i ih (hT i) (hT' i))

#print axioms absolute
#print axioms absoluteF
#print axioms table_unique

end Moon
