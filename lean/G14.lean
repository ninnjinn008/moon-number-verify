/-
  別紙 G の補題 G14（Θ の規則と Henkin 公理）の形式化（改訂38）。G5.lean の構文と意味論の上に載せる。

  ・自由変数 Form.fv と一致の補題 sat_congr：自由変数で一致する割当ての下では真偽が一致する。
  ・Θ の規則：Z = { σ : P が σ で真 }、dep_only i、good a、整列順序 W での最小の good な元。
    （生成プログラムでは i は P に現れる変数の添字 Ns を動く。ここでは任意の添字の集合 Ns で示す。）
  ・good_exists：good な元は必ずある。
  ・henkin：P の自由変数が高々 x_i だけなら、P を満たす x_i があるとき、x_i := Θ でも P は真（読み 1 の Henkin 公理）。
-/
import G5
namespace G5

mutual
def Term.fv : Term → Nat → Prop
  | .var i, k => k = i
  | .cst _, _ => False
  | .app _ _ ts, k => Terms.fv ts k
def Terms.fv : Terms → Nat → Prop
  | .nil, _ => False
  | .cons t ts, k => Term.fv t k ∨ Terms.fv ts k
end

def Form.fv : Form → Nat → Prop
  | .bot, _ => False
  | .elem t u, k => t.fv k ∨ u.fv k
  | .rel _ _ ts, k => ts.fv k
  | .imp p q, k => p.fv k ∨ q.fv k
  | .neg p, k => p.fv k
  | .ex j p, k => k ≠ j ∧ p.fv k

section
variable {α : Type} (M : Model α)

mutual
theorem term_congr : ∀ (t : Term) (σ σ' : Nat → α), (∀ k, t.fv k → σ k = σ' k) → t.eval M σ = t.eval M σ'
  | .var i, σ, σ', h => by simp only [Term.eval]; exact h i rfl
  | .cst _, _, _, _ => rfl
  | .app f a ts, σ, σ', h => by
    simp only [Term.eval]
    rw [terms_congr ts σ σ' (fun k hk => h k hk)]
theorem terms_congr : ∀ (ts : Terms) (σ σ' : Nat → α), (∀ k, ts.fv k → σ k = σ' k) → ts.eval M σ = ts.eval M σ'
  | .nil, _, _, _ => rfl
  | .cons t ts, σ, σ', h => by
    simp only [Terms.eval]
    rw [term_congr t σ σ' (fun k hk => h k (Or.inl hk)), terms_congr ts σ σ' (fun k hk => h k (Or.inr hk))]
end

theorem sat_congr : ∀ (φ : Form) (σ σ' : Nat → α), (∀ k, φ.fv k → σ k = σ' k) → (φ.sat M σ ↔ φ.sat M σ') := by
  intro φ
  induction φ with
  | bot => intro _ _ _; exact Iff.rfl
  | elem t u =>
    intro σ σ' h; simp only [Form.sat]
    rw [term_congr M t σ σ' (fun k hk => h k (Or.inl hk)), term_congr M u σ σ' (fun k hk => h k (Or.inr hk))]
  | rel r a ts =>
    intro σ σ' h; simp only [Form.sat]
    rw [terms_congr M ts σ σ' h]
  | imp p q ihp ihq =>
    intro σ σ' h; simp only [Form.sat]
    rw [ihp σ σ' (fun k hk => h k (Or.inl hk)), ihq σ σ' (fun k hk => h k (Or.inr hk))]
  | neg p ih =>
    intro σ σ' h; simp only [Form.sat]
    rw [ih σ σ' h]
  | ex j p ih =>
    intro σ σ' h; simp only [Form.sat]
    constructor
    · intro ⟨x, hx⟩
      refine ⟨x, (ih _ _ ?_).mp hx⟩
      intro k hk; simp only [upd]
      by_cases e : k = j
      · simp [e]
      · simp [e]; exact h k ⟨e, hk⟩
    · intro ⟨x, hx⟩
      refine ⟨x, (ih _ _ ?_).mpr hx⟩
      intro k hk; simp only [upd]
      by_cases e : k = j
      · simp [e]
      · simp [e]; exact h k ⟨e, hk⟩

-- ---------- Θ の規則 ----------
variable (P : Form) (Ns : Nat → Prop)

def Zs (σ : Nat → α) : Prop := P.sat M σ
def depOnly (i : Nat) : Prop := ∀ σ σ' : Nat → α, σ i = σ' i → (Zs M P σ ↔ Zs M P σ')
def good (a : α) : Prop := ∀ i, Ns i → depOnly M P i → (∃ σ, Zs M P σ) → ∀ σ, Zs M P (upd σ i a)

theorem upd_same (σ : Nat → α) (i : Nat) (a : α) : upd σ i a i = a := by simp [upd]
theorem upd_other (σ : Nat → α) {i k : Nat} (a : α) (h : k ≠ i) : upd σ i a k = σ k := by simp [upd, h]

/-- 二つの添字のどちらか一方だけで真偽が決まるなら、真偽はどの割当てでも同じ。 -/
theorem two_dep_const {i j : Nat} (hij : i ≠ j) (hi : depOnly M P i) (hj : depOnly M P j)
    (σ σ' : Nat → α) : Zs M P σ ↔ Zs M P σ' := by
  let τ : Nat → α := upd σ' i (σ i)
  have h1 : Zs M P σ ↔ Zs M P τ := hi σ τ (by simp [τ, upd_same])
  have h2 : Zs M P τ ↔ Zs M P σ' := hj τ σ' (by simp [τ, upd_other σ' (σ i) (Ne.symm hij)])
  exact h1.trans h2

/-- good な元は必ずある（領域が空でなければ）。 -/
theorem good_exists (a0 : α) : ∃ a, good M P Ns a := by
  by_cases hz : ∃ i, Ns i ∧ depOnly M P i ∧ ∃ σ, Zs M P σ
  · obtain ⟨i, _, hi, σ0, hσ0⟩ := hz
    refine ⟨σ0 i, ?_⟩
    intro j _ hj _ σ
    by_cases e : j = i
    · subst e
      exact (hi σ0 (upd σ j (σ0 j)) (by simp [upd_same])).mp hσ0
    · exact (two_dep_const M P (Ne.symm e) hi hj σ0 (upd σ j (σ0 i))).mp hσ0
  · refine ⟨a0, ?_⟩
    intro i hi hd hex
    exact absurd ⟨i, hi, hd, hex⟩ hz

/-- 読み 1 の Henkin 公理：P の自由変数が高々 x_i だけで、a が good なら、
    P を満たす x_i があるとき x_i := a でも P は真（全称閉包の読み）。 -/
theorem henkin {i : Nat} (hfv : ∀ k, P.fv k → k = i) (a : α) (ha : good M P Ns a) (hNs : Ns i ∨ ¬ P.fv i)
    (σ : Nat → α) (hex : ∃ x, P.sat M (upd σ i x)) : P.sat M (upd σ i a) := by
  obtain ⟨x, hx⟩ := hex
  -- P の真偽は x_i の値だけで決まる
  have hdep : depOnly M P i := by
    intro τ τ' e
    exact sat_congr M P τ τ' (fun k hk => by rw [hfv k hk]; exact e)
  rcases hNs with hN | hnf
  · exact ha i hN hdep ⟨_, hx⟩ σ
  · -- x_i が自由でなければ、P の真偽は割当てによらない
    exact (sat_congr M P _ _ (fun k hk => absurd (hfv k hk ▸ hk) hnf)).mp hx

end

-- ---------- 整列順序での最小の good な元 ----------
/-- 整礎な関係 W の下で、性質 Q をもつ元があれば、W について極小な Q の元がある。 -/
theorem exists_min {α : Type} (W : α → α → Prop) (wf : WellFounded W) (Q : α → Prop) (a : α) (ha : Q a) :
    ∃ m, Q m ∧ ∀ b, W b m → ¬ Q b := by
  refine Classical.byContradiction (fun hno => ?_)
  have : ∀ x, ¬ Q x := by
    intro x
    induction x using wf.induction with
    | _ x ih =>
      intro hx
      exact hno ⟨x, hx, fun b hb hQ => ih b hb hQ⟩
  exact this a ha

/-- Θ の値（W で最小の good な元）が存在し、Henkin 公理を満たす。 -/
theorem theta_henkin {α : Type} (M : Model α) (P : Form) (Ns : Nat → Prop) (W : α → α → Prop)
    (wf : WellFounded W) (a0 : α) :
    ∃ θ, good M P Ns θ ∧ (∀ b, W b θ → ¬ good M P Ns b) ∧
      ∀ i, (∀ k, P.fv k → k = i) → (Ns i ∨ ¬ P.fv i) →
        ∀ σ, (∃ x, P.sat M (upd σ i x)) → P.sat M (upd σ i θ) := by
  obtain ⟨a, ha⟩ := good_exists M P Ns a0
  obtain ⟨θ, hθ, hmin⟩ := exists_min W wf (good M P Ns) a ha
  exact ⟨θ, hθ, hmin, fun i hfv hNs σ hex => henkin M P Ns hfv θ hθ hNs σ hex⟩

#print axioms theta_henkin

end G5
