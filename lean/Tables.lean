/-
  別紙 G の補題 G2（ハイパー演算の表）と G16（有限和と反復の表）の形式化（改訂39）。

  ・H：ハイパー演算 H(0,a,b) = b+1、H(1,a,0) = a、H(2,a,0) = 0、H(n,a,0) = 1 (n ≥ 3)、
       H(n+1,a,b+1) = H(n,a,H(n+1,a,b))（arith.py と同じ定義）。
  ・hyperOk：arith.py の hyper_table の条件の書き写し（表のどの行も、初期値か、表の中の別の行を使った再帰で正当化される）。
  ・hyper_correct：「条件を満たす表に行 (n, b, v) がある」⟺ v = H(n, a, b)。
  ・H_one・H_two・H_three：H(1) は加法、H(2) は乗法、H(3) は冪（arith.py の add・mul・exp はこれを使う）。
  ・sum_correct・sum_indep：有限和の表 R の値は Σ_{k<K, k∈S} k で、S ⊆ K なら K の取り方によらない。
  ・iter_correct：反復の表 G の値は f の t 回の反復。
-/
namespace Tables

def H (a : Nat) : Nat → Nat → Nat
  | 0, b => b + 1
  | 1, 0 => a
  | 2, 0 => 0
  | _ + 3, 0 => 1
  | n + 1, b + 1 => H a n (H a (n + 1) b)
termination_by n b => (n, b)

/-- arith.py の hyper_table：行 (n, b, v) はすべて規則のどれかで正当化される。 -/
def hyperOk (a : Nat) (T : Nat → Nat → Nat → Prop) : Prop :=
  ∀ n b v, T n b v →
    (n = 0 ∧ v = b + 1) ∨
    (∃ n1, n = n1 + 1 ∧ b = 0 ∧ ((n1 = 0 ∧ v = a) ∨ (n1 = 1 ∧ v = 0) ∨ (n1 ≠ 0 ∧ n1 ≠ 1 ∧ v = 1))) ∨
    (∃ n1 b1, n = n1 + 1 ∧ b = b1 + 1 ∧ ∃ w, T n b1 w ∧ T n1 w v)

theorem hyper_sound (a : Nat) (T : Nat → Nat → Nat → Prop) (hT : hyperOk a T) :
    ∀ n b v, T n b v → v = H a n b := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro b
  induction b with
  | zero =>
    intro v hv
    rcases hT n 0 v hv with ⟨hn, hv'⟩ | ⟨n1, hn, _, h⟩ | ⟨n1, b1, _, hb, _⟩
    · subst hn; simp [H, hv']
    · subst hn
      rcases h with ⟨h1, hv'⟩ | ⟨h1, hv'⟩ | ⟨h1, h2, hv'⟩
      · subst h1; simp [H, hv']
      · subst h1; simp [H, hv']
      · match n1, h1, h2 with
        | k + 2, _, _ => simp [H, hv']
    · omega
  | succ b ihb =>
    intro v hv
    rcases hT n (b + 1) v hv with ⟨hn, hv'⟩ | ⟨n1, _, hb, _⟩ | ⟨n1, b1, hn, hb, w, hw1, hw2⟩
    · subst hn; simp [H, hv']
    · omega
    · have e : b1 = b := by omega
      subst e; subst hn
      have ew := ihb w hw1
      have ev := ihn n1 (by omega) w v hw2
      rw [ev, ew]; simp [H]

theorem hyper_correct (a n b v : Nat) :
    (∃ T, hyperOk a T ∧ T n b v) ↔ v = H a n b := by
  constructor
  · intro ⟨T, hT, hv⟩; exact hyper_sound a T hT n b v hv
  · intro hv
    refine ⟨fun n b v => v = H a n b, ?_, hv⟩
    intro n b v hv
    match n, b with
    | 0, b => exact Or.inl ⟨rfl, by simp [hv, H]⟩
    | 1, 0 => exact Or.inr (Or.inl ⟨0, rfl, rfl, Or.inl ⟨rfl, by simp [hv, H]⟩⟩)
    | 2, 0 => exact Or.inr (Or.inl ⟨1, rfl, rfl, Or.inr (Or.inl ⟨rfl, by simp [hv, H]⟩)⟩)
    | k + 3, 0 => exact Or.inr (Or.inl ⟨k + 2, rfl, rfl, Or.inr (Or.inr ⟨by omega, by omega, by simp [hv, H]⟩)⟩)
    | n + 1, b + 1 => exact Or.inr (Or.inr ⟨n, b, rfl, rfl, H a (n + 1) b, rfl, by simp [hv, H]⟩)

theorem H_one (a : Nat) : ∀ b, H a 1 b = a + b
  | 0 => by simp [H]
  | b + 1 => by simp [H, H_one a b]; omega

theorem H_two (a : Nat) : ∀ b, H a 2 b = a * b
  | 0 => by simp [H]
  | b + 1 => by simp [H, H_two a b, H_one]; rw [Nat.mul_succ]; omega

theorem H_three (a : Nat) : ∀ b, H a 3 b = a ^ b
  | 0 => by simp [H]
  | b + 1 => by simp [H, H_three a b, H_two, Nat.pow_succ]; exact Nat.mul_comm _ _

-- ---------- 有限和 ----------
def sumBelow (S : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => sumBelow S k + (if S k then k else 0)

/-- ffunc.py の finite_sum：R(0) = 0、k < K について R(k+1) = R(k) + (k ∈ S なら k)。 -/
theorem sum_correct (S : Nat → Bool) (K : Nat) (R : Nat → Nat)
    (h0 : R 0 = 0) (hs : ∀ k, k < K → R (k + 1) = R k + (if S k then k else 0)) :
    R K = sumBelow S K := by
  suffices H : ∀ k, k ≤ K → R k = sumBelow S k from H K (Nat.le_refl K)
  intro k
  induction k with
  | zero => intro _; simp [h0, sumBelow]
  | succ k ih => intro hk; rw [hs k (by omega), ih (by omega)]; simp [sumBelow]

/-- S ⊆ K なら、和は K の取り方によらない。 -/
theorem sum_indep (S : Nat → Bool) (K : Nat) (hK : ∀ k, S k = true → k < K) :
    ∀ K', K ≤ K' → sumBelow S K' = sumBelow S K := by
  intro K' hK'
  induction K' with
  | zero => have : K = 0 := by omega
            subst this; rfl
  | succ k ih =>
    by_cases e : K = k + 1
    · subst e; rfl
    · have hk : K ≤ k := by omega
      have hS : S k = false := by
        cases h : S k with
        | false => rfl
        | true => have := hK k h; omega
      simp [sumBelow, hS, ih hk]

-- ---------- 反復 ----------
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, a => a
  | t + 1, a => f (iter f t a)

/-- ffunc.py の iterate10：G(0) = a、j < t について G(j+1) = f(G(j)) なら、G(t) = f^t(a)。 -/
theorem iter_correct (f : Nat → Nat) (t a : Nat) (G : Nat → Nat)
    (h0 : G 0 = a) (hs : ∀ j, j < t → G (j + 1) = f (G j)) : G t = iter f t a := by
  suffices H : ∀ j, j ≤ t → G j = iter f j a from H t (Nat.le_refl t)
  intro j
  induction j with
  | zero => intro _; simp [h0, iter]
  | succ j ih => intro hj; rw [hs j (by omega), ih (by omega)]; rfl

#print axioms hyper_correct
#print axioms H_three
#print axioms sum_indep
#print axioms iter_correct

-- ---------- クヌースの矢印との対応 ----------
/-- a ↑^k b（k ≥ 1）。up a 1 b = a^b、up a (k+1) 0 = 1、up a (k+1) (b+1) = up a k (up a (k+1) b)。 -/
def up (a : Nat) : Nat → Nat → Nat
  | 0, b => a * b
  | 1, b => a ^ b
  | k + 2, 0 => 1
  | k + 2, b + 1 => up a (k + 1) (up a (k + 2) b)
termination_by k b => (k, b)

theorem H_up (a : Nat) : ∀ k b, H a (k + 3) b = up a (k + 1) b := by
  intro k
  induction k with
  | zero => intro b; rw [H_three]; simp [up]
  | succ k ih =>
    intro b
    induction b with
    | zero => simp [H, up]
    | succ b ihb => simp only [H]; rw [ihb, ih]; simp [up]

/-- 本文の数詞 A：10↑^10 10 = H(12, 10, 10)。 -/
theorem numeral_A : H 10 12 10 = up 10 10 10 := H_up 10 9 10

#print axioms numeral_A

end Tables
