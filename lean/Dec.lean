/-
  cnf.py の分解 dec（素数による）が G7 の仕様 DecSpec を満たすことの形式化（改訂40）。

  dec(i, a, b)：i ≠ 0 で、i+1 を割る最小の素数を p、p で割り切れる回数を v、(i+1)/p^v = j として、
               a = v − 1、b = j − 1（cnf.py の dec の書き写し。素数の定義は arith.py の prime と同じ：
               2 ≤ p で、2 ≤ d < p の d は p を割らない）。
  ・pyDec_uniq：(a, b) は一意。・pyDec_lt：a, b < i。・pyDec_ex：i > 0 なら存在する。
  ・pyDecSpec：以上をまとめた DecSpec。G7 の cnf_cmp_correct・name_lt_wf がこの分解についても成り立つ。
-/
import G7
namespace Dec

def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d < p → 2 ≤ d → ¬ d ∣ p

def pyDec (i a b : Nat) : Prop :=
  i ≠ 0 ∧ ∃ p, Prime p ∧ p ∣ i + 1 ∧ (∀ q, q < p → ¬ (Prime q ∧ q ∣ i + 1)) ∧
    ∃ j, i + 1 = p ^ (a + 1) * j ∧ j = b + 1 ∧ ¬ p ∣ j

theorem pow_cancel (p : Nat) (hp : 2 ≤ p) : ∀ m n j j', p ^ m * j = p ^ n * j' → ¬ p ∣ j → ¬ p ∣ j' →
    m = n ∧ j = j' := by
  intro m
  induction m with
  | zero =>
    intro n j j' h hj hj'
    cases n with
    | zero => simp at h; exact ⟨rfl, h⟩
    | succ n =>
      exfalso; apply hj
      simp at h
      exact ⟨p ^ n * j', by rw [h, Nat.pow_succ]; rw [Nat.mul_comm (p ^ n) p, Nat.mul_assoc]⟩
  | succ m ih =>
    intro n j j' h hj hj'
    cases n with
    | zero =>
      exfalso; apply hj'
      simp at h
      exact ⟨p ^ m * j, by rw [← h, Nat.pow_succ]; rw [Nat.mul_comm (p ^ m) p, Nat.mul_assoc]⟩
    | succ n =>
      have h' : p * (p ^ m * j) = p * (p ^ n * j') := by
        rw [Nat.pow_succ, Nat.pow_succ] at h
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm p (p ^ m), Nat.mul_comm p (p ^ n)]
        exact h
      have := ih n j j' (Nat.eq_of_mul_eq_mul_left (by omega) h') hj hj'
      exact ⟨by rw [this.1], this.2⟩

theorem pyDec_uniq : ∀ i a b a' b', pyDec i a b → pyDec i a' b' → a = a' ∧ b = b' := by
  intro i a b a' b' ⟨_, p, hp, hpd, hmin, j, hj, hjb, hpj⟩ ⟨_, p', hp', hpd', hmin', j', hj', hjb', hpj'⟩
  have epp : p = p' := by
    rcases Nat.lt_trichotomy p p' with h | h | h
    · exact absurd ⟨hp, hpd⟩ (hmin' p h)
    · exact h
    · exact absurd ⟨hp', hpd'⟩ (hmin p' h)
  subst epp
  have := pow_cancel p hp.1 (a + 1) (a' + 1) j j' (hj.symm.trans hj') hpj hpj'
  exact ⟨by omega, by omega⟩

theorem two_pow_ge (n : Nat) : n + 2 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.pow_succ]; omega

theorem pyDec_lt : ∀ i a b, pyDec i a b → a < i ∧ b < i := by
  intro i a b ⟨hi, p, hp, _, _, j, hj, hjb, _⟩
  have h2 : 2 ^ (a + 1) ≤ p ^ (a + 1) := Nat.pow_le_pow_left hp.1 _
  have hge := two_pow_ge a
  have hj1 : 1 ≤ j := by omega
  have hpj : p ^ (a + 1) ≤ i + 1 := by
    rw [hj]; exact Nat.le_mul_of_pos_right _ hj1
  have hp2 : 2 * j ≤ i + 1 := by
    rw [hj]
    have : 2 ≤ p ^ (a + 1) := by omega
    exact Nat.mul_le_mul_right j this
  constructor <;> omega

/-- 性質 P をもつ自然数があれば、最小のものがある。 -/
theorem exists_least (P : Nat → Prop) (n : Nat) (hn : P n) : ∃ m, P m ∧ ∀ k, k < m → ¬ P k := by
  refine Classical.byContradiction (fun hno => ?_)
  have : ∀ m, ¬ P m := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih => intro hm; exact hno ⟨m, hm, fun k hk hP => ih k hk hP⟩
  exact this n hn

theorem factor (p : Nat) (hp : 2 ≤ p) : ∀ m, 0 < m → ∃ v j, m = p ^ v * j ∧ ¬ p ∣ j := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro hm
  by_cases h : p ∣ m
  · obtain ⟨m', hm'⟩ := h
    have pos : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with e | e
      · subst e; simp at hm'; omega
      · exact e
    have lt : m' < m := by
      rw [hm']
      have : 1 * m' < p * m' := Nat.mul_lt_mul_of_pos_right (by omega) pos
      omega
    obtain ⟨v, j, e, hj⟩ := ih m' lt pos
    refine ⟨v + 1, j, ?_, hj⟩
    rw [hm', e, Nat.pow_succ, Nat.mul_comm (p ^ v) p, Nat.mul_assoc]
  · exact ⟨0, m, by simp, h⟩

theorem pyDec_ex : ∀ i, 0 < i → ∃ a b, pyDec i a b := by
  intro i hi
  -- i+1 を割る 2 以上の最小の数 p は素数
  obtain ⟨p, ⟨hp2, hpd⟩, hmin⟩ := exists_least (fun d => 2 ≤ d ∧ d ∣ i + 1) (i + 1) ⟨by omega, Nat.dvd_refl _⟩
  have hprime : Prime p := by
    refine ⟨hp2, fun d hd hd2 hdp => hmin d hd ⟨hd2, Nat.dvd_trans hdp hpd⟩⟩
  have hleast : ∀ q, q < p → ¬ (Prime q ∧ q ∣ i + 1) := fun q hq ⟨hq2, hqd⟩ => hmin q hq ⟨hq2.1, hqd⟩
  obtain ⟨v, j, e, hj⟩ := factor p hp2 (i + 1) (by omega)
  have hv : v ≠ 0 := by
    intro h; subst h; simp at e; rw [← e] at hj; exact hj hpd
  have hj0 : j ≠ 0 := by intro h; subst h; simp at e
  refine ⟨v - 1, j - 1, by omega, p, hprime, hpd, hleast, j, ?_, by omega, hj⟩
  have : v - 1 + 1 = v := by omega
  rw [this]; exact e

def pyDecSpec : G7.DecSpec where
  D := pyDec
  uniq := pyDec_uniq
  lt := pyDec_lt
  ex := pyDec_ex

/-- cnf.py の分解についての最終形。 -/
theorem cnf_cmp_correct_py (i k c : Nat) :
    (∃ HR CM, G7.tableOk pyDecSpec HR CM ∧ CM i k c) ↔
      c = G7.code (G7.ON.cmp (G7.norm pyDecSpec i) (G7.norm pyDecSpec k)) :=
  G7.cnf_cmp_correct pyDecSpec i k c

theorem name_lt_wf_py : WellFounded (fun k i => G7.ON.cmp (G7.norm pyDecSpec k) (G7.norm pyDecSpec i) = .lt) :=
  G7.name_lt_wf pyDecSpec

#print axioms cnf_cmp_correct_py
#print axioms name_lt_wf_py

end Dec
