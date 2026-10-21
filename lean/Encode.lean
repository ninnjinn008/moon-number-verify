/-
  補題 G3 の数論の部分（改訂41）：素数の表・積の表・Encode・MetaCode の正しさと、Encode の単射性。

  ・素数の判定 Prime は Dec.lean のもの（arith.py の prime の書き写し）。
  ・NP i p：p は i 番目の素数（0 番目は 2）。ptOk：arith.py の prime_table の行の条件。
    nth_correct：(∃ T, ptOk T ∧ T i p) ⟺ NP i p。NP は関数的で全域（素数は無限にある）。
  ・prodF k s = ∏_{i<k} p_{i+1}^{s(i)}。prodOk：prod_table の行の条件。prod_sound・prod_true。
  ・enc h s = 2^h · prodF h s − 1（原文の Encode）。encode_correct：encode の式が述べる内容。
  ・enc_inj：Encode は単射（列の長さと、長さ未満の各成分が一致する）。
  ・metacode_correct・metacode_inj：MetaCode = Encode(Encode(s(0)), …) の正しさと単射性。
  乗算と冪は Tables.lean（補題 G2）で H(2)・H(3) と一致することを示してあるので、ここでは Lean の * と ^ を使う。
-/
import Dec
namespace Enc
open Dec

/-! ### 素数についての基本事実（Mathlib なし） -/

theorem prime_two : Prime 2 := ⟨by decide, fun d hd h2 => by omega⟩

theorem prime_pos {q : Nat} (h : Prime q) : 0 < q := by have := h.1; omega

theorem dvd_prime {q d : Nat} (hq : Prime q) (hd : d ∣ q) : d = 1 ∨ d = q := by
  have hle : d ≤ q := Nat.le_of_dvd (prime_pos hq) hd
  rcases Nat.lt_or_eq_of_le hle with h | h
  · by_cases h2 : 2 ≤ d
    · exact absurd hd (hq.2 d h h2)
    · rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0; have := Nat.eq_zero_of_zero_dvd hd; have := hq.1; omega
      · left; omega
  · right; exact h

theorem prime_dvd_prime {q r : Nat} (hq : Prime q) (hr : Prime r) (h : q ∣ r) : q = r := by
  rcases dvd_prime hr h with h1 | h1
  · have := hq.1; omega
  · exact h1

/-- Euclid の補題。 -/
theorem euclid {q a b : Nat} (hq : Prime q) (h : q ∣ a * b) : q ∣ a ∨ q ∣ b := by
  by_cases ha : q ∣ a
  · exact Or.inl ha
  · right
    have hg : Nat.gcd q a = 1 := by
      rcases dvd_prime hq (Nat.gcd_dvd_left q a) with g | g
      · exact g
      · exact absurd (g ▸ Nat.gcd_dvd_right q a) ha
    have h2 : q ∣ Nat.gcd (q * b) (a * b) := Nat.dvd_gcd (Nat.dvd_mul_right q b) h
    rw [Nat.gcd_mul_right, hg, Nat.one_mul] at h2
    exact h2

theorem prime_dvd_pow {q r : Nat} (hq : Prime q) : ∀ e, q ∣ r ^ e → q ∣ r := by
  intro e
  induction e with
  | zero => intro h; simp at h; have := hq.1; omega
  | succ e ih =>
    intro h
    rw [Nat.pow_succ] at h
    rcases euclid hq h with h | h
    · exact ih h
    · exact h

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (by omega) (fact_pos n)

theorem dvd_fact : ∀ n d, 1 ≤ d → d ≤ n → d ∣ fact n := by
  intro n
  induction n with
  | zero => intro d h1 h2; omega
  | succ n ih =>
    intro d h1 h2
    show d ∣ (n + 1) * fact n
    rcases Nat.lt_or_eq_of_le h2 with h | h
    · exact Nat.dvd_trans (ih d h1 (by omega)) (Nat.dvd_mul_left _ _)
    · rw [h]; exact Nat.dvd_mul_right _ _

/-- 素数は無限にある。 -/
theorem exists_prime_gt (n : Nat) : ∃ p, Prime p ∧ n < p := by
  obtain ⟨d, ⟨hd2, hdd⟩, hmin⟩ :=
    exists_least (fun d => 2 ≤ d ∧ d ∣ fact n + 1) (fact n + 1) ⟨by have := fact_pos n; omega, Nat.dvd_refl _⟩
  refine ⟨d, ⟨hd2, fun e he he2 hed => hmin e he ⟨he2, Nat.dvd_trans hed hdd⟩⟩, ?_⟩
  refine Classical.byContradiction (fun hle => ?_)
  have h1 : d ∣ fact n := dvd_fact n d (by omega) (by omega)
  obtain ⟨a, ha⟩ := hdd
  obtain ⟨b, hb⟩ := h1
  have hab : b < a := by
    refine Classical.byContradiction (fun hn => ?_)
    have := Nat.mul_le_mul_left d (show a ≤ b by omega)
    omega
  have := Nat.mul_le_mul_left d (show b + 1 ≤ a from hab)
  rw [Nat.mul_succ] at this
  omega

/-! ### i 番目の素数 -/

inductive NP : Nat → Nat → Prop where
  | zero : NP 0 2
  | succ {i p2 p : Nat} : NP i p2 → p2 < p → Prime p → (∀ m, m < p → p2 < m → ¬ Prime m) → NP (i + 1) p

theorem NP_prime : ∀ {i p}, NP i p → Prime p
  | _, _, .zero => prime_two
  | _, _, .succ _ _ hp _ => hp

theorem NP_unique : ∀ i p p', NP i p → NP i p' → p = p' := by
  intro i
  induction i with
  | zero => intro p p' h h'; cases h; cases h'; rfl
  | succ i ih =>
    intro p p' h h'
    cases h with
    | succ h1 hlt hp hgap =>
    cases h' with
    | succ h1' hlt' hp' hgap' =>
    have e := ih _ _ h1 h1'
    subst e
    rcases Nat.lt_trichotomy p p' with c | c | c
    · exact absurd hp (hgap' p c hlt)
    · exact c
    · exact absurd hp' (hgap p' c hlt')

theorem NP_total : ∀ i, ∃ p, NP i p := by
  intro i
  induction i with
  | zero => exact ⟨2, .zero⟩
  | succ i ih =>
    obtain ⟨p2, h2⟩ := ih
    obtain ⟨q, hq, hlt⟩ := exists_prime_gt p2
    obtain ⟨p, ⟨hp, hpl⟩, hmin⟩ := exists_least (fun m => Prime m ∧ p2 < m) q ⟨hq, hlt⟩
    exact ⟨p, .succ h2 hpl hp (fun m hm hm2 hpm => hmin m hm ⟨hpm, hm2⟩)⟩

theorem NP_lt : ∀ j i p q, NP i p → NP j q → i < j → p < q := by
  intro j
  induction j with
  | zero => intro i p q _ _ h; omega
  | succ j ih =>
    intro i p q hp hq hij
    cases hq with
    | succ h2 hlt _ _ =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hij) with c | c
    · exact Nat.lt_trans (ih i p _ hp h2 c) hlt
    · subst c; rw [NP_unique _ _ _ hp h2]; exact hlt

noncomputable def np (i : Nat) : Nat := Classical.choose (NP_total i)
theorem np_spec (i : Nat) : NP i (np i) := Classical.choose_spec (NP_total i)
theorem NP_iff (i p : Nat) : NP i p ↔ p = np i :=
  ⟨fun h => NP_unique _ _ _ h (np_spec i), fun h => h ▸ np_spec i⟩
theorem np_prime (i : Nat) : Prime (np i) := NP_prime (np_spec i)
theorem np_zero : np 0 = 2 := ((NP_iff 0 2).mp .zero).symm
theorem np_lt {i j : Nat} (h : i < j) : np i < np j := NP_lt j i _ _ (np_spec i) (np_spec j) h

/-! ### 素数の表（arith.py の prime_table と nth_prime） -/

def ptOk (T : Nat → Nat → Prop) : Prop :=
  ∀ i p, T i p → (i = 0 ∧ p = 2) ∨
    ∃ i1, i = i1 + 1 ∧ ∃ p2, T i1 p2 ∧ p2 < p ∧ Prime p ∧ ∀ m, m < p → p2 < m → ¬ Prime m

theorem pt_sound (T : Nat → Nat → Prop) (hT : ptOk T) : ∀ i p, T i p → NP i p := by
  intro i
  induction i with
  | zero =>
    intro p h
    rcases hT 0 p h with ⟨_, e⟩ | ⟨i1, e, _⟩
    · subst e; exact .zero
    · omega
  | succ i ih =>
    intro p h
    rcases hT _ p h with ⟨e, _⟩ | ⟨i1, e, p2, h2, hlt, hp, hgap⟩
    · omega
    · have : i1 = i := by omega
      subst this
      exact .succ (ih p2 h2) hlt hp hgap

theorem pt_true : ptOk NP := by
  intro i p h
  cases h with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ h2 hlt hp hgap => exact Or.inr ⟨_, rfl, _, h2, hlt, hp, hgap⟩

/-- nth_prime(i, p) の述べる内容。 -/
def nthR (i p : Nat) : Prop := ∃ T, ptOk T ∧ T i p

theorem nth_correct (i p : Nat) : nthR i p ↔ p = np i := by
  rw [← NP_iff]
  exact ⟨fun ⟨T, hT, h⟩ => pt_sound T hT i p h, fun h => ⟨NP, pt_true, h⟩⟩

/-! ### 積の表と Encode -/

noncomputable def prodF (s : Nat → Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => prodF s k * np (k + 1) ^ s k

def prodOk (h : Nat) (s : Nat → Nat) (T : Nat → Nat → Prop) : Prop :=
  ∀ k P, T k P → (k = 0 ∧ P = 1) ∨
    ∃ k1, k = k1 + 1 ∧ k1 < h ∧ ∃ P1, T k1 P1 ∧ ∃ pr, nthR k pr ∧ P = P1 * pr ^ s k1

theorem prod_sound (h : Nat) (s : Nat → Nat) (T : Nat → Nat → Prop) (hT : prodOk h s T) :
    ∀ k P, T k P → P = prodF s k := by
  intro k
  induction k with
  | zero =>
    intro P hP
    rcases hT 0 P hP with ⟨_, e⟩ | ⟨k1, e, _⟩
    · exact e
    · omega
  | succ k ih =>
    intro P hP
    rcases hT _ P hP with ⟨e, _⟩ | ⟨k1, e, _, P1, h1, pr, hpr, eP⟩
    · omega
    · have : k1 = k := by omega
      subst this
      rw [e] at hpr
      rw [eP, ih P1 h1, (nth_correct _ _).mp hpr]
      rfl

theorem prod_true (h : Nat) (s : Nat → Nat) : prodOk h s (fun k P => k ≤ h ∧ P = prodF s k) := by
  intro k P ⟨hk, hP⟩
  cases k with
  | zero => exact Or.inl ⟨rfl, hP⟩
  | succ k =>
    exact Or.inr ⟨k, rfl, by omega, prodF s k, ⟨by omega, rfl⟩, np (k + 1),
      (nth_correct _ _).mpr rfl, hP⟩

theorem prodF_congr (s s' : Nat → Nat) : ∀ k, (∀ i, i < k → s i = s' i) → prodF s k = prodF s' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    show prodF s k * np (k + 1) ^ s k = prodF s' k * np (k + 1) ^ s' k
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

/-- np j が np 1, …, np k のどれとも異なれば、np j は prodF s k を割らない。 -/
theorem not_dvd_prod (s : Nat → Nat) (j : Nat) : ∀ k, (∀ i, i < k → np (i + 1) ≠ np j) → ¬ np j ∣ prodF s k := by
  intro k
  induction k with
  | zero =>
    intro _ h
    have := Nat.le_of_dvd (by decide) (show np j ∣ 1 from h)
    have := (np_prime j).1
    omega
  | succ k ih =>
    intro hne h
    rcases euclid (np_prime j) h with h | h
    · exact ih (fun i hi => hne i (by omega)) h
    · have := prime_dvd_prime (np_prime j) (np_prime (k + 1)) (prime_dvd_pow (np_prime j) _ h)
      exact hne k (by omega) this.symm

theorem two_not_dvd_prod (s : Nat → Nat) (k : Nat) : ¬ 2 ∣ prodF s k := by
  have := not_dvd_prod s 0 k (fun i _ e => by have := @np_lt 0 (i + 1) (by omega); omega)
  rw [np_zero] at this
  exact this

theorem prod_pos (s : Nat → Nat) (k : Nat) : 0 < prodF s k := by
  rcases Nat.eq_zero_or_pos (prodF s k) with e | e
  · exact absurd (e ▸ Nat.dvd_zero 2) (two_not_dvd_prod s k)
  · exact e

theorem prodF_inj (s s' : Nat → Nat) : ∀ k, prodF s k = prodF s' k → ∀ i, i < k → s i = s' i := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro h i hi
    have h' : np (k + 1) ^ s k * prodF s k = np (k + 1) ^ s' k * prodF s' k := by
      rw [Nat.mul_comm, Nat.mul_comm (np (k + 1) ^ s' k)]; exact h
    have hn : ∀ t : Nat → Nat, ¬ np (k + 1) ∣ prodF t k :=
      fun t => not_dvd_prod t (k + 1) k (fun i hi e => by have := @np_lt (i + 1) (k + 1) (by omega); omega)
    have := pow_cancel (np (k + 1)) (np_prime _).1 _ _ _ _ h' (hn s) (hn s')
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with c | c
    · exact ih this.2 i c
    · subst c; exact this.1

theorem enc_congr' (s s' : Nat → Nat) (h : Nat) (hs : ∀ i, i < h → s i = s' i) :
    2 ^ h * prodF s h - 1 = 2 ^ h * prodF s' h - 1 := by
  rw [prodF_congr s s' h hs]

/-- 原文の Encode：列 s（長さ h）の番号 −1 + 2^h ∏_{i<h} p_{i+1}^{s(i)}。 -/
noncomputable def enc (h : Nat) (s : Nat → Nat) : Nat := 2 ^ h * prodF s h - 1

theorem enc_succ (h : Nat) (s : Nat → Nat) : enc h s + 1 = 2 ^ h * prodF s h := by
  have : 0 < 2 ^ h * prodF s h := Nat.mul_pos (Nat.pos_pow_of_pos h (by decide)) (prod_pos s h)
  unfold enc; omega

/-- encode(s, c) の述べる内容（s は長さ h の列）。 -/
def encR (h : Nat) (s : Nat → Nat) (c : Nat) : Prop :=
  ∃ T, prodOk h s T ∧ ∃ P, T h P ∧ c + 1 = 2 ^ h * P

theorem encode_correct (h : Nat) (s : Nat → Nat) (c : Nat) : encR h s c ↔ c = enc h s := by
  constructor
  · intro ⟨T, hT, P, hP, e⟩
    rw [prod_sound h s T hT h P hP] at e
    have := enc_succ h s
    omega
  · intro e
    exact ⟨_, prod_true h s, prodF s h, ⟨Nat.le_refl _, rfl⟩, by rw [e]; exact enc_succ h s⟩

/-- Encode は単射。 -/
theorem enc_inj (h h' : Nat) (s s' : Nat → Nat) (e : enc h s = enc h' s') :
    h = h' ∧ ∀ i, i < h → s i = s' i := by
  have e2 : 2 ^ h * prodF s h = 2 ^ h' * prodF s' h' := by
    rw [← enc_succ, ← enc_succ, e]
  have := pow_cancel 2 (by decide) h h' _ _ e2 (two_not_dvd_prod s h) (two_not_dvd_prod s' h')
  obtain ⟨eh, ep⟩ := this
  subst eh
  exact ⟨rfl, prodF_inj s s' h ep⟩

/-! ### MetaCode（metacode.py）：記号は 4 つ組の自然数の列 S i（長さ 4） -/

def metaR (h : Nat) (S : Nat → Nat → Nat) (n : Nat) : Prop :=
  ∃ c : Nat → Nat, encR h c n ∧ ∀ i, i < h → encR 4 (S i) (c i)

noncomputable def metacode (h : Nat) (S : Nat → Nat → Nat) : Nat := enc h (fun i => enc 4 (S i))

theorem metacode_correct (h : Nat) (S : Nat → Nat → Nat) (n : Nat) : metaR h S n ↔ n = metacode h S := by
  constructor
  · intro ⟨c, hc, hs⟩
    rw [encode_correct] at hc
    rw [hc]
    exact enc_congr' c (fun i => enc 4 (S i)) h (fun i hi => (encode_correct _ _ _).mp (hs i hi))
  · intro e
    exact ⟨fun i => enc 4 (S i), (encode_correct _ _ _).mpr e, fun i _ => (encode_correct _ _ _).mpr rfl⟩

/-- MetaCode は単射：番号から、列の長さと各記号（4 つ組）が一意に定まる。 -/
theorem metacode_inj (h h' : Nat) (S S' : Nat → Nat → Nat) (e : metacode h S = metacode h' S') :
    h = h' ∧ ∀ i, i < h → ∀ j, j < 4 → S i j = S' i j := by
  obtain ⟨eh, es⟩ := enc_inj _ _ _ _ e
  exact ⟨eh, fun i hi j hj => (enc_inj _ _ _ _ (es i hi)).2 j hj⟩

#print axioms nth_correct
#print axioms encode_correct
#print axioms enc_inj
#print axioms metacode_correct
#print axioms metacode_inj

end Enc
