/-
  別紙 G の補題 G7（CNF の分解と名前どうしの比較）の形式化（改訂40）。順序数のライブラリは使わず、
  ε0 未満のカントール標準形の記法 ON（zero と ω^e + r）を自分で定義する。

  ・ON.cmp：標準形の比較（先頭の指数、等しければ残り）。cmp_swap・cmp_eq・cmp_trans。
  ・NF：標準形（残りの先頭の指数は先頭以下）。normAdd：ω^e + r を標準形に直す（吸収）。
  ・lt_wf：NF の上で、比較による順序は整礎（O の再帰が成り立つ根拠）。
  ・分解 dec は「i > 0 なら (a, b) が一意で a, b < i」という性質だけを仮定する（素数による具体的な分解が
    この性質をもつことは Dec.lean で示す）。norm i = 名前 i の表す標準形。
  ・table_sound：cnf.py の表の条件を満たす表の行は、norm についての本当の分解・比較に一致する。
  ・table_exists：本当の表は条件を満たす。cnf_cmp_correct：生成プログラムの cnf_cmp の主張そのもの。
-/
namespace G7

inductive ON where
  | zero
  | oadd (e r : ON)
deriving DecidableEq

def ON.cmp : ON → ON → Ordering
  | .zero, .zero => .eq
  | .zero, .oadd _ _ => .lt
  | .oadd _ _, .zero => .gt
  | .oadd e r, .oadd e' r' =>
    match ON.cmp e e' with
    | .eq => ON.cmp r r'
    | o => o

theorem cmp_swap : ∀ x y : ON, ON.cmp x y = (ON.cmp y x).swap
  | .zero, .zero => rfl
  | .zero, .oadd _ _ => rfl
  | .oadd _ _, .zero => rfl
  | .oadd e r, .oadd e' r' => by
    simp only [ON.cmp]
    rw [cmp_swap e e']
    cases h : ON.cmp e' e <;> simp [Ordering.swap, cmp_swap r r']

theorem cmp_self : ∀ x : ON, ON.cmp x x = .eq
  | .zero => rfl
  | .oadd e r => by simp only [ON.cmp]; rw [cmp_self e]; exact cmp_self r

theorem cmp_eq : ∀ x y : ON, ON.cmp x y = .eq → x = y
  | .zero, .zero, _ => rfl
  | .zero, .oadd _ _, h => by simp [ON.cmp] at h
  | .oadd _ _, .zero, h => by simp [ON.cmp] at h
  | .oadd e r, .oadd e' r', h => by
    simp only [ON.cmp] at h
    cases he : ON.cmp e e' with
    | eq => rw [he] at h; rw [cmp_eq e e' he, cmp_eq r r' h]
    | lt => rw [he] at h; simp at h
    | gt => rw [he] at h; simp at h

theorem cmp_trans_lt : ∀ x y z : ON, ON.cmp x y = .lt → ON.cmp y z = .lt → ON.cmp x z = .lt
  | .zero, .zero, _, h, _ => by simp [ON.cmp] at h
  | .zero, .oadd _ _, .zero, _, h => by simp [ON.cmp] at h
  | .zero, .oadd _ _, .oadd _ _, _, _ => rfl
  | .oadd _ _, .zero, _, h, _ => by simp [ON.cmp] at h
  | .oadd _ _, .oadd _ _, .zero, _, h => by simp [ON.cmp] at h
  | .oadd e1 r1, .oadd e2 r2, .oadd e3 r3, h1, h2 => by
    simp only [ON.cmp] at h1 h2 ⊢
    cases c12 : ON.cmp e1 e2 <;> cases c23 : ON.cmp e2 e3 <;> rw [c12] at h1 <;> rw [c23] at h2 <;>
      simp at h1 h2
    · rw [cmp_trans_lt e1 e2 e3 c12 c23]
    · rw [cmp_eq e2 e3 c23] at c12; rw [c12]
    · rw [cmp_eq e1 e2 c12]; rw [c23]
    · rw [cmp_eq e1 e2 c12, cmp_eq e2 e3 c23, cmp_self]
      exact cmp_trans_lt r1 r2 r3 h1 h2

def lt (x y : ON) : Prop := ON.cmp x y = .lt

-- ---------- 標準形 ----------
def leadLe (r : ON) (e : ON) : Prop :=
  match r with
  | .zero => True
  | .oadd e' _ => ON.cmp e' e ≠ .gt

inductive NF : ON → Prop where
  | zero : NF .zero
  | oadd {e r : ON} : NF e → NF r → leadLe r e → NF (.oadd e r)

/-- ω^e + r を標準形に直す：r の先頭の指数が e より大きければ ω^e は吸収される。 -/
def normAdd (e r : ON) : ON :=
  match r with
  | .zero => .oadd e .zero
  | .oadd e' r' => if ON.cmp e e' = .lt then .oadd e' r' else .oadd e (.oadd e' r')

theorem normAdd_nf (e r : ON) (he : NF e) (hr : NF r) : NF (normAdd e r) := by
  cases r with
  | zero => exact NF.oadd he NF.zero trivial
  | oadd e' r' =>
    simp only [normAdd]
    by_cases h : ON.cmp e e' = .lt
    · rw [if_pos h]; exact hr
    · rw [if_neg h]
      refine NF.oadd he hr ?_
      simp only [leadLe]
      intro hg
      rw [cmp_swap] at hg
      cases c : ON.cmp e e' <;> rw [c] at hg <;> simp [Ordering.swap] at hg
      exact h c

-- ---------- 整礎性 ----------
def ltNF (x y : ON) : Prop := NF x ∧ NF y ∧ lt x y

theorem acc_zero : Acc ltNF .zero := by
  constructor
  intro y ⟨_, _, h⟩
  cases y <;> simp [lt, ON.cmp] at h

/-- NF の上で、比較による順序は整礎。 -/
theorem lt_wf : WellFounded ltNF := by
  -- C e：NF (ω^e + r) なら ω^e + r は到達可能
  have stepB : ∀ e, (∀ e', ltNF e' e → ∀ r, NF (.oadd e' r) → Acc ltNF (.oadd e' r)) →
      ∀ r, Acc ltNF r → NF (.oadd e r) → Acc ltNF (.oadd e r) := by
    intro e ihe r hr
    induction hr with
    | intro r _ ihr =>
      intro hnf
      constructor
      intro y ⟨hy, _, hlt⟩
      cases y with
      | zero => exact acc_zero
      | oadd e' r' =>
        simp only [lt, ON.cmp] at hlt
        cases c : ON.cmp e' e with
        | lt =>
          have hy0 := hy
          cases hnf with
          | oadd he _ _ =>
          cases hy with
          | oadd he' _ _ => exact ihe e' ⟨he', he, c⟩ r' hy0
        | eq =>
          rw [c] at hlt
          have := cmp_eq e' e c; subst this
          have hy0 := hy
          cases hy with
          | oadd _ hr' _ =>
          cases hnf with
          | oadd _ hr _ => exact ihr r' ⟨hr', hr, hlt⟩ hy0
        | gt => rw [c] at hlt; simp at hlt
  have C : ∀ e, Acc ltNF e → ∀ r, NF (.oadd e r) → Acc ltNF (.oadd e r) := by
    intro e hacc
    induction hacc with
    | intro e _ ihe =>
      -- 段 A：NF (ω^e + r) なら r は到達可能（r の構造に関する帰納法）
      have stepA : ∀ r, NF (.oadd e r) → Acc ltNF r := by
        intro r
        induction r with
        | zero => intro _; exact acc_zero
        | oadd e2 r2 _ ih2 =>
          intro hnf
          cases hnf with
          | oadd he hr hlead =>
          simp only [leadLe] at hlead
          cases c : ON.cmp e2 e with
          | lt =>
            have hr0 := hr
            cases hr with
            | oadd he2 _ _ => exact ihe e2 ⟨he2, he, c⟩ r2 hr0
          | eq =>
            have := cmp_eq e2 e c; subst this
            cases hr with
            | oadd _ hr2 hl2 =>
            exact stepB e2 ihe r2 (ih2 (NF.oadd he hr2 hl2)) (NF.oadd he hr2 hl2)
          | gt => exact absurd c hlead
      intro r hnf
      exact stepB e ihe r (stepA r hnf) hnf
  constructor
  intro x
  induction x with
  | zero => exact acc_zero
  | oadd e r ihe _ =>
    constructor
    intro y hy
    -- y は ω^e + r より小さい NF。ω^e + r 自身の到達可能性を示せば足りる
    have hx : NF (.oadd e r) := hy.2.1
    cases hx with
    | oadd he _ _ =>
    exact (C e ihe r hy.2.1).inv hy

-- ---------- 名前と分解 ----------
/-- 分解 dec の仕様：i > 0 なら (a, b) は一意に存在し、a, b < i。 -/
structure DecSpec where
  D : Nat → Nat → Nat → Prop
  uniq : ∀ i a b a' b', D i a b → D i a' b' → a = a' ∧ b = b'
  lt : ∀ i a b, D i a b → a < i ∧ b < i
  ex : ∀ i, 0 < i → ∃ a b, D i a b

section Table
variable (S : DecSpec)

noncomputable def dA (i : Nat) (h : 0 < i) : Nat := Classical.choose (S.ex i h)
noncomputable def dB (i : Nat) (h : 0 < i) : Nat := Classical.choose (Classical.choose_spec (S.ex i h))
theorem dAB (i : Nat) (h : 0 < i) : S.D i (dA S i h) (dB S i h) :=
  Classical.choose_spec (Classical.choose_spec (S.ex i h))

/-- 名前 i の表す標準形：CNF(0) = 0、CNF(i) = ω^{CNF(a)} + CNF(b)（標準形に直す）。 -/
noncomputable def norm (i : Nat) : ON :=
  if h : 0 < i then normAdd (norm (dA S i h)) (norm (dB S i h)) else .zero
termination_by i
decreasing_by
  all_goals simp_wf
  · exact (S.lt _ _ _ (dAB S i h)).1
  · exact (S.lt _ _ _ (dAB S i h)).2

theorem norm_dec (i a b : Nat) (hd : S.D i a b) (hi : 0 < i) :
    norm S i = normAdd (norm S a) (norm S b) := by
  rw [norm, dif_pos hi]
  have := S.uniq i _ _ a b (dAB S i hi) hd
  rw [this.1, this.2]

theorem norm_zero : norm S 0 = .zero := by
  rw [norm]; simp

theorem norm_nf : ∀ i, NF (norm S i) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    rw [norm]
    by_cases h : 0 < i
    · rw [dif_pos h]
      have hl := S.lt _ _ _ (dAB S i h)
      exact normAdd_nf _ _ (ih _ hl.1) (ih _ hl.2)
    · rw [dif_neg h]; exact NF.zero

def code : Ordering → Nat
  | .lt => 0
  | .eq => 1
  | .gt => 2

theorem code_eq1 (o : Ordering) : code o = 1 ↔ o = .eq := by cases o <;> simp [code]
theorem code_eq2 (o : Ordering) : code o = 2 ↔ o = .gt := by cases o <;> simp [code]

/-- cnf.py の表の条件。HR i h r は行 (0, i, H, R)、CM i k c は行 (1, i, k, c)。 -/
def hrOk (HR CM : Nat → Nat → Nat → Prop) (i h r : Nat) : Prop :=
  ∃ a b, a < i ∧ b < i ∧ S.D i a b ∧
    ((b = 0 ∧ h = a ∧ r = 0) ∨
     (b ≠ 0 ∧ ∃ hb rb, HR b hb rb ∧ ∃ c, CM hb a c ∧ ((c = 2 ∧ h = hb ∧ r = rb) ∨ (c ≠ 2 ∧ h = a ∧ r = b))))

def cmpOk (HR CM : Nat → Nat → Nat → Prop) (i k c : Nat) : Prop :=
  (i = 0 ∧ k = 0 ∧ c = 1) ∨ (i = 0 ∧ k ≠ 0 ∧ c = 0) ∨ (i ≠ 0 ∧ k = 0 ∧ c = 2) ∨
  (i ≠ 0 ∧ k ≠ 0 ∧ ∃ hi ri, HR i hi ri ∧ ∃ hk rk, HR k hk rk ∧ ∃ c1, CM hi hk c1 ∧
    ((c1 ≠ 1 ∧ c = c1) ∨ (c1 = 1 ∧ ∃ c2, CM ri rk c2 ∧ c2 = c)))

def tableOk (HR CM : Nat → Nat → Nat → Prop) : Prop :=
  (∀ i h r, HR i h r → hrOk S HR CM i h r) ∧ (∀ i k c, CM i k c → cmpOk HR CM i k c)

theorem cmp_oadd (e r e' r' : ON) :
    ON.cmp (.oadd e r) (.oadd e' r') = (match ON.cmp e e' with | .eq => ON.cmp r r' | o => o) := rfl

theorem cmp_zero_oadd (e r : ON) : ON.cmp .zero (.oadd e r) = .lt := rfl
theorem cmp_oadd_zero (e r : ON) : ON.cmp (.oadd e r) .zero = .gt := rfl

/-- 健全性：条件を満たす表の行は、本当の分解・比較に一致する。 -/
theorem table_sound (HR CM : Nat → Nat → Nat → Prop) (hT : tableOk S HR CM) :
    ∀ N, (∀ i h r, i < N → HR i h r → h < i ∧ r < i ∧ norm S i = .oadd (norm S h) (norm S r)) ∧
         (∀ i k c, i < N → k < N → CM i k c → c = code (ON.cmp (norm S i) (norm S k))) := by
  intro N
  induction N with
  | zero => exact ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ N ih =>
    have HRs : ∀ i h r, i < N + 1 → HR i h r → h < i ∧ r < i ∧ norm S i = .oadd (norm S h) (norm S r) := by
      intro i h r hi hrow
      obtain ⟨a, b, ha, hb, hd, hcase⟩ := hT.1 i h r hrow
      have ipos : 0 < i := by omega
      rw [norm_dec S i a b hd ipos]
      rcases hcase with ⟨hb0, e1, e2⟩ | ⟨hb0, hb', rb, hrb, c, hc, hsub⟩
      · subst hb0; subst e1; subst e2
        refine ⟨ha, ipos, ?_⟩
        rw [norm_zero]; rfl
      · obtain ⟨hhb, hrb', hnb⟩ := ih.1 b hb' rb (by omega) hrb
        have hcv := ih.2 hb' a c (by omega) (by omega) hc
        rw [hnb]
        rcases hsub with ⟨hc2, e1, e2⟩ | ⟨hc2, e1, e2⟩
        · subst e1; subst e2
          refine ⟨by omega, by omega, ?_⟩
          rw [hc2] at hcv
          have hg := (code_eq2 _).mp hcv.symm
          have hl : ON.cmp (norm S a) (norm S h) = .lt := by rw [cmp_swap, hg]; rfl
          simp only [normAdd]; rw [if_pos hl]
        · subst e1; subst e2
          refine ⟨ha, hb, ?_⟩
          have hnl : ON.cmp (norm S h) (norm S hb') ≠ .lt := by
            intro hl
            rw [cmp_swap] at hl
            apply hc2; rw [hcv]
            cases e : ON.cmp (norm S hb') (norm S h) <;> rw [e] at hl <;> simp [Ordering.swap] at hl
            rfl
          simp only [normAdd]; rw [if_neg hnl, hnb]
    refine ⟨HRs, ?_⟩
    intro i k c hi hk hrow
    rcases hT.2 i k c hrow with ⟨e1, e2, e3⟩ | ⟨e1, hk0, e3⟩ | ⟨hi0, e2, e3⟩ |
        ⟨hi0, hk0, hi', ri, hri, hk', rk, hrk, c1, hc1, hsub⟩
    · subst e1; subst e2; subst e3; rw [norm_zero]; rfl
    · subst e1; subst e3
      obtain ⟨a, b, hd⟩ := (S.ex k (by omega))
      rw [norm_zero, norm_dec S k a b hd (by omega)]
      cases hb : norm S b with
      | zero => rfl
      | oadd _ _ => simp only [normAdd]; split <;> rfl
    · subst e2; subst e3
      obtain ⟨a, b, hd⟩ := (S.ex i (by omega))
      rw [norm_zero, norm_dec S i a b hd (by omega)]
      cases hb : norm S b with
      | zero => rfl
      | oadd _ _ => simp only [normAdd]; split <;> rfl
    · obtain ⟨hhi, hri', hni⟩ := HRs i hi' ri hi hri
      obtain ⟨hhk, hrk', hnk⟩ := HRs k hk' rk hk hrk
      have hc1v := ih.2 hi' hk' c1 (by omega) (by omega) hc1
      rw [hni, hnk, cmp_oadd]
      rcases hsub with ⟨hne, e⟩ | ⟨he1, c2, hc2, e⟩
      · subst e
        rw [hc1v]
        cases o : ON.cmp (norm S hi') (norm S hk') with
        | eq => rw [o] at hc1v; exact absurd hc1v (by simp [code]; exact hne)
        | lt => rfl
        | gt => rfl
      · subst e
        rw [he1] at hc1v
        have heq := (code_eq1 _).mp hc1v.symm
        rw [heq]
        exact ih.2 ri rk c2 (by omega) (by omega) hc2

/-- 本当の正規化した先頭 (H, R)：cnf.py の規則どおり（b = 0 なら (a, 0)、H(b) が a より大きければ吸収）。 -/
noncomputable def HRf (i : Nat) : Nat × Nat :=
  if h : 0 < i then
    if hb : dB S i h = 0 then (dA S i h, 0)
    else if ON.cmp (norm S (HRf (dB S i h)).1) (norm S (dA S i h)) = .gt then HRf (dB S i h)
    else (dA S i h, dB S i h)
  else (0, 0)
termination_by i
decreasing_by
  all_goals simp_wf
  all_goals exact (S.lt _ _ _ (dAB S i h)).2

theorem HRf_spec : ∀ i, 0 < i → (HRf S i).1 < i ∧ (HRf S i).2 < i ∧
    norm S i = .oadd (norm S (HRf S i).1) (norm S (HRf S i).2) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro hi
  have hd := dAB S i hi
  have hl := S.lt _ _ _ hd
  rw [norm_dec S i _ _ hd hi]
  rw [HRf, dif_pos hi]
  by_cases hb : dB S i hi = 0
  · rw [dif_pos hb]; simp only
    refine ⟨hl.1, hi, ?_⟩
    rw [hb, norm_zero]; rfl
  · rw [dif_neg hb]
    have bpos : 0 < dB S i hi := Nat.pos_of_ne_zero hb
    obtain ⟨h1, h2, hn⟩ := ih _ hl.2 bpos
    by_cases hg : ON.cmp (norm S (HRf S (dB S i hi)).1) (norm S (dA S i hi)) = .gt
    · rw [if_pos hg]
      refine ⟨by omega, by omega, ?_⟩
      rw [hn]; simp only [normAdd]
      have hlt : ON.cmp (norm S (dA S i hi)) (norm S (HRf S (dB S i hi)).1) = .lt := by rw [cmp_swap, hg]; rfl
      rw [if_pos hlt]
    · rw [if_neg hg]
      refine ⟨hl.1, hl.2, ?_⟩
      rw [hn]; simp only [normAdd]
      have hnl : ON.cmp (norm S (dA S i hi)) (norm S (HRf S (dB S i hi)).1) ≠ .lt := by
        intro h; rw [cmp_swap] at h; apply hg
        cases e : ON.cmp (norm S (HRf S (dB S i hi)).1) (norm S (dA S i hi)) <;> rw [e] at h <;>
          simp [Ordering.swap] at h
      rw [if_neg hnl]

def HRt (i h r : Nat) : Prop := 0 < i ∧ (h, r) = HRf S i
def CMt (i k c : Nat) : Prop := c = code (ON.cmp (norm S i) (norm S k))

theorem norm_pos_oadd (i : Nat) (hi : 0 < i) : ∃ e r, norm S i = .oadd e r :=
  ⟨_, _, (HRf_spec S i hi).2.2⟩

theorem true_table_ok : tableOk S (HRt S) (CMt S) := by
  constructor
  · intro i h r ⟨hi, e⟩
    have hd := dAB S i hi
    have hl := S.lt _ _ _ hd
    refine ⟨dA S i hi, dB S i hi, hl.1, hl.2, hd, ?_⟩
    rw [HRf, dif_pos hi] at e
    by_cases hb : dB S i hi = 0
    · rw [dif_pos hb] at e
      simp only [Prod.mk.injEq] at e
      exact Or.inl ⟨hb, e.1, e.2⟩
    · rw [dif_neg hb] at e
      have bpos : 0 < dB S i hi := Nat.pos_of_ne_zero hb
      refine Or.inr ⟨hb, (HRf S (dB S i hi)).1, (HRf S (dB S i hi)).2, ⟨bpos, rfl⟩,
        code (ON.cmp (norm S (HRf S (dB S i hi)).1) (norm S (dA S i hi))), rfl, ?_⟩
      by_cases hg : ON.cmp (norm S (HRf S (dB S i hi)).1) (norm S (dA S i hi)) = .gt
      · rw [if_pos hg] at e
        refine Or.inl ⟨by rw [hg]; rfl, ?_, ?_⟩
        · rw [← e]
        · rw [← e]
      · rw [if_neg hg] at e
        simp only [Prod.mk.injEq] at e
        refine Or.inr ⟨fun h2 => hg ((code_eq2 _).mp h2), e.1, e.2⟩
  · intro i k c hc
    simp only [CMt] at hc
    by_cases hi : i = 0 <;> by_cases hk : k = 0
    · subst hi; subst hk; rw [norm_zero] at hc; exact Or.inl ⟨rfl, rfl, hc⟩
    · subst hi
      obtain ⟨e, r, hn⟩ := norm_pos_oadd S k (by omega)
      rw [norm_zero, hn] at hc
      exact Or.inr (Or.inl ⟨rfl, hk, hc⟩)
    · subst hk
      obtain ⟨e, r, hn⟩ := norm_pos_oadd S i (by omega)
      rw [norm_zero, hn] at hc
      exact Or.inr (Or.inr (Or.inl ⟨hi, rfl, hc⟩))
    · have si := HRf_spec S i (by omega)
      have sk := HRf_spec S k (by omega)
      refine Or.inr (Or.inr (Or.inr ⟨hi, hk, (HRf S i).1, (HRf S i).2, ⟨by omega, rfl⟩,
        (HRf S k).1, (HRf S k).2, ⟨by omega, rfl⟩,
        code (ON.cmp (norm S (HRf S i).1) (norm S (HRf S k).1)), rfl, ?_⟩))
      rw [si.2.2, sk.2.2, cmp_oadd] at hc
      cases o : ON.cmp (norm S (HRf S i).1) (norm S (HRf S k).1) with
      | eq =>
        rw [o] at hc
        exact Or.inr ⟨rfl, code (ON.cmp (norm S (HRf S i).2) (norm S (HRf S k).2)), rfl, hc.symm⟩
      | lt => rw [o] at hc; exact Or.inl ⟨by simp [code], hc⟩
      | gt => rw [o] at hc; exact Or.inl ⟨by simp [code], hc⟩

/-- 生成プログラムの cnf_cmp の主張：条件を満たす表に行 (1, i, k, c) があることは、
    c が CNF(i) と CNF(k) の本当の比較結果であることと同値。 -/
theorem cnf_cmp_correct (i k c : Nat) :
    (∃ HR CM, tableOk S HR CM ∧ CM i k c) ↔ c = code (ON.cmp (norm S i) (norm S k)) := by
  constructor
  · intro ⟨HR, CM, hT, hc⟩
    exact (table_sound S HR CM hT (max i k + 1)).2 i k c (by omega) (by omega) hc
  · intro hc
    exact ⟨HRt S, CMt S, true_table_ok S, hc⟩

/-- 名前どうしの順序（cnf_lt）は整礎。O の再帰（O(i) = {O(k) : CNF(k) < CNF(i)}）はこれで成り立つ。 -/
theorem name_lt_wf : WellFounded (fun k i => ON.cmp (norm S k) (norm S i) = .lt) := by
  apply Subrelation.wf _ (InvImage.wf (norm S) lt_wf)
  intro k i h
  exact ⟨norm_nf S k, norm_nf S i, h⟩

end Table

#print axioms G7.cnf_cmp_correct
#print axioms G7.name_lt_wf

end G7
