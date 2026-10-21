/-
  書き写しの検証（改訂43）：集合の言葉の条件（TrCore の Rstd）から、自然数の値への橋渡し。

  構造 (α, mem) について、次だけを仮定する（Model）。M = (V_{κ+1})^L はこれを満たす（H は遺伝的有限な集合のクラスでも V_κ でもよい。改訂45 の TrSem では H = V_κ とする）。
  ・ext：外延性。・wf：mem は整礎。
  ・num n：フォン・ノイマンの自然数 n（num n の元はちょうど num m、m < n）。
  ・H：有限集合を作ってよい元のクラス。num n は H に属し、H の元の有限個からなる集合は存在して H に属する。

  主な結果（TrMeans の mean_X と合わせると、生成プログラムの出力した式そのものについての主張になる）：
  ・num_iff：Num k x ⟺ x = num k。nat_iff：NatM x ⟺ x はある num n。
  ・pair_unique：Pair p a b ∧ Pair p a' b' → a = a' ∧ b = b'。
  ・hyper_iff：Hyper (num n) (num a) (num b) c ⟺ c = num (H(n, a, b))（Tables.H）。
  ・op_iff・divides_iff・prime_iff：加法・乗法・冪、割り切り、素数（Dec.Prime）。
  ・nth_prime_iff：NthPrime (num i) p ⟺ p = num (p_i)（Enc.np）。
  ・encode_iff：s が長さ n の列 f を表すなら、EncodeM s c ⟺ c = num (Encode(f))（Enc.enc）。
  ・metacode_iff：s が 4 つ組の列 S を表すなら、MetaCodeM n s ⟺ n = num (MetaCode(S))（Enc.metacode）。
-/
import TrMeans
import Tables
import Encode
namespace Tr

structure Model (α : Type) where
  mem : α → α → Prop
  ext : ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b
  wf : WellFounded mem
  num : Nat → α
  num_mem : ∀ n x, mem x (num n) ↔ ∃ m, m < n ∧ x = num m
  H : α → Prop
  H_num : ∀ n, H (num n)
  fin : ∀ l : List α, (∀ x, x ∈ l → H x) → ∃ s, H s ∧ ∀ x, mem x s ↔ x ∈ l

namespace Model
variable {α : Type} (M : Model α)

/-! ### 自然数 -/

theorem irrefl (x : α) : ¬ M.mem x x := by
  intro h
  have : ∀ y, Acc M.mem y → y ≠ x := by
    intro y hy
    induction hy with
    | intro y _ ih => intro e; subst e; exact ih y h rfl
  exact this x (M.wf.apply x) rfl

theorem num_lt {m n : Nat} (h : m < n) : M.mem (M.num m) (M.num n) := (M.num_mem n _).mpr ⟨m, h, rfl⟩

theorem num_inj {m n : Nat} (h : M.num m = M.num n) : m = n := by
  rcases Nat.lt_trichotomy m n with c | c | c
  · have := M.num_lt c; rw [h] at this; exact absurd this (M.irrefl _)
  · exact c
  · have := M.num_lt c; rw [h] at this; exact absurd this (M.irrefl _)

theorem num_mem_iff {m n : Nat} : M.mem (M.num m) (M.num n) ↔ m < n := by
  constructor
  · intro h
    obtain ⟨k, hk, e⟩ := (M.num_mem n _).mp h
    rw [M.num_inj e]; exact hk
  · exact M.num_lt

theorem empty_iff (x : α) : Empty M.mem x ↔ x = M.num 0 := by
  constructor
  · intro h
    apply M.ext
    intro y
    simp only [M.num_mem]
    constructor
    · intro hy; exact absurd hy (h y)
    · rintro ⟨m, hm, _⟩; omega
  · rintro rfl y hy
    obtain ⟨m, hm, _⟩ := (M.num_mem 0 y).mp hy
    omega

theorem succ_num_iff (n : Nat) (c : α) : Succ M.mem (M.num n) c ↔ c = M.num (n + 1) := by
  constructor
  · intro h
    apply M.ext
    intro y
    rw [h y, M.num_mem, M.num_mem]
    constructor
    · rintro (⟨m, hm, rfl⟩ | rfl)
      · exact ⟨m, by omega, rfl⟩
      · exact ⟨n, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with c | c
      · exact Or.inl ⟨m, c, rfl⟩
      · exact Or.inr (by rw [c])
  · rintro rfl y
    rw [M.num_mem, M.num_mem]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with c | c
      · exact Or.inl ⟨m, c, rfl⟩
      · exact Or.inr (by rw [c])
    · rintro (⟨m, hm, rfl⟩ | rfl)
      · exact ⟨m, by omega, rfl⟩
      · exact ⟨n, by omega, rfl⟩

/-- c = b ∪ {b} で c が自然数なら、b も自然数で c の前者。 -/
theorem succ_into_num {b : α} {N : Nat} (h : Succ M.mem b (M.num N)) : ∃ j, N = j + 1 ∧ b = M.num j := by
  have hb : M.mem b (M.num N) := (h b).mpr (Or.inr rfl)
  obtain ⟨j, hj, rfl⟩ := (M.num_mem N b).mp hb
  have := (M.succ_num_iff j (M.num N)).mp h
  exact ⟨j, M.num_inj this, rfl⟩

theorem num_iff : ∀ k (x : α), Num M.mem k x ↔ x = M.num k := by
  intro k
  induction k with
  | zero => intro x; exact M.empty_iff x
  | succ k ih =>
    intro x
    simp only [Num]
    constructor
    · rintro ⟨w, _, hs, hn⟩
      rw [ih] at hn; subst hn
      exact (M.succ_num_iff k x).mp hs
    · rintro rfl
      exact ⟨M.num k, M.num_lt (by omega), (M.succ_num_iff k _).mpr rfl, (ih _).mpr rfl⟩

theorem isOne_iff (x : α) : IsOne M.mem x ↔ x = M.num 1 := by
  have := M.num_iff 1 x
  simp only [Num] at this
  rw [← this]
  simp only [IsOne, M.empty_iff, Num]
  constructor
  · rintro ⟨e, he, h0, hs⟩; exact ⟨e, he, hs, h0⟩
  · rintro ⟨e, he, hs, h0⟩; exact ⟨e, he, h0, hs⟩

theorem natM_num (n : Nat) : NatM M.mem (M.num n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz u hu
    obtain ⟨m, hm, rfl⟩ := (M.num_mem n z).mp hz
    obtain ⟨k, hk, rfl⟩ := (M.num_mem m u).mp hu
    exact M.num_lt (by omega)
  · intro z hz u hu w hw
    obtain ⟨m, _, rfl⟩ := (M.num_mem n z).mp hz
    obtain ⟨k, hk, rfl⟩ := (M.num_mem m u).mp hu
    obtain ⟨j, hj, rfl⟩ := (M.num_mem k w).mp hw
    exact M.num_lt (by omega)
  · intro z hz
    have : ∃ m, z = M.num m := by
      rcases hz with hz | rfl
      · obtain ⟨m, _, rfl⟩ := (M.num_mem n z).mp hz; exact ⟨m, rfl⟩
      · exact ⟨n, rfl⟩
    obtain ⟨m, rfl⟩ := this
    cases m with
    | zero => exact Or.inl ((M.empty_iff _).mpr rfl)
    | succ m => exact Or.inr ⟨M.num m, M.num_lt (by omega), (M.succ_num_iff m _).mpr rfl⟩

theorem nat_iff (x : α) : NatM M.mem x ↔ ∃ n, x = M.num n := by
  constructor
  · intro hx
    induction x using M.wf.induction with
    | _ x ih =>
    obtain ⟨htr, hel, hcase⟩ := hx
    rcases hcase x (Or.inr rfl) with h0 | ⟨w, hw, hs⟩
    · exact ⟨0, (M.empty_iff x).mp h0⟩
    · have hwn : NatM M.mem w := by
        refine ⟨fun z hz u hu => hel w hw z hz u hu, ?_, ?_⟩
        · intro z hz u hu v hv
          exact hel z (htr w hw z hz) u hu v hv
        · intro z hz
          apply hcase z
          rcases hz with hz | rfl
          · exact Or.inl (htr w hw z hz)
          · exact Or.inl hw
      obtain ⟨n, rfl⟩ := ih w hw hwn
      exact ⟨n + 1, (M.succ_num_iff n x).mp hs⟩
  · rintro ⟨n, rfl⟩; exact M.natM_num n

/-! ### 順序対 -/

theorem pair_unique {p a b a' b' : α} (h : Pair M.mem p a b) (h' : Pair M.mem p a' b') : a = a' ∧ b = b' := by
  obtain ⟨hall, ⟨s, hs, hsing⟩, ⟨s2, hs2, hdbl⟩⟩ := h
  obtain ⟨hall', ⟨s', hs', hsing'⟩, ⟨s3, hs3, hdbl'⟩⟩ := h'
  have eaa : a = a' := by
    rcases hall' s hs with h1 | h1
    · exact (hsing.2 _ h1.1).symm
    · exact (hsing.2 _ h1.1).symm
  subst eaa
  refine ⟨rfl, ?_⟩
  by_cases hab : b = a
  · subst hab
    rcases hall s3 hs3 with h1 | h1
    · exact (h1.2 _ hdbl'.2.1).symm
    · rcases h1.2.2 _ hdbl'.2.1 with e | e
      · exact e.symm
      · exact e.symm
  · rcases hall' s2 hs2 with h1 | h1
    · exact absurd (h1.2 _ hdbl.2.1) hab
    · rcases h1.2.2 _ hdbl.2.1 with e | e
      · exact absurd e hab
      · exact e

theorem triple_unique {p n b v n' b' v' : α} (h : Triple M.mem p n b v) (h' : Triple M.mem p n' b' v') :
    n = n' ∧ b = b' ∧ v = v' := by
  obtain ⟨q, h1, h2⟩ := h
  obtain ⟨q', h1', h2'⟩ := h'
  obtain ⟨eq, ev⟩ := M.pair_unique h1 h1'
  subst eq
  obtain ⟨en, eb⟩ := M.pair_unique h2 h2'
  exact ⟨en, eb, ev⟩

open Classical in
/-- 有限集合（H の元からなるリストの元をちょうど元にもつ集合）。 -/
noncomputable def set (l : List α) : α :=
  if h : ∀ x, x ∈ l → M.H x then Classical.choose (M.fin l h) else M.num 0

theorem set_spec (l : List α) (h : ∀ x, x ∈ l → M.H x) : M.H (M.set l) ∧ ∀ x, M.mem x (M.set l) ↔ x ∈ l := by
  unfold set
  rw [dif_pos h]
  exact Classical.choose_spec (M.fin l h)

noncomputable def pr (a b : α) : α := M.set [M.set [a], M.set [a, b]]

theorem pr_spec {a b : α} (ha : M.H a) (hb : M.H b) : M.H (M.pr a b) ∧ Pair M.mem (M.pr a b) a b := by
  have h1 := M.set_spec [a] (by intro x hx; simp at hx; subst hx; exact ha)
  have h2 := M.set_spec [a, b] (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
  have h3 := M.set_spec [M.set [a], M.set [a, b]]
    (by intro x hx; simp at hx; rcases hx with rfl | rfl; exact h1.1; exact h2.1)
  unfold pr
  refine ⟨h3.1, ?_, ?_, ?_⟩
  · intro s hs
    rw [h3.2] at hs; simp at hs
    rcases hs with rfl | rfl
    · left; exact ⟨(h1.2 a).mpr (by simp), fun t ht => by rw [h1.2] at ht; simpa using ht⟩
    · right; exact ⟨(h2.2 a).mpr (by simp), (h2.2 b).mpr (by simp), fun t ht => by rw [h2.2] at ht; simpa using ht⟩
  · exact ⟨M.set [a], (h3.2 _).mpr (by simp), (h1.2 a).mpr (by simp), fun t ht => by rw [h1.2] at ht; simpa using ht⟩
  · exact ⟨M.set [a, b], (h3.2 _).mpr (by simp), (h2.2 a).mpr (by simp), (h2.2 b).mpr (by simp),
      fun t ht => by rw [h2.2] at ht; simpa using ht⟩

/-- 自然数の組 (m, n) の順序対。 -/
noncomputable def np2 (m n : Nat) : α := M.pr (M.num m) (M.num n)
theorem np2_spec (m n : Nat) : M.H (M.np2 m n) ∧ Pair M.mem (M.np2 m n) (M.num m) (M.num n) :=
  M.pr_spec (M.H_num m) (M.H_num n)

/-- 自然数の三つ組 ((n, b), v)。 -/
noncomputable def nt3 (n b v : Nat) : α := M.pr (M.np2 n b) (M.num v)
theorem nt3_spec (n b v : Nat) : M.H (M.nt3 n b v) ∧ Triple M.mem (M.nt3 n b v) (M.num n) (M.num b) (M.num v) := by
  have h1 := M.np2_spec n b
  have h2 := M.pr_spec h1.1 (M.H_num v)
  exact ⟨h2.1, M.np2 n b, h2.2, h1.2⟩


/-! ### ハイパー演算の表 -/

theorem H_zero (A b : Nat) : Tables.H A 0 b = b + 1 := by simp [Tables.H]
theorem H_rec (A n b : Nat) : Tables.H A (n + 1) (b + 1) = Tables.H A n (Tables.H A (n + 1) b) := by
  simp [Tables.H]
theorem H_base1 (A : Nat) : Tables.H A 1 0 = A := by simp [Tables.H]
theorem H_base2 (A : Nat) : Tables.H A 2 0 = 0 := by simp [Tables.H]
theorem H_base3 (A k : Nat) : Tables.H A (k + 3) 0 = 1 := by simp [Tables.H]

theorem num_ne_empty_one {k : Nat} : (¬ Empty M.mem (M.num k) ↔ k ≠ 0) ∧ (IsOne M.mem (M.num k) ↔ k = 1) := by
  constructor
  · rw [M.empty_iff]
    constructor
    · intro h e; subst e; exact h rfl
    · intro h e; exact h (M.num_inj e)
  · rw [M.isOne_iff]
    constructor
    · exact M.num_inj
    · intro e; subst e; rfl

/-- 表の行の正しさ：n > 0 の行、または b が自然数の行 ((n, b), v) について、b = num m かつ v = num H(n, A, m)。 -/
theorem hyper_sound (t : α) (A : Nat) (ht : HyperTable M.mem t (M.num A)) :
    ∀ n b v p, M.mem p t → Triple M.mem p (M.num n) b v → (0 < n ∨ ∃ m, b = M.num m) →
      ∃ m, b = M.num m ∧ v = M.num (Tables.H A n m) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro b
  induction b using M.wf.induction with
  | _ b ihb =>
  intro v p hp htr hcond
  rcases ht p hp _ _ _ htr with ⟨h0, hs⟩ | ⟨n1, hn1, hs, hb0, hbase⟩ | ⟨n1, hn1, b1, hb1, hs, hsb, p2, hp2, w, htr2, p3, hp3, htr3⟩
  · have : n = 0 := M.num_inj ((M.empty_iff _).mp h0)
    subst this
    rcases hcond with h | ⟨m, rfl⟩
    · omega
    · exact ⟨m, rfl, by rw [(M.succ_num_iff m v).mp hs, H_zero]⟩
  · obtain ⟨k, rfl, rfl⟩ := M.succ_into_num hs
    refine ⟨0, (M.empty_iff b).mp hb0, ?_⟩
    rcases hbase with ⟨he, rfl⟩ | ⟨ho, hv⟩ | ⟨hne, hno, hv⟩
    · have : k = 0 := M.num_inj ((M.empty_iff _).mp he)
      subst this; rw [H_base1]
    · have : k = 1 := (M.num_ne_empty_one).2.mp ho
      subst this; rw [H_base2]; exact (M.empty_iff v).mp hv
    · have h1 : k ≠ 0 := (M.num_ne_empty_one).1.mp hne
      have h2 : k ≠ 1 := fun e => hno ((M.num_ne_empty_one).2.mpr e)
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [show j + 2 + 1 = j + 3 by omega, H_base3]
      exact (M.isOne_iff v).mp hv
  · obtain ⟨k, rfl, rfl⟩ := M.succ_into_num hs
    obtain ⟨m', rfl, rfl⟩ := ihb b1 hb1 w p2 hp2 htr2 (Or.inl (by omega))
    have eb : b = M.num (m' + 1) := (M.succ_num_iff m' b).mp hsb
    obtain ⟨m2, e2, rfl⟩ := ihn k (by omega) _ v p3 hp3 htr3 (Or.inr ⟨_, rfl⟩)
    refine ⟨m' + 1, eb, ?_⟩
    rw [H_rec, M.num_inj e2]

/-- 表を作るのに必要な (n, b) の一覧（閉じている）。 -/
def needs (A : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, b => [(0, b)]
  | n + 1, 0 => [(n + 1, 0)]
  | n + 1, b + 1 => (n + 1, b + 1) :: (needs A (n + 1) b ++ needs A n (Tables.H A (n + 1) b))
termination_by n b => (n, b)

theorem needs_head (A n b : Nat) : (n, b) ∈ needs A n b := by
  cases n with
  | zero => simp [needs]
  | succ n => cases b with
    | zero => simp [needs]
    | succ b => simp [needs]

theorem needs_closed (A : Nat) : ∀ n b, ∀ x, x ∈ needs A n b → ∀ y, y ∈ needs A x.1 x.2 → y ∈ needs A n b := by
  intro n b
  induction n, b using needs.induct A with
  | case1 b => intro x hx y hy; simp [needs] at hx; subst hx; exact hy
  | case2 n => intro x hx y hy; simp [needs] at hx; subst hx; exact hy
  | case3 n b ih1 ih2 =>
    intro x hx y hy
    rw [needs] at hx ⊢
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [needs] at hy; exact hy
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih1 x hx y hy))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih2 x hx y hy))

theorem needs_just (A n b k j : Nat) (h : (k + 1, j + 1) ∈ needs A n b) :
    (k + 1, j) ∈ needs A n b ∧ (k, Tables.H A (k + 1) j) ∈ needs A n b := by
  constructor
  · apply needs_closed A n b _ h
    show (k + 1, j) ∈ needs A (k + 1) (j + 1)
    rw [needs]; exact List.mem_cons_of_mem _ (List.mem_append_left _ (needs_head A _ _))
  · apply needs_closed A n b _ h
    show (k, Tables.H A (k + 1) j) ∈ needs A (k + 1) (j + 1)
    rw [needs]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (needs_head A _ _))

noncomputable def htab (A n b : Nat) : α :=
  M.set ((needs A n b).map (fun x => M.nt3 x.1 x.2 (Tables.H A x.1 x.2)))

theorem htab_spec (A n b : Nat) : M.H (M.htab A n b) ∧
    ∀ p, M.mem p (M.htab A n b) ↔ ∃ x, x ∈ needs A n b ∧ p = M.nt3 x.1 x.2 (Tables.H A x.1 x.2) := by
  have := M.set_spec ((needs A n b).map (fun x => M.nt3 x.1 x.2 (Tables.H A x.1 x.2)))
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact (M.nt3_spec _ _ _).1)
  refine ⟨this.1, fun p => ?_⟩
  rw [htab, this.2, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem htab_row (A n b : Nat) {x : Nat × Nat} (hx : x ∈ needs A n b) :
    M.mem (M.nt3 x.1 x.2 (Tables.H A x.1 x.2)) (M.htab A n b) :=
  ((M.htab_spec A n b).2 _).mpr ⟨x, hx, rfl⟩

theorem htab_ok (A n b : Nat) : HyperTable M.mem (M.htab A n b) (M.num A) := by
  intro p hp n' b' v' htr
  obtain ⟨⟨x1, x2⟩, hx, rfl⟩ := ((M.htab_spec A n b).2 p).mp hp
  obtain ⟨rfl, rfl, rfl⟩ := M.triple_unique htr (M.nt3_spec x1 x2 _).2
  simp only
  cases x1 with
  | zero => exact Or.inl ⟨(M.empty_iff _).mpr rfl, (M.succ_num_iff _ _).mpr (by rw [H_zero])⟩
  | succ k =>
    cases x2 with
    | zero =>
      refine Or.inr (Or.inl ⟨M.num k, M.num_lt (by omega), (M.succ_num_iff k _).mpr rfl, (M.empty_iff _).mpr rfl, ?_⟩)
      rcases Nat.lt_trichotomy k 1 with c | c | c
      · have : k = 0 := by omega
        subst this; exact Or.inl ⟨(M.empty_iff _).mpr rfl, by rw [H_base1]⟩
      · subst c; exact Or.inr (Or.inl ⟨(M.isOne_iff _).mpr rfl, (M.empty_iff _).mpr (by rw [H_base2])⟩)
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
        refine Or.inr (Or.inr ⟨(M.num_ne_empty_one).1.mpr (by omega), fun h => absurd ((M.num_ne_empty_one).2.mp h) (by omega), ?_⟩)
        rw [show j + 2 + 1 = j + 3 by omega, H_base3]; exact (M.isOne_iff _).mpr rfl
    | succ j =>
      obtain ⟨h1, h2⟩ := needs_just A n b k j hx
      refine Or.inr (Or.inr ⟨M.num k, M.num_lt (by omega), M.num j, M.num_lt (by omega),
        (M.succ_num_iff k _).mpr rfl, (M.succ_num_iff j _).mpr rfl,
        _, M.htab_row A n b h1, M.num (Tables.H A (k + 1) j), (M.nt3_spec _ _ _).2,
        _, M.htab_row A n b h2, ?_⟩)
      simp only
      rw [H_rec]; exact (M.nt3_spec _ _ _).2

theorem hyper_iff (n A : Nat) (b c : α) (hb : 0 < n ∨ ∃ m, b = M.num m) :
    Hyper M.mem (M.num n) (M.num A) b c ↔ ∃ m, b = M.num m ∧ c = M.num (Tables.H A n m) := by
  constructor
  · rintro ⟨t, ht, p, hp, htr⟩
    exact M.hyper_sound t A ht n b c p hp htr hb
  · rintro ⟨m, rfl, rfl⟩
    exact ⟨M.htab A n m, M.htab_ok A n m, _, M.htab_row A n m (needs_head A n m), (M.nt3_spec _ _ _).2⟩

theorem op_iff (k A : Nat) (hk : 0 < k) (b c : α) :
    Op M.mem k (M.num A) b c ↔ ∃ m, b = M.num m ∧ c = M.num (Tables.H A k m) := by
  simp only [Op, M.num_iff]
  constructor
  · rintro ⟨o, rfl, h⟩; exact (M.hyper_iff k A b c (Or.inl hk)).mp h
  · intro h; exact ⟨_, rfl, (M.hyper_iff k A b c (Or.inl hk)).mpr h⟩

theorem add_iff (A m : Nat) (c : α) : Op M.mem 1 (M.num A) (M.num m) c ↔ c = M.num (A + m) := by
  rw [M.op_iff 1 A (by decide)]
  constructor
  · rintro ⟨m', e, rfl⟩; rw [M.num_inj e, Tables.H_one]
  · rintro rfl; exact ⟨m, rfl, by rw [Tables.H_one]⟩
theorem mul_iff (A m : Nat) (c : α) : Op M.mem 2 (M.num A) (M.num m) c ↔ c = M.num (A * m) := by
  rw [M.op_iff 2 A (by decide)]
  constructor
  · rintro ⟨m', e, rfl⟩; rw [M.num_inj e, Tables.H_two]
  · rintro rfl; exact ⟨m, rfl, by rw [Tables.H_two]⟩
theorem exp_iff (A m : Nat) (c : α) : Op M.mem 3 (M.num A) (M.num m) c ↔ c = M.num (A ^ m) := by
  rw [M.op_iff 3 A (by decide)]
  constructor
  · rintro ⟨m', e, rfl⟩; rw [M.num_inj e, Tables.H_three]
  · rintro rfl; exact ⟨m, rfl, by rw [Tables.H_three]⟩

/-! ### 割り切りと素数 -/

theorem divides_iff (d m : Nat) : Divides M.mem (M.num d) (M.num m) ↔ d ∣ m := by
  simp only [Divides]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨j, rfl, e⟩ := (M.op_iff 2 d (by decide) k _).mp hk
    rw [M.num_inj e, Tables.H_two]; exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨M.num j, (M.mul_iff d j _).mpr rfl⟩

theorem small_iff (n : Nat) : Small M.mem (M.num n) ↔ n = 0 ∨ n = 1 := by
  simp only [Small, M.empty_iff, M.isOne_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (M.num_inj h)
    · exact Or.inr (M.num_inj h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem prime_iff (p : Nat) : PrimeM M.mem (M.num p) ↔ Dec.Prime p := by
  simp only [PrimeM, M.small_iff]
  constructor
  · rintro ⟨_, hs, hd⟩
    refine ⟨by omega, fun d hd1 hd2 hdiv => ?_⟩
    exact hd (M.num d) (M.num_lt hd1) (by rw [M.small_iff]; omega) ((M.divides_iff d p).mpr hdiv)
  · rintro ⟨h2, hd⟩
    refine ⟨M.natM_num p, by omega, fun x hx hs hdiv => ?_⟩
    obtain ⟨d, hdp, rfl⟩ := (M.num_mem p x).mp hx
    rw [M.small_iff] at hs
    exact hd d hdp (by omega) ((M.divides_iff d p).mp hdiv)

theorem prime_num {x : α} (h : PrimeM M.mem x) : ∃ p, x = M.num p := (M.nat_iff x).mp h.1

/-! ### 素数の表 -/

theorem pt_sound (t : α) (ht : PrimeTable M.mem t) :
    ∀ i p q, M.mem q t → Pair M.mem q i p → ∃ n, i = M.num n ∧ p = M.num (Enc.np n) := by
  intro i
  induction i using M.wf.induction with
  | _ i ih =>
  intro p q hq hpair
  rcases ht q hq i p hpair with ⟨h0, h2⟩ | ⟨i1, hi1, hs, q', hq', p2, hpair2, hp2p, hprime, hgap⟩
  · refine ⟨0, (M.empty_iff i).mp h0, ?_⟩
    rw [Enc.np_zero]; exact (M.num_iff 2 p).mp h2
  · obtain ⟨n, rfl, rfl⟩ := ih i1 hi1 p2 q' hq' hpair2
    obtain ⟨P, rfl⟩ := M.prime_num hprime
    refine ⟨n + 1, (M.succ_num_iff n i).mp hs, ?_⟩
    have hlt : Enc.np n < P := (M.num_mem_iff).mp hp2p
    have hNP : Enc.NP (n + 1) P := by
      refine Enc.NP.succ (Enc.np_spec n) hlt ((M.prime_iff P).mp hprime) (fun m hm hm2 hpm => ?_)
      exact hgap (M.num m) (M.num_lt hm) (M.num_lt hm2) ((M.prime_iff m).mpr hpm)
    rw [(Enc.NP_iff _ _).mp hNP]

noncomputable def ptab (n : Nat) : α := M.set ((List.range (n + 1)).map (fun j => M.np2 j (Enc.np j)))

theorem ptab_spec (n : Nat) : M.H (M.ptab n) ∧
    ∀ q, M.mem q (M.ptab n) ↔ ∃ j, j ≤ n ∧ q = M.np2 j (Enc.np j) := by
  have := M.set_spec ((List.range (n + 1)).map (fun j => M.np2 j (Enc.np j)))
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact (M.np2_spec _ _).1)
  refine ⟨this.1, fun q => ?_⟩
  rw [ptab, this.2, List.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, by simp at hj; omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, by simp; omega, rfl⟩

theorem ptab_ok (n : Nat) : PrimeTable M.mem (M.ptab n) := by
  intro q hq i p hpair
  obtain ⟨j, hj, rfl⟩ := ((M.ptab_spec n).2 q).mp hq
  obtain ⟨rfl, rfl⟩ := M.pair_unique hpair (M.np2_spec _ _).2
  cases j with
  | zero => exact Or.inl ⟨(M.empty_iff _).mpr rfl, (M.num_iff 2 _).mpr (by rw [Enc.np_zero])⟩
  | succ j =>
    refine Or.inr ⟨M.num j, M.num_lt (by omega), (M.succ_num_iff j _).mpr rfl,
      M.np2 j (Enc.np j), ((M.ptab_spec n).2 _).mpr ⟨j, by omega, rfl⟩, M.num (Enc.np j), (M.np2_spec _ _).2,
      M.num_lt (Enc.np_lt (by omega)), (M.prime_iff _).mpr (Enc.np_prime _), ?_⟩
    intro m hm hm2 hpm
    obtain ⟨m', hm', rfl⟩ := (M.num_mem _ m).mp hm
    have hlt := (M.num_mem_iff).mp hm2
    have := Enc.np_spec (j + 1)
    cases this with
    | succ h2 _ _ hgap =>
      rw [Enc.NP_unique _ _ _ h2 (Enc.np_spec j)] at hgap
      exact hgap m' hm' hlt ((M.prime_iff m').mp hpm)

theorem nth_prime_iff (i : Nat) (p : α) : NthPrime M.mem (M.num i) p ↔ p = M.num (Enc.np i) := by
  constructor
  · rintro ⟨t, ht, q, hq, p2, hpair, rfl⟩
    obtain ⟨n, e, rfl⟩ := M.pt_sound t ht _ _ q hq hpair
    rw [M.num_inj e]
  · rintro rfl
    exact ⟨M.ptab i, M.ptab_ok i, M.np2 i (Enc.np i), ((M.ptab_spec i).2 _).mpr ⟨i, by omega, rfl⟩, _,
      (M.np2_spec _ _).2, rfl⟩

/-! ### 列 -/

/-- s は長さ n の自然数の列 f を表す：s の元はちょうど順序対 (i, f(i))（i < n）。 -/
def SeqRep (s : α) (n : Nat) (f : Nat → Nat) : Prop :=
  (∀ x, M.mem x s → ∃ i, i < n ∧ Pair M.mem x (M.num i) (M.num (f i))) ∧
    (∀ i, i < n → ∃ x, M.mem x s ∧ Pair M.mem x (M.num i) (M.num (f i)))

/-- s の元の第 1 成分がちょうど num i（i < n）。 -/
def Dom (s : α) (n : Nat) : Prop :=
  (∀ x, M.mem x s → ∃ i, i < n ∧ ∃ a, Pair M.mem x (M.num i) a) ∧
    (∀ i, i < n → ∃ x, M.mem x s ∧ ∃ a, Pair M.mem x (M.num i) a)

theorem SeqRep.dom {s : α} {n : Nat} {f : Nat → Nat} (h : M.SeqRep s n f) : M.Dom s n :=
  ⟨fun x hx => by obtain ⟨i, hi, hp⟩ := h.1 x hx; exact ⟨i, hi, _, hp⟩,
   fun i hi => by obtain ⟨x, hx, hp⟩ := h.2 i hi; exact ⟨x, hx, _, hp⟩⟩

theorem seq_lookup {s : α} {n : Nat} {f : Nat → Nat} (h : M.SeqRep s n f) {q i a : α}
    (hq : M.mem q s) (hp : Pair M.mem q i a) : ∃ j, j < n ∧ i = M.num j ∧ a = M.num (f j) := by
  obtain ⟨j, hj, hp'⟩ := h.1 q hq
  obtain ⟨e1, e2⟩ := M.pair_unique hp hp'
  exact ⟨j, hj, e1, e2⟩

theorem seqWith_dom {s h : α} {n : Nat} {V : α → Prop} (hd : M.Dom s n) (hs : SeqWith M.mem s h V) :
    h = M.num n := by
  obtain ⟨hnat, helem, htot, _⟩ := hs
  obtain ⟨m, rfl⟩ := (M.nat_iff h).mp hnat
  congr 1
  apply Nat.le_antisymm
  · refine Classical.byContradiction (fun hlt => ?_)
    obtain ⟨q, hq, a, hp⟩ := htot (M.num n) (M.num_lt (by omega))
    obtain ⟨j, hj, a', hp'⟩ := hd.1 q hq
    obtain ⟨e, _⟩ := M.pair_unique hp hp'
    rw [M.num_inj e] at hj
    omega
  · refine Classical.byContradiction (fun hlt => ?_)
    obtain ⟨x, hx, a, hp⟩ := hd.2 m (by omega)
    obtain ⟨i, a', hp', hi, _⟩ := helem x hx
    obtain ⟨e, _⟩ := M.pair_unique hp' hp
    rw [e, M.num_mem_iff] at hi
    omega

theorem seqWith_iff {s : α} {n : Nat} {f : Nat → Nat} (hr : M.SeqRep s n f) (h : α) :
    SeqWith M.mem s h (NatM M.mem) ↔ h = M.num n := by
  constructor
  · exact M.seqWith_dom hr.dom
  · rintro rfl
    refine ⟨M.natM_num n, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, hp⟩ := hr.1 x hx
      exact ⟨_, _, hp, M.num_lt hi, M.natM_num _⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := (M.num_mem n i).mp hi
      obtain ⟨x, hx, hp⟩ := hr.2 j hj
      exact ⟨x, hx, _, hp⟩
    · intro q1 hq1 i1 a1 hp1 q2 hq2 i2 a2 hp2 e
      obtain ⟨j1, _, rfl, rfl⟩ := M.seq_lookup hr hq1 hp1
      obtain ⟨j2, _, e2, rfl⟩ := M.seq_lookup hr hq2 hp2
      rw [M.num_inj (e.trans e2)]

theorem seq_extract {s : α} {n : Nat} (hs : SeqWith M.mem s (M.num n) (NatM M.mem)) : ∃ f, M.SeqRep s n f := by
  obtain ⟨_, helem, htot, hfun⟩ := hs
  have hex : ∀ i, ∃ v, i < n → ∃ x, M.mem x s ∧ Pair M.mem x (M.num i) (M.num v) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨q, hq, a, hp⟩ := htot (M.num i) (M.num_lt hi)
      obtain ⟨i', a', hp', _, ha'⟩ := helem q hq
      obtain ⟨_, e2⟩ := M.pair_unique hp hp'
      obtain ⟨v, rfl⟩ := (M.nat_iff a').mp ha'
      exact ⟨v, fun _ => ⟨q, hq, e2 ▸ hp⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  refine ⟨fun i => Classical.choose (hex i), ?_, fun i hi => Classical.choose_spec (hex i) hi⟩
  intro x hx
  obtain ⟨i, a, hp, hi, ha⟩ := helem x hx
  obtain ⟨j, hj, rfl⟩ := (M.num_mem n i).mp hi
  refine ⟨j, hj, ?_⟩
  obtain ⟨x', hx', hp'⟩ := Classical.choose_spec (hex j) hj
  have := hfun x hx _ _ hp x' hx' _ _ hp' rfl
  rw [this] at hp; exact hp

/-- 自然数の列 f の、長さ n の部分を表す集合。 -/
noncomputable def sset (n : Nat) (f : Nat → Nat) : α := M.set ((List.range n).map (fun i => M.np2 i (f i)))

theorem sset_spec (n : Nat) (f : Nat → Nat) : M.H (M.sset n f) ∧ M.SeqRep (M.sset n f) n f := by
  have := M.set_spec ((List.range n).map (fun i => M.np2 i (f i)))
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact (M.np2_spec _ _).1)
  refine ⟨this.1, ?_, ?_⟩
  · intro x hx
    rw [sset, this.2, List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, by simpa using hi, (M.np2_spec _ _).2⟩
  · intro i hi
    exact ⟨M.np2 i (f i), by rw [sset, this.2, List.mem_map]; exact ⟨i, by simpa using hi, rfl⟩, (M.np2_spec _ _).2⟩

/-! ### 積の表と Encode -/

theorem prod_sound {s : α} {n : Nat} {f : Nat → Nat} (hr : M.SeqRep s n f) (t : α) (ht : ProdTable M.mem t s) :
    ∀ k P q, M.mem q t → Pair M.mem q k P → ∃ j, k = M.num j ∧ P = M.num (Enc.prodF f j) := by
  intro k
  induction k using M.wf.induction with
  | _ k ih =>
  intro P q hq hpair
  rcases ht q hq k P hpair with ⟨h0, h1⟩ | ⟨k1, hk1, hs, q1, hq1, P1, hp1, q2, hq2, a, hp2, pr, hpr, pw, hpw, hP⟩
  · exact ⟨0, (M.empty_iff k).mp h0, (M.isOne_iff P).mp h1⟩
  · obtain ⟨j, rfl, rfl⟩ := ih k1 hk1 P1 q1 hq1 hp1
    obtain ⟨j', _, e, rfl⟩ := M.seq_lookup hr hq2 hp2
    rw [← M.num_inj e] at *
    have ek : k = M.num (j + 1) := (M.succ_num_iff j k).mp hs
    subst ek
    rw [M.nth_prime_iff] at hpr; subst hpr
    rw [M.exp_iff] at hpw; subst hpw
    rw [M.mul_iff] at hP; subst hP
    exact ⟨j + 1, rfl, rfl⟩

noncomputable def prtab (n : Nat) (f : Nat → Nat) : α :=
  M.set ((List.range (n + 1)).map (fun j => M.np2 j (Enc.prodF f j)))

theorem prtab_spec (n : Nat) (f : Nat → Nat) : M.H (M.prtab n f) ∧
    ∀ q, M.mem q (M.prtab n f) ↔ ∃ j, j ≤ n ∧ q = M.np2 j (Enc.prodF f j) := by
  have := M.set_spec ((List.range (n + 1)).map (fun j => M.np2 j (Enc.prodF f j)))
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact (M.np2_spec _ _).1)
  refine ⟨this.1, fun q => ?_⟩
  rw [prtab, this.2, List.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, by simp at hj; omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, by simp; omega, rfl⟩

theorem prtab_ok {s : α} {n : Nat} {f : Nat → Nat} (hr : M.SeqRep s n f) : ProdTable M.mem (M.prtab n f) s := by
  intro q hq k P hpair
  obtain ⟨j, hj, rfl⟩ := ((M.prtab_spec n f).2 q).mp hq
  obtain ⟨rfl, rfl⟩ := M.pair_unique hpair (M.np2_spec _ _).2
  cases j with
  | zero => exact Or.inl ⟨(M.empty_iff _).mpr rfl, (M.isOne_iff _).mpr rfl⟩
  | succ j =>
    obtain ⟨x, hx, hpx⟩ := hr.2 j (by omega)
    exact Or.inr ⟨M.num j, M.num_lt (by omega), (M.succ_num_iff j _).mpr rfl,
      M.np2 j (Enc.prodF f j), ((M.prtab_spec n f).2 _).mpr ⟨j, by omega, rfl⟩, _, (M.np2_spec _ _).2,
      x, hx, _, hpx, _, (M.nth_prime_iff _ _).mpr rfl, _, (M.exp_iff _ _ _).mpr rfl, (M.mul_iff _ _ _).mpr rfl⟩

theorem encode_iff {s : α} {n : Nat} {f : Nat → Nat} (hr : M.SeqRep s n f) (c : α) :
    EncodeM M.mem s c ↔ c = M.num (Enc.enc n f) := by
  constructor
  · rintro ⟨h, hseq, t, ht, q, hq, P, hpair, two, h2, e, he, c1, hc1, hsucc⟩
    rw [M.seqWith_iff hr] at hseq; subst hseq
    obtain ⟨j, ej, rfl⟩ := M.prod_sound hr t ht _ _ q hq hpair
    rw [← M.num_inj ej] at *
    rw [M.num_iff] at h2; subst h2
    rw [M.exp_iff] at he; subst he
    rw [M.mul_iff] at hc1; subst hc1
    obtain ⟨j', e1, rfl⟩ := M.succ_into_num hsucc
    have := Enc.enc_succ n f
    congr 1
    omega
  · rintro rfl
    have hN := Enc.enc_succ n f
    exact ⟨M.num n, (M.seqWith_iff hr _).mpr rfl, M.prtab n f, M.prtab_ok hr,
      M.np2 n (Enc.prodF f n), ((M.prtab_spec n f).2 _).mpr ⟨n, by omega, rfl⟩, _, (M.np2_spec _ _).2,
      M.num 2, (M.num_iff 2 _).mpr rfl, _, (M.exp_iff _ _ _).mpr rfl, _, (M.mul_iff _ _ _).mpr rfl,
      (M.succ_num_iff _ _).mpr (by rw [hN])⟩

/-! ### MetaCode -/

theorem pair_ext {p p' a b : α} (h : Pair M.mem p a b) (h' : Pair M.mem p' a b) : p = p' := by
  have sing_eq : ∀ s s', Sing M.mem s a → Sing M.mem s' a → s = s' := by
    intro s s' hs hs'
    apply M.ext; intro x
    constructor
    · intro hx; rw [hs.2 x hx]; exact hs'.1
    · intro hx; rw [hs'.2 x hx]; exact hs.1
  have dbl_eq : ∀ s s', Dbl M.mem s a b → Dbl M.mem s' a b → s = s' := by
    intro s s' hs hs'
    apply M.ext; intro x
    constructor
    · intro hx; rcases hs.2.2 x hx with rfl | rfl; exact hs'.1; exact hs'.2.1
    · intro hx; rcases hs'.2.2 x hx with rfl | rfl; exact hs.1; exact hs.2.1
  have sub : ∀ p p', Pair M.mem p a b → Pair M.mem p' a b → ∀ x, M.mem x p → M.mem x p' := by
    intro p p' h h' x hx
    obtain ⟨_, ⟨s1, hs1, hsing⟩, ⟨s2, hs2, hdbl⟩⟩ := h'
    rcases h.1 x hx with hx' | hx'
    · rw [sing_eq x s1 hx' hsing]; exact hs1
    · rw [dbl_eq x s2 hx' hdbl]; exact hs2
  exact M.ext p p' (fun x => ⟨sub p p' h h' x, sub p' p h' h x⟩)

theorem seqRep_ext {t t' : α} {g : Nat → Nat} {n : Nat} (h : M.SeqRep t n g) (h' : M.SeqRep t' n g) : t = t' := by
  have sub : ∀ t t', M.SeqRep t n g → M.SeqRep t' n g → ∀ x, M.mem x t → M.mem x t' := by
    intro t t' h h' x hx
    obtain ⟨i, hi, hp⟩ := h.1 x hx
    obtain ⟨x', hx', hp'⟩ := h'.2 i hi
    rw [M.pair_ext hp hp']; exact hx'
  exact M.ext t t' (fun x => ⟨sub t t' h h' x, sub t' t h' h x⟩)

theorem tuple4_iff (t : α) : Tuple4 M.mem t ↔ ∃ g, M.SeqRep t 4 g := by
  simp only [Tuple4, M.num_iff]
  constructor
  · rintro ⟨_, rfl, hs⟩; exact M.seq_extract hs
  · rintro ⟨g, hg⟩; exact ⟨_, rfl, (M.seqWith_iff hg _).mpr rfl⟩

/-- s は長さ n の記号（4 つ組）の列 S を表す：s の元はちょうど順序対 (i, t)（i < n、t は S(i) を表す集合）。 -/
def SeqRep4 (s : α) (n : Nat) (S : Nat → Nat → Nat) : Prop :=
  (∀ x, M.mem x s → ∃ i, i < n ∧ ∃ t, Pair M.mem x (M.num i) t ∧ M.SeqRep t 4 (S i)) ∧
    (∀ i, i < n → ∃ x, M.mem x s ∧ ∃ t, Pair M.mem x (M.num i) t ∧ M.SeqRep t 4 (S i))

theorem metacode_iff {s : α} {len : Nat} {S : Nat → Nat → Nat} (hr : M.SeqRep4 s len S) (nn : α) :
    MetaCodeM M.mem nn s ↔ nn = M.num (Enc.metacode len S) := by
  have hdom : M.Dom s len :=
    ⟨fun x hx => by obtain ⟨i, hi, t, hp, _⟩ := hr.1 x hx; exact ⟨i, hi, t, hp⟩,
     fun i hi => by obtain ⟨x, hx, t, hp, _⟩ := hr.2 i hi; exact ⟨x, hx, t, hp⟩⟩
  have look : ∀ q i t, M.mem q s → Pair M.mem q (M.num i) t → M.SeqRep t 4 (S i) := by
    intro q i t hq hp
    obtain ⟨i', _, t', hp', hrep⟩ := hr.1 q hq
    obtain ⟨e1, e2⟩ := M.pair_unique hp hp'
    rw [M.num_inj e1, e2]; exact hrep
  constructor
  · rintro ⟨h, hs, c, hc, hcs, hall⟩
    have eh := M.seqWith_dom hdom hs; subst eh
    obtain ⟨f, hf⟩ := M.seq_extract hcs
    rw [M.encode_iff hf] at hc; subst hc
    congr 1
    unfold Enc.metacode Enc.enc
    apply Enc.enc_congr'
    intro i hi
    obtain ⟨q, hq, t, hp, q', hq', v, hp', henc⟩ := hall (M.num i) (M.num_lt hi)
    have ht := look q i t hq hp
    rw [M.encode_iff ht] at henc; subst henc
    obtain ⟨j, _, e1, e2⟩ := M.seq_lookup hf hq' hp'
    rw [← M.num_inj e1] at e2
    exact (M.num_inj e2).symm
  · rintro rfl
    have hc := M.sset_spec len (fun i => Enc.enc 4 (S i))
    refine ⟨M.num len, ⟨M.natM_num len, ?_, ?_, ?_⟩, M.sset len (fun i => Enc.enc 4 (S i)),
      (M.encode_iff hc.2 _).mpr rfl, (M.seqWith_iff hc.2 _).mpr rfl, ?_⟩
    · intro x hx
      obtain ⟨i, hi, t, hp, hrep⟩ := hr.1 x hx
      exact ⟨_, t, hp, M.num_lt hi, (M.tuple4_iff t).mpr ⟨_, hrep⟩⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := (M.num_mem len i).mp hi
      obtain ⟨x, hx, t, hp, _⟩ := hr.2 j hj
      exact ⟨x, hx, t, hp⟩
    · intro q1 hq1 i1 a1 hp1 q2 hq2 i2 a2 hp2 e
      obtain ⟨j1, _, t1, hp1', h1⟩ := hr.1 q1 hq1
      obtain ⟨j2, _, t2, hp2', h2⟩ := hr.1 q2 hq2
      obtain ⟨e1, rfl⟩ := M.pair_unique hp1 hp1'
      obtain ⟨e2, rfl⟩ := M.pair_unique hp2 hp2'
      rw [e1, e2] at e
      rw [M.num_inj e] at h1
      exact M.seqRep_ext h1 h2
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := (M.num_mem len i).mp hi
      obtain ⟨x, hx, t, hp, hrep⟩ := hr.2 j hj
      obtain ⟨y, hy, hpy⟩ := hc.2.2 j hj
      exact ⟨x, hx, t, hp, y, hy, _, hpy, (M.encode_iff hrep _).mpr rfl⟩

/-! ### 生成プログラムの出力した式そのものについて（TrMeans の mean_X と合わせる） -/

section
variable (R : Nm → List α → Prop) (e : Nat → α)

theorem lit_nat_nat : ev M.mem R lit_nat e ↔ ∃ n, e 0 = M.num n := by
  rw [mean_nat]; exact M.nat_iff (e 0)

theorem lit_numeral2_nat : ev M.mem R lit_numeral2 e ↔ e 0 = M.num 2 := by
  rw [mean_numeral2]; exact M.num_iff 2 (e 0)

theorem lit_hyper_nat {n A b : Nat} (h0 : e 0 = M.num n) (h1 : e 1 = M.num A) (h2 : e 2 = M.num b) :
    ev M.mem R lit_hyper e ↔ e 3 = M.num (Tables.H A n b) := by
  rw [mean_hyper]
  show Hyper M.mem (e 0) (e 1) (e 2) (e 3) ↔ _
  rw [h0, h1, h2, M.hyper_iff n A _ _ (Or.inr ⟨b, rfl⟩)]
  constructor
  · rintro ⟨m, e1, h3⟩; rw [M.num_inj e1]; exact h3
  · intro h; exact ⟨b, rfl, h⟩

theorem lit_add_nat {a b : Nat} (h0 : e 0 = M.num a) (h1 : e 1 = M.num b) :
    ev M.mem R lit_add e ↔ e 2 = M.num (a + b) := by
  rw [mean_add]; show Op M.mem 1 (e 0) (e 1) (e 2) ↔ _
  rw [h0, h1]; exact M.add_iff a b (e 2)
theorem lit_mul_nat {a b : Nat} (h0 : e 0 = M.num a) (h1 : e 1 = M.num b) :
    ev M.mem R lit_mul e ↔ e 2 = M.num (a * b) := by
  rw [mean_mul]; show Op M.mem 2 (e 0) (e 1) (e 2) ↔ _
  rw [h0, h1]; exact M.mul_iff a b (e 2)
theorem lit_exp_nat {a b : Nat} (h0 : e 0 = M.num a) (h1 : e 1 = M.num b) :
    ev M.mem R lit_exp e ↔ e 2 = M.num (a ^ b) := by
  rw [mean_exp]; show Op M.mem 3 (e 0) (e 1) (e 2) ↔ _
  rw [h0, h1]; exact M.exp_iff a b (e 2)

theorem lit_divides_nat {d m : Nat} (h0 : e 0 = M.num d) (h1 : e 1 = M.num m) :
    ev M.mem R lit_divides e ↔ d ∣ m := by
  rw [mean_divides]; show Divides M.mem (e 0) (e 1) ↔ _
  rw [h0, h1]; exact M.divides_iff d m

theorem lit_prime_nat {p : Nat} (h0 : e 0 = M.num p) : ev M.mem R lit_prime e ↔ Dec.Prime p := by
  rw [mean_prime]; show PrimeM M.mem (e 0) ↔ _
  rw [h0]; exact M.prime_iff p

theorem lit_nth_prime_nat {i : Nat} (h0 : e 0 = M.num i) :
    ev M.mem R lit_nth_prime e ↔ e 1 = M.num (Enc.np i) := by
  rw [mean_nth_prime]; show NthPrime M.mem (e 0) (e 1) ↔ _
  rw [h0]; exact M.nth_prime_iff i (e 1)

theorem lit_encode_nat {n : Nat} {f : Nat → Nat} (hs : M.SeqRep (e 0) n f) :
    ev M.mem R lit_encode e ↔ e 1 = M.num (Enc.enc n f) := by
  rw [mean_encode]; exact M.encode_iff hs (e 1)

theorem lit_metacode_nat {len : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 (e 1) len S) :
    ev M.mem R lit_metacode e ↔ e 0 = M.num (Enc.metacode len S) := by
  rw [mean_metacode]; exact M.metacode_iff hs (e 0)

/-- まとめ：metacode の式が二つの記号列 S, S′ について同じ番号で成り立てば、列は一致する。 -/
theorem lit_metacode_inj {len len' : Nat} {S S' : Nat → Nat → Nat} (e' : Nat → α)
    (hs : M.SeqRep4 (e 1) len S) (hs' : M.SeqRep4 (e' 1) len' S') (he : e 0 = e' 0)
    (h : ev M.mem R lit_metacode e) (h' : ev M.mem R lit_metacode e') :
    len = len' ∧ ∀ i, i < len → ∀ j, j < 4 → S i j = S' i j := by
  rw [M.lit_metacode_nat R e hs] at h
  rw [M.lit_metacode_nat R e' hs'] at h'
  rw [h, h'] at he
  exact Enc.metacode_inj _ _ _ _ (M.num_inj he)
end

#print axioms lit_encode_nat
#print axioms lit_metacode_nat
#print axioms lit_metacode_inj
#print axioms lit_hyper_nat
#print axioms lit_nth_prime_nat

end Model
end Tr
