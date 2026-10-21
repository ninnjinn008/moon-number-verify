/-
  書き写しの検証（改訂44）：構文の層（parse.py の formula・formula₋）を、G5 の構文（G5.Form）までつなぐ。

  ・decode：4 つ組の記号 (a0, a1, a2, a3) から G5 の記号（Tok）への読み替え（本文第 2 節の記号表）。
    U = (8,2,0,1) は fn 0 1、Θ = (8,3,0,1) は fn 1 1、f_{a,i} = (8,4,i,a) は fn (i+2) a とする。
  ・str S h：長さ h の記号列 S を G5 の記号列（位置 → Option Tok）にしたもの。
  ・formula_iff：s が記号列 S を表すなら、
      FormulaM s ⟺ ∃ φ : G5.Form, φ.wf ∧ φ の記号列が str S h の 0 から始まり、長さがちょうど h。
    健全性は G5.sound、完全性は G5.parses_just による（証明書は構文木に現れる区間全体の有限集合）。
  ・formula_minus_iff：さらに Θ（fn 1 1）が現れないこと。
  ・lit_formula_nat・lit_formula_minus_nat：生成プログラムが出力した式そのものについての最終形。
-/
import TrNat
import G5
namespace Tr
open G5 (Tok Str Term Terms Form Occ termOk formOk listOk Just Parses term_head)

def punctTok : Nat → Tok
  | 0 => .bot | 1 => .imp | 2 => .neg | 3 => .ex | 4 => .lp | _ => .rp
def decode (a b c d : Nat) : Option Tok :=
  if b = 0 ∧ c = 0 ∧ d = 0 ∧ a ≤ 5 then some (punctTok a)
  else if a = 6 ∧ b = 0 ∧ d = 0 then some (.cst c)
  else if a = 7 ∧ b = 1 ∧ d = 0 then some (.var c)
  else if a = 8 ∧ b = 2 ∧ c = 0 ∧ d = 1 then some (.fn 0 1)
  else if a = 8 ∧ b = 3 ∧ c = 0 ∧ d = 1 then some (.fn 1 1)
  else if a = 8 ∧ b = 4 then some (.fn (c + 2) d)
  else if a = 9 ∧ b = 5 ∧ c = 0 ∧ d = 2 then some .elem
  else if a = 9 ∧ b = 6 then some (.rel c d)
  else none

theorem punctTok_inj {a a0 : Nat} (ha : a ≤ 5) (h0 : a0 ≤ 5) (h : punctTok a = punctTok a0) : a = a0 := by
  match a, a0, ha, h0 with
  | 0, 0, _, _ => rfl | 1, 1, _, _ => rfl | 2, 2, _, _ => rfl | 3, 3, _, _ => rfl | 4, 4, _, _ => rfl | 5, 5, _, _ => rfl
  | 0, 1, _, _ | 0, 2, _, _ | 0, 3, _, _ | 0, 4, _, _ | 0, 5, _, _ => cases h
  | 1, 0, _, _ | 1, 2, _, _ | 1, 3, _, _ | 1, 4, _, _ | 1, 5, _, _ => cases h
  | 2, 0, _, _ | 2, 1, _, _ | 2, 3, _, _ | 2, 4, _, _ | 2, 5, _, _ => cases h
  | 3, 0, _, _ | 3, 1, _, _ | 3, 2, _, _ | 3, 4, _, _ | 3, 5, _, _ => cases h
  | 4, 0, _, _ | 4, 1, _, _ | 4, 2, _, _ | 4, 3, _, _ | 4, 5, _, _ => cases h
  | 5, 0, _, _ | 5, 1, _, _ | 5, 2, _, _ | 5, 3, _, _ | 5, 4, _, _ => cases h

theorem punctTok_ne (a : Nat) : (∀ k, punctTok a ≠ .var k) ∧ (∀ k, punctTok a ≠ .cst k) ∧ (∀ f n, punctTok a ≠ .fn f n) ∧
    punctTok a ≠ .elem ∧ (∀ r n, punctTok a ≠ .rel r n) := by
  unfold punctTok; split <;> simp

theorem punctTok_ne' (a : Nat) : (∀ k, Tok.var k ≠ punctTok a) ∧ (∀ k, Tok.cst k ≠ punctTok a) ∧
    (∀ f n, Tok.fn f n ≠ punctTok a) ∧ Tok.elem ≠ punctTok a ∧ (∀ r n, Tok.rel r n ≠ punctTok a) := by
  unfold punctTok; split <;> simp

macro "dec_tac" : tactic => `(tactic| (unfold decode; repeat' split) <;> simp_all [punctTok_ne] <;> omega)

theorem dec_punct (a0 : Nat) (h0 : a0 ≤ 5) (a b c d : Nat) :
    decode a b c d = some (punctTok a0) ↔ (a = a0 ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · rename_i hc; simp at h; exact ⟨punctTok_inj hc.2.2.2 h0 h, hc.1, hc.2.1, hc.2.2.1⟩
    · repeat' (split at h)
      all_goals (simp at h; try (have := punctTok_ne a0; have := punctTok_ne' a0; simp_all))
  · rintro ⟨rfl, rfl, rfl, rfl⟩; simp [decode, h0]
theorem dec_var (a b c d k : Nat) : decode a b c d = some (.var k) ↔ (a = 7 ∧ b = 1 ∧ d = 0 ∧ c = k) := by
  constructor
  · intro h; unfold decode at h
    repeat' (split at h)
    all_goals (simp at h; try (have := punctTok_ne a; simp_all)) <;> omega
  · rintro ⟨rfl, rfl, rfl, rfl⟩; simp [decode]

macro "dec_inv" : tactic => `(tactic| (unfold decode at *; repeat' (split at *)) <;>
  (simp at *; try (have := punctTok_ne (by assumption); simp_all)))

theorem dec_cst (a b c d k : Nat) : decode a b c d = some (.cst k) ↔ (a = 6 ∧ b = 0 ∧ d = 0 ∧ c = k) := by
  constructor
  · intro h; unfold decode at h
    repeat' (split at h)
    all_goals (simp at h; try (have := punctTok_ne a; simp_all)) <;> omega
  · rintro ⟨rfl, rfl, rfl, rfl⟩; simp [decode]
theorem dec_elem (a b c d : Nat) : decode a b c d = some .elem ↔ (a = 9 ∧ b = 5 ∧ c = 0 ∧ d = 2) := by
  constructor
  · intro h; unfold decode at h
    repeat' (split at h)
    all_goals (simp at h; try (have := punctTok_ne a; simp_all)) <;> omega
  · rintro ⟨rfl, rfl, rfl, rfl⟩; simp [decode]
theorem dec_rel (a b c d r n : Nat) : decode a b c d = some (.rel r n) ↔ (a = 9 ∧ b = 6 ∧ c = r ∧ d = n) := by
  constructor
  · intro h; unfold decode at h
    repeat' (split at h)
    all_goals (simp at h; try (have := punctTok_ne a; simp_all)) <;> omega
  · rintro ⟨rfl, rfl, rfl, rfl⟩; simp [decode]
theorem dec_fn (a b c d f n : Nat) : decode a b c d = some (.fn f n) ↔
    ((a = 8 ∧ b = 2 ∧ c = 0 ∧ d = 1 ∧ f = 0 ∧ n = 1) ∨ (a = 8 ∧ b = 3 ∧ c = 0 ∧ d = 1 ∧ f = 1 ∧ n = 1) ∨
     (a = 8 ∧ b = 4 ∧ f = c + 2 ∧ n = d)) := by
  constructor
  · intro h; unfold decode at h
    repeat' (split at h)
    all_goals (simp at h; try (have := punctTok_ne a; simp_all)) <;> omega
  · rintro (⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> simp [decode]

def tok (g : Nat → Nat) : Option Tok := decode (g 0) (g 1) (g 2) (g 3)
def str (S : Nat → Nat → Nat) (h : Nat) : Str := fun n => if n < h then tok (S n) else none

theorem str_fin (S : Nat → Nat → Nat) (h : Nat) : ∀ n, h ≤ n → str S h n = none := by
  intro n hn; simp [str]; omega

theorem str_some {S : Nat → Nat → Nat} {h n : Nat} {x : Tok} : str S h n = some x ↔ n < h ∧ tok (S n) = some x := by
  unfold str; by_cases hn : n < h <;> simp [hn]

theorem tok_fn_arity {g : Nat → Nat} {f a : Nat} (h : tok g = some (.fn f a)) : a = g 3 := by
  unfold tok at h; rw [dec_fn] at h; omega
theorem tok_rel_arity {g : Nat → Nat} {r a : Nat} (h : tok g = some (.rel r a)) : a = g 3 := by
  unfold tok at h; rw [dec_rel] at h; omega

theorem terms_len_le : ∀ ts : Terms, ts.len ≤ ts.toks.length
  | .nil => by simp [G5.Terms.len, G5.Terms.toks]
  | .cons t ts => by
    obtain ⟨x, l, e, _⟩ := term_head t
    have := terms_len_le ts
    simp [G5.Terms.len, G5.Terms.toks, e]; omega

namespace Model
variable {α : Type} (M : Model α)

/-! ### 列の成分と記号 -/

theorem compIs_iff {t : α} {g : Nat → Nat} (ht : M.SeqRep t 4 g) {k : Nat} (hk : k < 4) (v : Nat) :
    CompIs M.mem t k v ↔ g k = v := by
  simp only [CompIs, M.num_iff]
  constructor
  · rintro ⟨_, rfl, q, hq, a, hp, rfl⟩
    obtain ⟨j, _, e1, e2⟩ := M.seq_lookup ht hq hp
    rw [M.num_inj e1]; exact (M.num_inj e2).symm
  · intro e
    obtain ⟨x, hx, hp⟩ := ht.2 k hk
    exact ⟨_, rfl, x, hx, _, hp, by rw [e]⟩

theorem comp_iff {t : α} {g : Nat → Nat} (ht : M.SeqRep t 4 g) {k : Nat} (hk : k < 4) (P : α → Prop) :
    Comp M.mem t k P ↔ P (M.num (g k)) := by
  simp only [Comp, M.num_iff]
  constructor
  · rintro ⟨_, rfl, q, hq, a, hp, hP⟩
    obtain ⟨j, _, e1, e2⟩ := M.seq_lookup ht hq hp
    rw [M.num_inj e1, ← e2]; exact hP
  · intro hP
    obtain ⟨x, hx, hp⟩ := ht.2 k hk
    exact ⟨_, rfl, x, hx, _, hp, hP⟩

theorem punct_iff {t : α} {g : Nat → Nat} (ht : M.SeqRep t 4 g) {a0 : Nat} (h0 : a0 ≤ 5) :
    PunctM M.mem a0 t ↔ tok g = some (punctTok a0) := by
  simp only [PunctM, M.compIs_iff ht (by decide : 0 < 4), M.compIs_iff ht (by decide : 1 < 4),
    M.compIs_iff ht (by decide : 2 < 4), M.compIs_iff ht (by decide : 3 < 4), tok, dec_punct a0 h0]
theorem var_iff {t : α} {g : Nat → Nat} (ht : M.SeqRep t 4 g) : SymVar M.mem t ↔ ∃ k, tok g = some (.var k) := by
  simp only [SymVar, M.compIs_iff ht (by decide : 0 < 4), M.compIs_iff ht (by decide : 1 < 4),
    M.compIs_iff ht (by decide : 3 < 4), tok, dec_var]
  constructor
  · rintro ⟨h0, h1, h3⟩; exact ⟨g 2, h0, h1, h3, rfl⟩
  · rintro ⟨k, h0, h1, h3, _⟩; exact ⟨h0, h1, h3⟩
theorem const_iff {t : α} {g : Nat → Nat} (ht : M.SeqRep t 4 g) : SymConst M.mem t ↔ ∃ k, tok g = some (.cst k) := by
  simp only [SymConst, M.compIs_iff ht (by decide : 0 < 4), M.compIs_iff ht (by decide : 1 < 4),
    M.compIs_iff ht (by decide : 3 < 4), tok, dec_cst]
  constructor
  · rintro ⟨h0, h1, h3⟩; exact ⟨g 2, h0, h1, h3, rfl⟩
  · rintro ⟨k, h0, h1, h3, _⟩; exact ⟨h0, h1, h3⟩
theorem func_iff {t : α} {g : Nat → Nat} (ht : M.SeqRep t 4 g) : SymFunc M.mem t ↔ ∃ f, tok g = some (.fn f (g 3)) := by
  simp only [SymFunc, M.compIs_iff ht (by decide : 0 < 4), M.compIs_iff ht (by decide : 1 < 4),
    M.compIs_iff ht (by decide : 2 < 4), M.compIs_iff ht (by decide : 3 < 4), tok, dec_fn]
  constructor
  · rintro (h | h | h)
    · exact ⟨0, Or.inl (by omega)⟩
    · exact ⟨1, Or.inr (Or.inl (by omega))⟩
    · exact ⟨g 2 + 2, Or.inr (Or.inr (by simp_all))⟩
  · rintro ⟨f, h | h | h⟩
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by simp_all))
theorem rel_iff {t : α} {g : Nat → Nat} (ht : M.SeqRep t 4 g) : SymRel M.mem t ↔ ∃ r, tok g = some (.rel r (g 3)) := by
  simp only [SymRel, M.compIs_iff ht (by decide : 0 < 4), M.compIs_iff ht (by decide : 1 < 4), tok, dec_rel]
  constructor
  · rintro ⟨h0, h1⟩; exact ⟨g 2, by simp_all⟩
  · rintro ⟨r, h0, h1, _⟩; exact ⟨h0, h1⟩
theorem elem_iff {t : α} {g : Nat → Nat} (ht : M.SeqRep t 4 g) : SymElem M.mem t ↔ tok g = some .elem := by
  simp only [SymElem, M.compIs_iff ht (by decide : 0 < 4), M.compIs_iff ht (by decide : 1 < 4),
    M.compIs_iff ht (by decide : 2 < 4), M.compIs_iff ht (by decide : 3 < 4), tok, dec_elem]
theorem theta_iff {t : α} {g : Nat → Nat} (ht : M.SeqRep t 4 g) : SymTheta M.mem t ↔ tok g = some (.fn 1 1) := by
  simp only [SymTheta, M.compIs_iff ht (by decide : 0 < 4), M.compIs_iff ht (by decide : 1 < 4),
    M.compIs_iff ht (by decide : 2 < 4), M.compIs_iff ht (by decide : 3 < 4), tok, dec_fn]
  simp only [and_true]
  constructor
  · intro h; omega
  · intro h; omega

/-! ### 列 s の i 番目 -/

section
variable {s : α} {h : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 s h S)
include hs

theorem at_num {x : α} {P : α → Prop} (ha : At M.mem s x P) : ∃ i, x = M.num i := by
  obtain ⟨q, hq, t, hp, _⟩ := ha
  obtain ⟨i, _, t', hp', _⟩ := hs.1 q hq
  exact ⟨i, (M.pair_unique hp hp').1⟩

theorem at_iff (i : Nat) (P : α → Prop) : At M.mem s (M.num i) P ↔ i < h ∧ ∃ t, M.SeqRep t 4 (S i) ∧ P t := by
  constructor
  · rintro ⟨q, hq, t, hp, hP⟩
    obtain ⟨i', hi', t', hp', hrep⟩ := hs.1 q hq
    obtain ⟨e1, rfl⟩ := M.pair_unique hp hp'
    obtain rfl := M.num_inj e1
    exact ⟨hi', t, hrep, hP⟩
  · rintro ⟨hi, t, hrep, hP⟩
    obtain ⟨x, hx, t', hp, hrep'⟩ := hs.2 i hi
    exact ⟨x, hx, t', hp, by rw [M.seqRep_ext hrep' hrep]; exact hP⟩

/-- 記号の述語 P が「その 4 つ組を decode したものが Q を満たす」と同値なら、At s i P ⟺ Q (str S h i)。 -/
theorem at_tok (i : Nat) (P : α → Prop) (Q : Option Tok → Prop)
    (hPQ : ∀ t g, M.SeqRep t 4 g → (P t ↔ Q (tok g))) (hQ : ¬ Q none) :
    At M.mem s (M.num i) P ↔ Q (str S h i) := by
  rw [M.at_iff hs]
  constructor
  · rintro ⟨hi, t, hrep, hP⟩
    simp only [str, hi, ite_true]; exact (hPQ t _ hrep).mp hP
  · intro hq
    by_cases hi : i < h
    · obtain ⟨x, _, t, _, hrep⟩ := hs.2 i hi
      simp only [str, hi, ite_true] at hq
      exact ⟨hi, t, hrep, (hPQ t _ hrep).mpr hq⟩
    · simp only [str, hi, ite_false] at hq; exact absurd hq hQ

theorem at_punct (i a0 : Nat) (h0 : a0 ≤ 5) : At M.mem s (M.num i) (PunctM M.mem a0) ↔ str S h i = some (punctTok a0) :=
  M.at_tok hs i _ (· = some (punctTok a0)) (fun t g ht => M.punct_iff ht h0) (by simp)
theorem at_elem (i : Nat) : At M.mem s (M.num i) (SymElem M.mem) ↔ str S h i = some .elem :=
  M.at_tok hs i _ (· = some .elem) (fun t g ht => M.elem_iff ht) (by simp)
theorem at_var (i : Nat) : At M.mem s (M.num i) (SymVar M.mem) ↔ ∃ k, str S h i = some (.var k) :=
  M.at_tok hs i _ (fun x => ∃ k, x = some (.var k)) (fun t g ht => M.var_iff ht) (by simp)
theorem at_theta (i : Nat) : At M.mem s (M.num i) (SymTheta M.mem) ↔ str S h i = some (.fn 1 1) :=
  M.at_tok hs i _ (· = some (.fn 1 1)) (fun t g ht => M.theta_iff ht) (by simp)
theorem at_varconst (i : Nat) : At M.mem s (M.num i) (fun t => SymVar M.mem t ∨ SymConst M.mem t) ↔
    ((∃ k, str S h i = some (.var k)) ∨ (∃ k, str S h i = some (.cst k))) :=
  M.at_tok hs i _ (fun x => (∃ k, x = some (.var k)) ∨ (∃ k, x = some (.cst k)))
    (fun t g ht => by rw [M.var_iff ht, M.const_iff ht]) (by simp)
end

/-! ### 後者・前者・+2・証明書の項目 -/

theorem nxt_iff (i : Nat) (B : α → Prop) : Nxt M.mem (M.num i) B ↔ B (M.num (i + 1)) := by
  simp only [Nxt, M.succ_num_iff]
  constructor
  · rintro ⟨_, rfl, hb⟩; exact hb
  · intro hb; exact ⟨_, rfl, hb⟩

theorem prv_iff (j : Nat) (B : α → Prop) : Prv M.mem (M.num j) B ↔ ∃ j1, j = j1 + 1 ∧ B (M.num j1) := by
  simp only [Prv]
  constructor
  · rintro ⟨x, hx, hs, hb⟩
    obtain ⟨j1, e, rfl⟩ := M.succ_into_num hs
    exact ⟨j1, e, hb⟩
  · rintro ⟨j1, rfl, hb⟩
    exact ⟨_, M.num_lt (by omega), (M.succ_num_iff j1 _).mpr rfl, hb⟩

theorem plus2_iff (n : Nat) (x : α) : Plus2 M.mem (M.num n) x ↔ x = M.num (n + 2) := by
  simp only [Plus2]
  constructor
  · rintro ⟨n1, _, h1, h2⟩
    rw [(M.succ_num_iff n n1).mp h1] at h2
    exact (M.succ_num_iff _ x).mp h2
  · rintro rfl
    exact ⟨M.num (n + 1), M.num_lt (by omega), (M.succ_num_iff n _).mpr rfl, (M.succ_num_iff _ _).mpr rfl⟩

theorem plus2_num {x : α} {k : Nat} (h : Plus2 M.mem x (M.num k)) : ∃ n, x = M.num n ∧ k = n + 2 := by
  obtain ⟨n1, _, h1, h2⟩ := h
  obtain ⟨j, e, rfl⟩ := M.succ_into_num h2
  obtain ⟨n, e2, rfl⟩ := M.succ_into_num h1
  exact ⟨n, rfl, by omega⟩

/-- 証明書 C の自然数の項目 ((i, j), k)。 -/
def Cn (C : α) (i j k : Nat) : Prop := InCert M.mem C (M.num i) (M.num j) (fun x => x = M.num k)

theorem incert_plus2 (C : α) (i j a : Nat) : InCert M.mem C (M.num i) (M.num j) (Plus2 M.mem (M.num a)) ↔ M.Cn C i j (a + 2) := by
  simp only [Cn, InCert, M.plus2_iff]

/-! ### 証明書の各条件と G5 の条件 -/

section
variable {s : α} {h : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 s h S) (C : α)
include hs

theorem argsOk_iff (i j : Nat) (ar : α → Prop) (T : Nat → Nat → Tok)
    (har : ∀ t g, M.SeqRep t 4 g → (ar t ↔ ∃ f, tok g = some (T f (g 3))))
    (harity : ∀ g f a, tok g = some (T f a) → a = g 3) :
    ArgsOk M.mem s C (M.num i) (M.num j) ar ↔
      ∃ f a j1, j = j1 + 1 ∧ str S h i = some (T f a) ∧ str S h (i + 1) = some .lp ∧ str S h j1 = some .rp ∧
        M.Cn C (i + 2) j1 (a + 2) := by
  unfold ArgsOk
  rw [M.at_tok hs i _ (fun x => ∃ f a j1, j = j1 + 1 ∧ x = some (T f a) ∧ str S h (i + 1) = some .lp ∧
        str S h j1 = some .rp ∧ M.Cn C (i + 2) j1 (a + 2))]
  · intro t g ht
    rw [M.comp_iff ht (by decide : 3 < 4), M.nxt_iff, M.nxt_iff, M.prv_iff]
    simp only [M.at_punct hs _ 4 (by decide), M.at_punct hs _ 5 (by decide), M.incert_plus2, har t g ht]
    constructor
    · rintro ⟨j1, rfl, ⟨f, hf⟩, h4, h5, hc⟩
      exact ⟨f, g 3, j1, rfl, hf, h4, h5, hc⟩
    · rintro ⟨f, a, j1, rfl, hf, h4, h5, hc⟩
      have ea := harity g f a hf
      subst ea
      exact ⟨j1, rfl, ⟨f, hf⟩, h4, h5, hc⟩
  · simp

theorem termOk_iff (i j : Nat) : TermOkM M.mem s C (M.num i) (M.num j) ↔ termOk (str S h) (M.Cn C) i j := by
  unfold TermOkM termOk
  rw [M.argsOk_iff hs C i j _ Tok.fn (fun t g ht => M.func_iff ht) (fun g f a hf => tok_fn_arity hf),
    M.at_varconst hs, M.succ_num_iff]
  constructor
  · rintro (⟨e, hv⟩ | ⟨f, a, j1, e, hf, hl, hr, hc⟩)
    · exact Or.inl ⟨M.num_inj e, hv⟩
    · exact Or.inr ⟨f, a, j1, e, hf, hl, hr, hc⟩
  · rintro (⟨rfl, hv⟩ | ⟨f, a, j1, e, hf, hl, hr, hc⟩)
    · exact Or.inl ⟨rfl, hv⟩
    · exact Or.inr ⟨f, a, j1, e, hf, hl, hr, hc⟩

theorem infix_iff (i j : Nat) (op : α → Prop) (x : Tok) (kind : Nat)
    (hop : ∀ m, At M.mem s (M.num m) op ↔ str S h m = some x) :
    Infix M.mem s C (M.num i) (M.num j) op (M.num kind) ↔
      (str S h i = some .lp ∧ ∃ j1, j = j1 + 1 ∧ str S h j1 = some .rp ∧
        ∃ m, m < j ∧ M.Cn C (i + 1) m kind ∧ str S h m = some x ∧ M.Cn C (m + 1) j1 kind) := by
  unfold Infix
  rw [M.at_punct hs i 4 (by decide), M.nxt_iff, M.prv_iff]
  simp only [M.at_punct hs _ 5 (by decide)]
  constructor
  · rintro ⟨hl, j1, rfl, hr, m, hm, hc1, hop', hn⟩
    obtain ⟨m', rfl⟩ := M.at_num hs hop'
    rw [M.nxt_iff] at hn
    exact ⟨hl, j1, rfl, hr, m', (M.num_mem_iff).mp hm, hc1, (hop m').mp hop', hn⟩
  · rintro ⟨hl, j1, rfl, hr, m, hm, hc1, hx, hc2⟩
    exact ⟨hl, j1, rfl, hr, M.num m, M.num_lt hm, hc1, (hop m).mpr hx, (M.nxt_iff m _).mpr hc2⟩

theorem formOk_iff (i j : Nat) :
    FormOkM M.mem s C (M.num 0) (M.num 1) (M.num i) (M.num j) ↔ formOk (str S h) (M.Cn C) i j := by
  unfold FormOkM formOk
  rw [M.infix_iff hs C i j _ .elem 0 (M.at_elem hs), M.infix_iff hs C i j _ .imp 1 (M.at_punct hs · 1 (by decide)),
    M.argsOk_iff hs C i j _ Tok.rel (fun t g ht => M.rel_iff ht) (fun g f a hf => tok_rel_arity hf),
    M.at_punct hs i 0 (by decide), M.at_punct hs i 2 (by decide), M.at_punct hs i 3 (by decide),
    M.succ_num_iff, M.nxt_iff, M.nxt_iff]
  simp only [M.at_var hs, M.nxt_iff, M.at_punct hs _ 4 (by decide), M.prv_iff, M.at_punct hs _ 5 (by decide)]
  have e1 : (M.num j = M.num (i + 1)) ↔ j = i + 1 := ⟨M.num_inj, fun e => by rw [e]⟩
  rw [e1]
  simp only [punctTok]
  constructor
  · rintro (h1 | h2 | h3 | h4 | ⟨hn, hc⟩ | ⟨he, hv, hl, j1, rfl, hr, hc⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hn, hc⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨he, hv, hl, j1, rfl, hr, hc⟩))))
  · rintro (h1 | h2 | h3 | h4 | ⟨hn, hc⟩ | ⟨he, hv, hl, j1, rfl, hr, hc⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hn, hc⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨he, hv, hl, j1, rfl, hr, hc⟩))))

end

theorem listOk_iff (C : α) (i j k : Nat) :
    ListOkM M.mem C (M.num 0) (M.num i) (M.num j) (M.num k) ↔ ∃ n, k = n + 2 ∧ listOk (M.Cn C) i j n := by
  unfold ListOkM listOk
  constructor
  · rintro ⟨nn1, hnn1, n, hn, hp, hcase⟩
    obtain ⟨n', rfl, rfl⟩ := M.plus2_num hp
    refine ⟨n', rfl, ?_⟩
    rcases hcase with ⟨he, hij⟩ | ⟨n0, hn0, hs0, hc⟩
    · exact Or.inl ⟨M.num_inj ((M.empty_iff _).mp he), M.num_inj hij⟩
    · obtain ⟨n0', rfl, rfl⟩ := M.succ_into_num hs0
      refine Or.inr ⟨n0', rfl, ?_⟩
      rcases hc with ⟨m, hm, hc1, hc2⟩ | ⟨hc1, hc2⟩
      · obtain ⟨m', rfl⟩ : ∃ m', m = M.num m' := by
          obtain ⟨m', _, e⟩ := (M.num_mem j m).mp hm; exact ⟨m', e⟩
        exact ⟨m', Nat.le_of_lt ((M.num_mem_iff).mp hm), hc1, (M.incert_plus2 C _ _ _).mp hc2⟩
      · exact ⟨j, Nat.le_refl _, hc1, (M.incert_plus2 C _ _ _).mp hc2⟩
  · rintro ⟨n, rfl, hl⟩
    refine ⟨M.num (n + 1), M.num_lt (by omega), M.num n, M.num_lt (by omega), (M.plus2_iff n _).mpr rfl, ?_⟩
    rcases hl with ⟨rfl, rfl⟩ | ⟨n0, rfl, m, hm, hc1, hc2⟩
    · exact Or.inl ⟨(M.empty_iff _).mpr rfl, rfl⟩
    · refine Or.inr ⟨M.num n0, M.num_lt (by omega), (M.succ_num_iff n0 _).mpr rfl, ?_⟩
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact Or.inl ⟨M.num m, M.num_lt hm, hc1, (M.incert_plus2 C _ _ _).mpr hc2⟩
      · exact Or.inr ⟨hc1, (M.incert_plus2 C _ _ _).mpr hc2⟩

/-! ### 証明書と構文木 -/

theorem SeqRep4.dom {s : α} {h : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 s h S) : M.Dom s h :=
  ⟨fun x hx => by obtain ⟨i, hi, t, hp, _⟩ := hs.1 x hx; exact ⟨i, hi, t, hp⟩,
   fun i hi => by obtain ⟨x, hx, t, hp, _⟩ := hs.2 i hi; exact ⟨x, hx, t, hp⟩⟩

theorem seqWith4 {s : α} {h : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 s h S) :
    SeqWith M.mem s (M.num h) (Tuple4 M.mem) := by
  refine ⟨M.natM_num h, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, t, hp, hrep⟩ := hs.1 x hx
    exact ⟨_, t, hp, M.num_lt hi, (M.tuple4_iff t).mpr ⟨_, hrep⟩⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := (M.num_mem h i).mp hi
    obtain ⟨x, hx, t, hp, _⟩ := hs.2 j hj
    exact ⟨x, hx, t, hp⟩
  · intro q1 hq1 i1 a1 hp1 q2 hq2 i2 a2 hp2 e
    obtain ⟨j1, _, t1, hp1', h1⟩ := hs.1 q1 hq1
    obtain ⟨j2, _, t2, hp2', h2⟩ := hs.1 q2 hq2
    obtain ⟨e1, rfl⟩ := M.pair_unique hp1 hp1'
    obtain ⟨e2, rfl⟩ := M.pair_unique hp2 hp2'
    rw [e1, e2] at e
    rw [M.num_inj e] at h1
    exact M.seqRep_ext h1 h2

section
variable {s : α} {h : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 s h S)
include hs

theorem cert_sound (C : α) (hC : CertOk M.mem s C (M.num 0) (M.num 1)) :
    ∀ i j k, M.Cn C i j k → Just (str S h) (M.Cn C) i j k := by
  intro i j k ⟨p, hp, kk, htr, hk⟩
  subst hk
  obtain ⟨i', j', k', htr', hcl⟩ := hC p hp
  obtain ⟨rfl, rfl, rfl⟩ := M.triple_unique htr' htr
  rcases hcl with ⟨e, ht⟩ | ⟨e, hf⟩ | hl
  · have := M.num_inj e; subst this
    exact (M.termOk_iff hs C i j).mp ht
  · have := M.num_inj e; subst this
    exact (M.formOk_iff hs C i j).mp hf
  · obtain ⟨n, rfl, hl'⟩ := (M.listOk_iff C i j k).mp hl
    exact hl'
end

theorem just_mono (s : Str) (C C' : Nat → Nat → Nat → Prop) (i j : Nat)
    (hm : ∀ a b c, b ≤ j → C a b c → C' a b c) : ∀ k, Just s C i j k → Just s C' i j k
  | 0, h0 => by
    simp only [Just, termOk] at h0 ⊢
    rcases h0 with h0 | ⟨f, a, j1, e, h1, h2, h3, hc⟩
    · exact Or.inl h0
    · exact Or.inr ⟨f, a, j1, e, h1, h2, h3, hm _ _ _ (by omega) hc⟩
  | 1, h0 => by
    simp only [Just, formOk] at h0 ⊢
    rcases h0 with h0 | ⟨hl, j1, e, hr, m, hmj, c1, hx, c2⟩ | ⟨r, a, j1, e, h1, h2, h3, hc⟩ |
      ⟨hl, j1, e, hr, m, hmj, c1, hx, c2⟩ | ⟨hn, hc⟩ | ⟨hx, hv, hl, j1, e, hr, hc⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨hl, j1, e, hr, m, hmj, hm _ _ _ (by omega) c1, hx, hm _ _ _ (by omega) c2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨r, a, j1, e, h1, h2, h3, hm _ _ _ (by omega) hc⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hl, j1, e, hr, m, hmj, hm _ _ _ (by omega) c1, hx, hm _ _ _ (by omega) c2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hn, hm _ _ _ (by omega) hc⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hx, hv, hl, j1, e, hr, hm _ _ _ (by omega) hc⟩))))
  | n + 2, h0 => by
    simp only [Just, listOk] at h0 ⊢
    rcases h0 with h0 | ⟨n0, e, m, hmj, c1, c2⟩
    · exact Or.inl h0
    · exact Or.inr ⟨n0, e, m, hmj, hm _ _ _ hmj c1, hm _ _ _ (Nat.le_refl _) c2⟩

/-- 本当の構文木の区間で、h を越えないもの。 -/
def PB (S : Nat → Nat → Nat) (h i j k : Nat) : Prop := Parses (str S h) i j k ∧ j ≤ h

theorem pb_just (S : Nat → Nat → Nat) (h i j k : Nat) (hp : PB S h i j k) : Just (str S h) (PB S h) i j k :=
  just_mono _ _ _ i j (fun a b c hb hc => ⟨hc, Nat.le_trans hb hp.2⟩) k (G5.parses_just (str S h) i j k hp.1)

theorem pb_bound (S : Nat → Nat → Nat) (h i j k : Nat) (hp : PB S h i j k) : i ≤ h ∧ k ≤ h + 2 := by
  obtain ⟨hpar, hj⟩ := hp
  match k, hpar with
  | 0, ⟨_, _, _, e⟩ => exact ⟨by omega, by omega⟩
  | 1, ⟨_, _, _, e⟩ => exact ⟨by omega, by omega⟩
  | n + 2, ⟨ts, _, hn, _, e⟩ =>
    have := terms_len_le ts
    exact ⟨by omega, by omega⟩

open Classical in
/-- 証明書の行の一覧。 -/
noncomputable def rows (S : Nat → Nat → Nat) (h : Nat) : List (Nat × Nat × Nat) :=
  (List.range (h + 1)).bind fun i => (List.range (h + 1)).bind fun j =>
    ((List.range (h + 3)).filter fun k => decide (PB S h i j k)).map fun k => (i, j, k)

theorem rows_mem (S : Nat → Nat → Nat) (h i j k : Nat) : (i, j, k) ∈ rows S h ↔ PB S h i j k := by
  simp only [rows, List.mem_bind, List.mem_range, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨i', _, j', _, k', ⟨_, hp⟩, e⟩
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact hp
  · intro hp
    have hb := pb_bound S h i j k hp
    exact ⟨i, by omega, j, by have := hp.2; omega, k, ⟨by omega, hp⟩, rfl⟩

noncomputable def ctab (S : Nat → Nat → Nat) (h : Nat) : α :=
  M.set ((rows S h).map fun x => M.nt3 x.1 x.2.1 x.2.2)

theorem ctab_mem (S : Nat → Nat → Nat) (h : Nat) (p : α) :
    M.mem p (M.ctab S h) ↔ ∃ i j k, PB S h i j k ∧ p = M.nt3 i j k := by
  have := M.set_spec ((rows S h).map fun x => M.nt3 x.1 x.2.1 x.2.2)
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact (M.nt3_spec _ _ _).1)
  rw [ctab, this.2, List.mem_map]
  constructor
  · rintro ⟨⟨i, j, k⟩, hx, rfl⟩; exact ⟨i, j, k, (rows_mem S h i j k).mp hx, rfl⟩
  · rintro ⟨i, j, k, hp, rfl⟩; exact ⟨(i, j, k), (rows_mem S h i j k).mpr hp, rfl⟩

theorem cn_ctab (S : Nat → Nat → Nat) (h i j k : Nat) : M.Cn (M.ctab S h) i j k ↔ PB S h i j k := by
  constructor
  · rintro ⟨p, hp, kk, htr, rfl⟩
    obtain ⟨a, b, c, hpb, rfl⟩ := (M.ctab_mem S h p).mp hp
    obtain ⟨e1, e2, e3⟩ := M.triple_unique htr (M.nt3_spec a b c).2
    rw [M.num_inj e1, M.num_inj e2, M.num_inj e3]; exact hpb
  · intro hp
    exact ⟨M.nt3 i j k, (M.ctab_mem S h _).mpr ⟨i, j, k, hp, rfl⟩, M.num k, (M.nt3_spec i j k).2, rfl⟩

section
variable {s : α} {h : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 s h S)
include hs

theorem ctab_ok : CertOk M.mem s (M.ctab S h) (M.num 0) (M.num 1) := by
  intro p hp
  obtain ⟨i, j, k, hpb, rfl⟩ := (M.ctab_mem S h p).mp hp
  refine ⟨M.num i, M.num j, M.num k, (M.nt3_spec i j k).2, ?_⟩
  have hj : Just (str S h) (M.Cn (M.ctab S h)) i j k :=
    just_mono _ _ _ i j (fun a b c _ hc => (M.cn_ctab S h a b c).mpr hc) k (pb_just S h i j k hpb)
  match k, hj with
  | 0, hj => exact Or.inl ⟨rfl, (M.termOk_iff hs _ i j).mpr hj⟩
  | 1, hj => exact Or.inr (Or.inl ⟨rfl, (M.formOk_iff hs _ i j).mpr hj⟩)
  | n + 2, hj => exact Or.inr (Or.inr ((M.listOk_iff _ i j (n + 2)).mpr ⟨n, rfl, hj⟩))

/-- 構文の層の主定理：s が長さ h の記号列 S を表すなら、Formula(s) ⟺ S が G5 の論理式の記号列。 -/
theorem formula_iff : FormulaM M.mem s ↔ ∃ φ : Form, φ.wf ∧ Occ (str S h) 0 φ.toks ∧ h = φ.toks.length := by
  constructor
  · rintro ⟨K0, he, K1, hs1, h', hsw, C, hroot, hC⟩
    rw [M.empty_iff] at he; subst he
    rw [M.succ_num_iff] at hs1; subst hs1
    have eh := M.seqWith_dom (SeqRep4.dom M hs) hsw; subst eh
    have := G5.sound (str S h) (M.Cn C) h (str_fin S h) (M.cert_sound hs C hC) h 1 0 hroot
    obtain ⟨φ, hw, ho, e⟩ := this
    exact ⟨φ, hw, ho, by omega⟩
  · rintro ⟨φ, hw, ho, hl⟩
    have hpb : PB S h 0 h 1 := ⟨⟨φ, hw, ho, by omega⟩, Nat.le_refl _⟩
    exact ⟨M.num 0, (M.empty_iff _).mpr rfl, M.num 1, (M.succ_num_iff 0 _).mpr rfl, M.num h, M.seqWith4 hs,
      M.ctab S h, (M.cn_ctab S h 0 h 1).mpr hpb, M.ctab_ok hs⟩

theorem no_theta_iff (h' : α) (eh : h' = M.num h) :
    (¬ ∃ w, M.mem w h' ∧ At M.mem s w (SymTheta M.mem)) ↔ ∀ n, n < h → str S h n ≠ some (.fn 1 1) := by
  subst eh
  constructor
  · intro hno n hn hx
    exact hno ⟨M.num n, M.num_lt hn, (M.at_theta hs n).mpr hx⟩
  · rintro hall ⟨w, hw, hat⟩
    obtain ⟨n, hn, rfl⟩ := (M.num_mem h w).mp hw
    exact hall n hn ((M.at_theta hs n).mp hat)

theorem formula_minus_iff : FormulaMinusM M.mem s ↔
    (∃ φ : Form, φ.wf ∧ Occ (str S h) 0 φ.toks ∧ h = φ.toks.length) ∧ ∀ n, n < h → str S h n ≠ some (.fn 1 1) := by
  rw [← M.formula_iff hs]
  constructor
  · rintro ⟨K0, he, K1, hs1, h', ⟨hsw, C, hroot, hC⟩, hno⟩
    have eh := M.seqWith_dom (SeqRep4.dom M hs) hsw
    exact ⟨⟨K0, he, K1, hs1, h', hsw, C, hroot, hC⟩, (M.no_theta_iff hs h' eh).mp hno⟩
  · rintro ⟨⟨K0, he, K1, hs1, h', hsw, C, hroot, hC⟩, hall⟩
    have eh := M.seqWith_dom (SeqRep4.dom M hs) hsw
    exact ⟨K0, he, K1, hs1, h', ⟨hsw, C, hroot, hC⟩, (M.no_theta_iff hs h' eh).mpr hall⟩

end

/-! ### 生成プログラムの出力した式そのものについて -/

theorem lit_formula_nat (R : Nm → List α → Prop) (e : Nat → α) {h : Nat} {S : Nat → Nat → Nat}
    (hs : M.SeqRep4 (e 0) h S) :
    ev M.mem R lit_formula e ↔ ∃ φ : Form, φ.wf ∧ Occ (str S h) 0 φ.toks ∧ h = φ.toks.length := by
  rw [mean_formula]; exact M.formula_iff hs

theorem lit_formula_minus_nat (R : Nm → List α → Prop) (e : Nat → α) {h : Nat} {S : Nat → Nat → Nat}
    (hs : M.SeqRep4 (e 0) h S) :
    ev M.mem R lit_formula_minus e ↔
      (∃ φ : Form, φ.wf ∧ Occ (str S h) 0 φ.toks ∧ h = φ.toks.length) ∧ ∀ n, n < h → str S h n ≠ some (.fn 1 1) := by
  rw [mean_formula_minus]; exact M.formula_minus_iff hs

#print axioms lit_formula_nat
#print axioms lit_formula_minus_nat

end Model
end Tr
