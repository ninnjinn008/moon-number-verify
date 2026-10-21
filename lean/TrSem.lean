/-
  書き写しの検証（改訂45）：充足関係の層（semantics.py の sat）を、G5 の Tarski の意味論までつなぐ。

  ・構造：集合 dom, E, Cn, Fn, Rel が G5 の構造 M5（領域は dom の元）を表すこと（hE・hCn・hFn・hRel）。
  ・項の列：集合 w が dom の元の列 l を表す（RepL）。割当て：σ を s に現れる変数の上に制限した集合 sgOf σ。
  ・sat_iff：s が論理式 φ を表すとき、sat(s, dom, E, Cn, Fn, Rel, sgOf σ) ⟺ φ.sat M5 σ（Tarski）。
-/
import TrSyn
namespace Tr
open G5 (Tok Str Term Terms Form Occ termOk formOk listOk Just Parses term_head)

theorem terms_eval_length {β : Type} (M5 : G5.Model β) (σ : Nat → β) :
    ∀ ts : Terms, (G5.Terms.eval M5 σ ts).length = ts.len
  | .nil => rfl
  | .cons _ ts => by simp [G5.Terms.eval, G5.Terms.len, terms_eval_length M5 σ ts]

namespace Model
variable {α : Type} (M : Model α)

/-! ### 項の値の列 -/

/-- 集合 w は列 l を表す：w の元はちょうど順序対 (i, l[i])。 -/
def RepL (w : α) (l : List α) : Prop :=
  (∀ x, M.mem x w → ∃ i a, l.get? i = some a ∧ Pair M.mem x (M.num i) a) ∧
  (∀ i a, l.get? i = some a → ∃ x, M.mem x w ∧ Pair M.mem x (M.num i) a)

theorem repL_nil (w : α) : M.RepL w [] ↔ Empty M.mem w := by
  constructor
  · rintro ⟨h1, _⟩ x hx
    obtain ⟨i, a, h, _⟩ := h1 x hx
    simp at h
  · intro he
    exact ⟨fun x hx => absurd hx (he x), fun i a h => by simp at h⟩

theorem repL_unique {w : α} : ∀ {l l' : List α}, M.RepL w l → M.RepL w l' → l = l' := by
  have key : ∀ {l l' : List α}, M.RepL w l → M.RepL w l' → ∀ i a, l.get? i = some a → l'.get? i = some a := by
    intro l l' h h' i a hi
    obtain ⟨x, hx, hp⟩ := h.2 i a hi
    obtain ⟨j, b, hj, hp'⟩ := h'.1 x hx
    obtain ⟨e1, e2⟩ := M.pair_unique hp hp'
    rw [M.num_inj e1, e2]; exact hj
  intro l l' h h'
  apply List.ext_get?
  intro i
  cases hl : l.get? i with
  | none =>
    cases hl' : l'.get? i with
    | none => rfl
    | some b => have := key h' h i b hl'; rw [hl] at this; cases this
  | some a => exact (key h h' i a hl).symm

theorem cons_rep {v w2 w : α} {l : List α} (hc : ConsM M.mem v w2 w) (hr : M.RepL w2 l) : M.RepL w (v :: l) := by
  obtain ⟨⟨z, hz, q0, hq0, hp0⟩, hall, hback⟩ := hc
  rw [M.empty_iff] at hz; subst hz
  constructor
  · intro x hx
    obtain ⟨k, y, hp, hcase⟩ := hall x hx
    rcases hcase with ⟨hk, rfl⟩ | ⟨k0, hk0, hs, q, hq, hpq⟩
    · rw [M.empty_iff] at hk; subst hk
      exact ⟨0, y, rfl, hp⟩
    · obtain ⟨i, b, hb, hpb⟩ := hr.1 q hq
      obtain ⟨e1, rfl⟩ := M.pair_unique hpq hpb
      subst e1
      rw [M.succ_num_iff] at hs; subst hs
      exact ⟨i + 1, y, by simpa using hb, hp⟩
  · intro i a hi
    cases i with
    | zero =>
      simp at hi; subst hi
      exact ⟨q0, hq0, hp0⟩
    | succ i =>
      rw [List.get?_cons_succ] at hi
      obtain ⟨q, hq, hpq⟩ := hr.2 i a hi
      obtain ⟨k0, x, hp, hn⟩ := hback q hq
      obtain ⟨e1, rfl⟩ := M.pair_unique hp hpq
      subst e1
      rw [M.nxt_iff] at hn
      obtain ⟨y, hy, hpy⟩ := hn
      exact ⟨y, hy, hpy⟩

theorem cons_inv {v w2 w x : α} {l : List α} (hc : ConsM M.mem v w2 w) (hr : M.RepL w (x :: l)) :
    v = x ∧ M.RepL w2 l := by
  obtain ⟨⟨z, hz, q0, hq0, hp0⟩, hall, hback⟩ := hc
  rw [M.empty_iff] at hz; subst hz
  constructor
  · obtain ⟨i, a, hi, hp⟩ := hr.1 q0 hq0
    obtain ⟨e1, e2⟩ := M.pair_unique hp0 hp
    rw [← M.num_inj e1] at hi; simp at hi
    rw [e2, hi]
  · constructor
    · intro q hq
      obtain ⟨k0, y, hp, k, hs, q1, hq1, hp1⟩ := hback q hq
      obtain ⟨i, a, hi, hpa⟩ := hr.1 q1 hq1
      obtain ⟨e1, rfl⟩ := M.pair_unique hp1 hpa
      subst e1
      obtain ⟨j, rfl, rfl⟩ := M.succ_into_num hs
      exact ⟨j, y, by simpa using hi, hp⟩
    · intro i a hi
      obtain ⟨x1, hx1, hp1⟩ := hr.2 (i + 1) a (by simpa using hi)
      obtain ⟨k, y, hp, hcase⟩ := hall x1 hx1
      obtain ⟨rfl, rfl⟩ := M.pair_unique hp hp1
      rcases hcase with ⟨hk, _⟩ | ⟨k0, _, hs, q, hq, hpq⟩
      · rw [M.empty_iff] at hk; exact absurd (M.num_inj hk) (by omega)
      · obtain ⟨j, e, rfl⟩ := M.succ_into_num hs
        have : j = i := by omega
        subst this
        exact ⟨q, hq, hpq⟩

/-! ### 変数の集合 Ns と割当て -/

def varOf : Option Tok → Option Nat
  | some (.var k) => some k
  | _ => none

theorem varOf_eq (x : Option Tok) (k : Nat) : varOf x = some k ↔ x = some (.var k) := by
  unfold varOf; split <;> simp_all

/-- 記号列 S（長さ h）に現れる変数の添字。 -/
def NsL (S : Nat → Nat → Nat) (h : Nat) : List Nat := (List.range h).filterMap fun p => varOf (tok (S p))

theorem mem_NsL (S : Nat → Nat → Nat) (h k : Nat) : k ∈ NsL S h ↔ ∃ p, p < h ∧ tok (S p) = some (.var k) := by
  simp only [NsL, List.mem_filterMap, List.mem_range, varOf_eq]

theorem tok_var_idx {g : Nat → Nat} {k : Nat} (h : tok g = some (.var k)) : g 2 = k := by
  unfold tok at h; rw [dec_var] at h; exact h.2.2.2

section
variable {s : α} {h : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 s h S)
include hs

theorem varset_iff (Ns : α) :
    VarSet M.mem s (M.num h) Ns ↔ ∀ x, M.mem x Ns ↔ ∃ k, k ∈ NsL S h ∧ x = M.num k := by
  constructor
  · rintro ⟨h1, h2⟩ x
    constructor
    · intro hx
      obtain ⟨p, hp, hat⟩ := h1 x hx
      obtain ⟨p', hp', rfl⟩ := (M.num_mem h p).mp hp
      obtain ⟨_, t, ht, hv, hc⟩ := (M.at_iff hs p' _).mp hat
      obtain ⟨kk, hkk⟩ := (M.var_iff ht).mp hv
      rw [M.comp_iff ht (by decide)] at hc
      rw [tok_var_idx hkk] at hc
      exact ⟨kk, (mem_NsL S h kk).mpr ⟨p', hp', hkk⟩, hc.symm⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨p, hp, htok⟩ := (mem_NsL S h k).mp hk
      obtain ⟨_, t, ht, himp⟩ := (M.at_iff hs p _).mp (h2 (M.num p) (M.num_lt hp))
      have := himp ((M.var_iff ht).mpr ⟨k, htok⟩)
      rw [M.comp_iff ht (by decide), tok_var_idx htok] at this
      exact this
  · intro hNs
    constructor
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := (hNs x).mp hx
      obtain ⟨p, hp, htok⟩ := (mem_NsL S h k).mp hk
      obtain ⟨q, hq, t, hpq, ht⟩ := hs.2 p hp
      refine ⟨M.num p, M.num_lt hp, (M.at_iff hs p _).mpr ⟨hp, t, ht, (M.var_iff ht).mpr ⟨k, htok⟩, ?_⟩⟩
      rw [M.comp_iff ht (by decide), tok_var_idx htok]
    · intro p hp
      obtain ⟨p', hp', rfl⟩ := (M.num_mem h p).mp hp
      obtain ⟨q, hq, t, hpq, ht⟩ := hs.2 p' hp'
      refine (M.at_iff hs p' _).mpr ⟨hp', t, ht, fun hv => ?_⟩
      obtain ⟨kk, hkk⟩ := (M.var_iff ht).mp hv
      rw [M.comp_iff ht (by decide), tok_var_idx hkk]
      exact (hNs _).mpr ⟨kk, (mem_NsL S h kk).mpr ⟨p', hp', hkk⟩, rfl⟩
end

/-- 割当て τ の、s に現れる変数への制限（順序対 (k, τ k) の集合）。 -/
noncomputable def sgOf (L : List Nat) (τ : Nat → α) : α := M.set (L.map fun k => M.pr (M.num k) (τ k))

theorem sgOf_spec (L : List Nat) (τ : Nat → α) (hτ : ∀ k, M.H (τ k)) :
    ∀ q, M.mem q (M.sgOf L τ) ↔ ∃ k, k ∈ L ∧ q = M.pr (M.num k) (τ k) := by
  have := M.set_spec (L.map fun k => M.pr (M.num k) (τ k))
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨k, _, rfl⟩ := hx; exact (M.pr_spec (M.H_num k) (hτ k)).1)
  intro q
  rw [sgOf, this.2, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

section
variable (L : List Nat) (τ : Nat → α) (hτ : ∀ k, M.H (τ k))
include hτ

theorem sgOf_pair {q i a : α} (hq : M.mem q (M.sgOf L τ)) (hp : Pair M.mem q i a) :
    ∃ k, k ∈ L ∧ i = M.num k ∧ a = τ k := by
  obtain ⟨k, hk, rfl⟩ := (M.sgOf_spec L τ hτ q).mp hq
  obtain ⟨e1, e2⟩ := M.pair_unique hp (M.pr_spec (M.H_num k) (hτ k)).2
  exact ⟨k, hk, e1, e2⟩

theorem at_sgOf (k : Nat) (hk : k ∈ L) (P : α → Prop) : At M.mem (M.sgOf L τ) (M.num k) P ↔ P (τ k) := by
  constructor
  · rintro ⟨q, hq, a, hp, hP⟩
    obtain ⟨k', _, e1, rfl⟩ := M.sgOf_pair L τ hτ hq hp
    rw [M.num_inj e1]; exact hP
  · intro hP
    exact ⟨_, (M.sgOf_spec L τ hτ _).mpr ⟨k, hk, rfl⟩, τ k, (M.pr_spec (M.H_num k) (hτ k)).2, hP⟩

theorem assign_sgOf (Ns dom : α) (hNs : ∀ x, M.mem x Ns ↔ ∃ k, k ∈ L ∧ x = M.num k) (hd : ∀ k, M.mem (τ k) dom) :
    AssignM M.mem Ns dom (M.sgOf L τ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := (M.sgOf_spec L τ hτ q).mp hq
    exact ⟨_, _, (M.pr_spec (M.H_num k) (hτ k)).2, (hNs _).mpr ⟨k, hk, rfl⟩, hd k⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := (hNs x).mp hx
    exact ⟨_, (M.sgOf_spec L τ hτ _).mpr ⟨k, hk, rfl⟩, τ k, (M.pr_spec (M.H_num k) (hτ k)).2⟩
  · intro q1 hq1 i1 a1 hp1 q2 hq2 i2 a2 hp2 e
    obtain ⟨k1, _, rfl, rfl⟩ := M.sgOf_pair L τ hτ hq1 hp1
    obtain ⟨k2, _, e2, rfl⟩ := M.sgOf_pair L τ hτ hq2 hp2
    rw [M.num_inj (e.trans e2)]
end

theorem assign_func {Ns dom sg : α} (ha : AssignM M.mem Ns dom sg) {q1 q2 k a1 a2 : α}
    (hq1 : M.mem q1 sg) (hp1 : Pair M.mem q1 k a1) (hq2 : M.mem q2 sg) (hp2 : Pair M.mem q2 k a2) : a1 = a2 :=
  ha.2.2 q1 hq1 _ _ hp1 q2 hq2 _ _ hp2 rfl

/-- 割当ての更新：sgOf τ の k を a に替えたものは sgOf (upd τ k a)。 -/
theorem update_sgOf (L : List Nat) (τ : Nat → α) (hτ : ∀ k, M.H (τ k)) (Ns dom : α)
    (hNs : ∀ x, M.mem x Ns ↔ ∃ k, k ∈ L ∧ x = M.num k) (hd : ∀ k, M.mem (τ k) dom)
    (k : Nat) (hk : k ∈ L) (a sg2 : α) (ha : M.mem a dom) (haH : M.H a) :
    UpdateM M.mem Ns dom (M.sgOf L τ) (M.num k) a sg2 ↔ sg2 = M.sgOf L (Tr.upd τ k a) := by
  have hτ' : ∀ k', M.H (Tr.upd τ k a k') := by
    intro k'; unfold Tr.upd; split; exact haH; exact hτ k'
  have hd' : ∀ k', M.mem (Tr.upd τ k a k') dom := by
    intro k'; unfold Tr.upd; split; exact ha; exact hd k'
  have upd_ne : ∀ k', k' ≠ k → Tr.upd τ k a k' = τ k' := by intro k' h; simp [Tr.upd, h]
  have upd_eq : Tr.upd τ k a k = a := by simp [Tr.upd]
  constructor
  · rintro ⟨hA, hat, hrest⟩
    have val : ∀ q, M.mem q sg2 → ∀ k' b, Pair M.mem q (M.num k') b → k' ∈ L → b = Tr.upd τ k a k' := by
      intro q hq k' b hp hk'
      by_cases e : k' = k
      · subst e
        obtain ⟨q', hq', b', hp', rfl⟩ := hat
        rw [upd_eq]; exact M.assign_func hA hq hp hq' hp'
      · have hq0 := (M.sgOf_spec L τ hτ _).mpr ⟨k', hk', rfl⟩
        rcases hrest _ hq0 _ _ (M.pr_spec (M.H_num k') (hτ k')).2 with e2 | ⟨q', hq', b', hp', rfl⟩
        · exact absurd (M.num_inj e2) e
        · rw [upd_ne k' e]; exact M.assign_func hA hq hp hq' hp'
    apply M.ext
    intro q
    rw [M.sgOf_spec L _ hτ']
    constructor
    · intro hq
      obtain ⟨kk, b, hp, hkk, _⟩ := hA.1 q hq
      obtain ⟨k', hk', rfl⟩ := (hNs kk).mp hkk
      have := val q hq k' b hp hk'
      subst this
      exact ⟨k', hk', M.pair_ext hp (M.pr_spec (M.H_num k') (hτ' k')).2⟩
    · rintro ⟨k', hk', rfl⟩
      obtain ⟨q', hq', b, hp⟩ := hA.2.1 (M.num k') ((hNs _).mpr ⟨k', hk', rfl⟩)
      have := val q' hq' k' b hp hk'
      subst this
      rw [← M.pair_ext hp (M.pr_spec (M.H_num k') (hτ' k')).2]; exact hq'
  · rintro rfl
    refine ⟨M.assign_sgOf L _ hτ' Ns dom hNs hd', (M.at_sgOf L _ hτ' k hk _).mpr upd_eq, ?_⟩
    intro q hq k1 b1 hp
    obtain ⟨k', hk', rfl, rfl⟩ := M.sgOf_pair L τ hτ hq hp
    by_cases e : k' = k
    · exact Or.inl (by rw [e])
    · exact Or.inr ((M.at_sgOf L _ hτ' k' hk' _).mpr (upd_ne k' e))

/-! ### TV の参照 -/

theorem tv_split (TV i j : α) (kp : α → Prop) (sg : α) (vp : α → Prop) :
    Tv M.mem TV i j kp sg vp ↔ ∃ v, Tv M.mem TV i j kp sg (fun x => x = v) ∧ vp v := by
  constructor
  · rintro ⟨e, he, a, b, hp, hk, sg2, v, hb, hsg, hv⟩
    exact ⟨v, ⟨e, he, a, b, hp, hk, sg2, v, hb, hsg, rfl⟩, hv⟩
  · rintro ⟨v, ⟨e, he, a, b, hp, hk, sg2, v', hb, hsg, rfl⟩, hv⟩
    exact ⟨e, he, a, b, hp, hk, sg2, v', hb, hsg, hv⟩

theorem tv_kp (TV i j : α) {kp kp' : α → Prop} (hk : ∀ k, kp k ↔ kp' k) (sg : α) (vp : α → Prop) :
    Tv M.mem TV i j kp sg vp ↔ Tv M.mem TV i j kp' sg vp := by
  simp only [Tv, hk]

theorem tvall_val {TV i j : α} {kp : α → Prop} {sg v : α} {vp : α → Prop}
    (h1 : Tv M.mem TV i j kp sg (fun x => x = v)) (h2 : TvAll M.mem TV i j kp sg vp) : vp v := by
  obtain ⟨e, he, a, b, hp, ⟨ij, k, ha, hij, hk⟩, sg2, v', hb, rfl, rfl⟩ := h1
  obtain ⟨a', b', hp', himp⟩ := h2 e he
  obtain ⟨rfl, rfl⟩ := M.pair_unique hp hp'
  obtain ⟨sg3, v'', hb', hv⟩ := himp ⟨ij, k, ha, hij, hk⟩
  obtain ⟨rfl, rfl⟩ := M.pair_unique hb hb'
  exact hv rfl

theorem plus2_kp (a : Nat) : ∀ k, Plus2 M.mem (M.num a) k ↔ k = M.num (a + 2) := M.plus2_iff a

/-! ### 健全性：sat が成り立てば、G5 の表の条件が成り立つ -/

/-- 集合 dom, E, Cn, Fn, Rel が G5 の構造 M5（領域は dom の元）を表すこと。 -/
structure Rep5 (dom E Cn Fn Rel : α) (M5 : G5.Model {x // M.mem x dom}) : Prop where
  domH : ∀ x, M.mem x dom → M.H x
  hE : ∀ a b : {x // M.mem x dom}, InPair M.mem E a.1 b.1 ↔ M5.E a b
  hCn : ∀ t g k, M.SeqRep t 4 g → tok g = some (.cst k) → ∀ v, InPair M.mem Cn t v ↔ v = (M5.Cn k).1
  hFn : ∀ t g f a, M.SeqRep t 4 g → tok g = some (.fn f a) → ∀ w (ws : List {x // M.mem x dom}),
      ws.length = a → M.RepL w (ws.map Subtype.val) → ∀ v, InTriple M.mem Fn t w v ↔ v = (M5.Fn f a ws).1
  hFnd : ∀ t w v, InTriple M.mem Fn t w v → M.mem v dom
  hRel : ∀ t g r a, M.SeqRep t 4 g → tok g = some (.rel r a) → ∀ w (ws : List {x // M.mem x dom}),
      ws.length = a → M.RepL w (ws.map Subtype.val) → (InPair M.mem Rel t w ↔ M5.Rel r a ws)

/-- Rep5 を、式 s（長さ h、記号 S）に現れる記号に限って要求する形（改訂48）。
    定数・関数・関係記号を含まない式（lorder.py の純粋な式）では Cn = Fn = Rel = ∅ でよい。 -/
structure Rep5T (dom E Cn Fn Rel : α) (M5 : G5.Model {x // M.mem x dom}) (S : Nat → Nat → Nat) (h : Nat) : Prop where
  domH : ∀ x, M.mem x dom → M.H x
  hE : ∀ a b : {x // M.mem x dom}, InPair M.mem E a.1 b.1 ↔ M5.E a b
  hCn : ∀ t g k, (∃ i, i < h ∧ g = S i) → M.SeqRep t 4 g → tok g = some (.cst k) → ∀ v,
      InPair M.mem Cn t v ↔ v = (M5.Cn k).1
  hFn : ∀ t g f a, (∃ i, i < h ∧ g = S i) → M.SeqRep t 4 g → tok g = some (.fn f a) →
      ∀ w (ws : List {x // M.mem x dom}),
      ws.length = a → M.RepL w (ws.map Subtype.val) → ∀ v, InTriple M.mem Fn t w v ↔ v = (M5.Fn f a ws).1
  hFnd : ∀ t w v, InTriple M.mem Fn t w v → M.mem v dom
  hRel : ∀ t g r a, (∃ i, i < h ∧ g = S i) → M.SeqRep t 4 g → tok g = some (.rel r a) →
      ∀ w (ws : List {x // M.mem x dom}),
      ws.length = a → M.RepL w (ws.map Subtype.val) → (InPair M.mem Rel t w ↔ M5.Rel r a ws)

theorem Rep5.toT {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}} (R : M.Rep5 dom E Cn Fn Rel M5)
    (S : Nat → Nat → Nat) (h : Nat) : M.Rep5T dom E Cn Fn Rel M5 S h :=
  ⟨R.domH, R.hE, fun t g k _ => R.hCn t g k, fun t g f a _ => R.hFn t g f a, R.hFnd,
    fun t g r a _ => R.hRel t g r a⟩

section Sound
variable {dom : α}

/-- G5 の割当て τ に対応する集合。 -/
noncomputable def sgT (S : Nat → Nat → Nat) (h : Nat) (τ : Nat → {x // M.mem x dom}) : α :=
  M.sgOf (NsL S h) (fun k => (τ k).1)

/-- G5 の表。 -/
noncomputable def TVt5 (S : Nat → Nat → Nat) (h : Nat) (TV : α) (i j : Nat) (τ : Nat → {x // M.mem x dom})
    (v : {x // M.mem x dom}) : Prop :=
  Tv M.mem TV (M.num i) (M.num j) (fun k => k = M.num 0) (M.sgT S h τ) (fun x => x = v.1)
noncomputable def TVl5 (S : Nat → Nat → Nat) (h : Nat) (TV : α) (i j n : Nat) (τ : Nat → {x // M.mem x dom})
    (ws : List {x // M.mem x dom}) : Prop :=
  ∃ w, Tv M.mem TV (M.num i) (M.num j) (fun k => k = M.num (n + 2)) (M.sgT S h τ) (fun x => x = w) ∧
    M.RepL w (ws.map Subtype.val)
noncomputable def S5 (S : Nat → Nat → Nat) (h : Nat) (SS : α) (i j : Nat) (τ : Nat → {x // M.mem x dom}) : Prop :=
  InS M.mem SS (M.num i) (M.num j) (M.sgT S h τ)

end Sound

theorem at_tok2 {s : α} {h : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 s h S)
    (i : Nat) (P : α → Prop) (Q : Option Tok → Prop)
    (hPQ : ∀ t, M.SeqRep t 4 (S i) → i < h → (P t ↔ Q (tok (S i)))) (hQ : ¬ Q none) :
    At M.mem s (M.num i) P ↔ Q (str S h i) := by
  rw [M.at_iff hs]
  constructor
  · rintro ⟨hi, t, hrep, hP⟩
    simp only [str, hi, ite_true]; exact (hPQ t hrep hi).mp hP
  · intro hq
    by_cases hi : i < h
    · obtain ⟨x, _, t, _, hrep⟩ := hs.2 i hi
      simp only [str, hi, ite_true] at hq
      exact ⟨hi, t, hrep, (hPQ t hrep hi).mpr hq⟩
    · simp only [str, hi, ite_false] at hq; exact absurd hq hQ

theorem subtype_val_eq {β : Type} {P : β → Prop} {a : β} {b : {x // P x}} : a = b.1 → ∀ (ha : P a), (⟨a, ha⟩ : {x // P x}) = b := by
  intro e ha; apply Subtype.ext; exact e

theorem at_sgT {dom : α} (S : Nat → Nat → Nat) (h : Nat) (τ : Nat → {x // M.mem x dom}) (hτ : ∀ k, M.H (τ k).1)
    (k : Nat) (hk : k ∈ NsL S h) (P : α → Prop) : At M.mem (M.sgT S h τ) (M.num k) P ↔ P (τ k).1 :=
  M.at_sgOf (NsL S h) (fun k => (τ k).1) hτ k hk P

section Clauses
variable {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}} {s : α} {h : Nat} {S : Nat → Nat → Nat} (R : M.Rep5T dom E Cn Fn Rel M5 S h)
  (hs : M.SeqRep4 s h S) (TV : α)
include R hs

theorem termClause_iff (i j : Nat) (τ : Nat → {x // M.mem x dom}) (v : {x // M.mem x dom})
    (hlist : ∀ f a j1 w, str S h i = some (.fn f a) → j = j1 + 1 →
      Tv M.mem TV (M.num (i + 2)) (M.num j1) (fun k => k = M.num (a + 2)) (M.sgT S h τ) (fun x => x = w) →
      ∃ ws : List {x // M.mem x dom}, ws.length = a ∧ M.RepL w (ws.map Subtype.val)) :
    TermClauseM M.mem s Cn Fn TV (M.num i) (M.num j) (M.sgT S h τ) v.1 ↔
      G5.termClause M5 (str S h) (M.TVl5 S h TV) i j τ v := by
  have hτ : ∀ k, M.H (τ k).1 := fun k => R.domH _ (τ k).2
  unfold TermClauseM G5.termClause
  rw [M.succ_num_iff]
  have ej : (M.num j = M.num (i + 1)) ↔ j = i + 1 := ⟨M.num_inj, fun e => by rw [e]⟩
  rw [ej]
  apply or_congr
  · apply and_congr Iff.rfl
    rw [M.at_tok2 hs i _ (fun x => ∃ k, x = some (.var k) ∧ v = τ k)]
    · intro t ht hi
      rw [M.var_iff ht, M.comp_iff ht (by decide)]
      constructor
      · rintro ⟨⟨k, hk⟩, hat⟩
        rw [tok_var_idx hk] at hat
        have hkL : k ∈ NsL S h := (mem_NsL S h k).mpr ⟨i, hi, hk⟩
        rw [M.at_sgT S h τ hτ k hkL] at hat
        exact ⟨k, hk, Subtype.ext hat.symm⟩
      · rintro ⟨k, hk, rfl⟩
        refine ⟨⟨k, hk⟩, ?_⟩
        rw [tok_var_idx hk]
        have hkL : k ∈ NsL S h := (mem_NsL S h k).mpr ⟨i, hi, hk⟩
        exact (M.at_sgT S h τ hτ k hkL _).mpr rfl
    · simp
  apply or_congr
  · apply and_congr Iff.rfl
    rw [M.at_tok2 hs i _ (fun x => ∃ k, x = some (.cst k) ∧ v = M5.Cn k)]
    · intro t ht hi
      rw [M.const_iff ht]
      constructor
      · rintro ⟨⟨k, hk⟩, hin⟩
        exact ⟨k, hk, Subtype.ext ((R.hCn t _ k ⟨i, hi, rfl⟩ ht hk v.1).mp hin)⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, (R.hCn t _ k ⟨i, hi, rfl⟩ ht hk _).mpr rfl⟩
    · simp
  · rw [M.at_tok2 hs i _ (fun x => ∃ f a j1, j = j1 + 1 ∧ x = some (.fn f a) ∧ str S h (i + 1) = some .lp ∧
        str S h j1 = some .rp ∧ ∃ ws, M.TVl5 S h TV (i + 2) j1 a τ ws ∧ v = M5.Fn f a ws)]
    · intro t ht hi
      rw [M.func_iff ht, M.comp_iff ht (by decide), M.nxt_iff, M.nxt_iff, M.prv_iff]
      simp only [M.at_punct hs _ 4 (by decide), M.at_punct hs _ 5 (by decide), punctTok]
      constructor
      · rintro ⟨⟨f, hf⟩, j1, rfl, hl, hr, htv⟩
        rw [M.tv_kp TV _ _ (M.plus2_kp (S i 3)), M.tv_split] at htv
        obtain ⟨w, htw, hin⟩ := htv
        obtain ⟨ws, hlen, hws⟩ := hlist f _ _ _ (str_some.mpr ⟨hi, hf⟩) rfl htw
        refine ⟨f, S i 3, j1, rfl, hf, hl, hr, ws, ⟨w, htw, hws⟩, ?_⟩
        exact Subtype.ext ((R.hFn t _ f _ ⟨i, hi, rfl⟩ ht hf w ws hlen hws v.1).mp hin)
      · rintro ⟨f, a, j1, rfl, hf, hl, hr, ws, ⟨w, htw, hws⟩, rfl⟩
        have ea := tok_fn_arity hf
        subst ea
        refine ⟨⟨f, hf⟩, j1, rfl, hl, hr, ?_⟩
        rw [M.tv_kp TV _ _ (M.plus2_kp (S i 3)), M.tv_split]
        obtain ⟨ws', hlen', hws'⟩ := hlist f _ _ _ (str_some.mpr ⟨hi, hf⟩) rfl htw
        have hlen : ws.length = S i 3 := by
          have := congrArg List.length (M.repL_unique hws hws'); simp only [List.length_map] at this; omega
        exact ⟨w, htw, (R.hFn t _ f _ ⟨i, hi, rfl⟩ ht hf w ws hlen hws _).mpr rfl⟩
    · simp

end Clauses

theorem cons_of_rep {v w2 w : α} {l : List α} (h2 : M.RepL w2 l) (h1 : M.RepL w (v :: l)) : ConsM M.mem v w2 w := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, hp⟩ := h1.2 0 v rfl
    exact ⟨M.num 0, (M.empty_iff _).mpr rfl, x, hx, hp⟩
  · intro q hq
    obtain ⟨i, a, hi, hp⟩ := h1.1 q hq
    refine ⟨_, _, hp, ?_⟩
    cases i with
    | zero =>
      simp at hi
      exact Or.inl ⟨(M.empty_iff _).mpr rfl, hi.symm⟩
    | succ i =>
      rw [List.get?_cons_succ] at hi
      obtain ⟨x, hx, hpx⟩ := h2.2 i a hi
      exact Or.inr ⟨M.num i, M.num_lt (by omega), (M.succ_num_iff i _).mpr rfl, x, hx, hpx⟩
  · intro q hq
    obtain ⟨i, a, hi, hp⟩ := h2.1 q hq
    refine ⟨_, _, hp, (M.nxt_iff i _).mpr ?_⟩
    exact h1.2 (i + 1) a (by rw [List.get?_cons_succ]; exact hi)

section Clauses2
variable {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}} {s : α} {h : Nat} {S : Nat → Nat → Nat} (R : M.Rep5T dom E Cn Fn Rel M5 S h)
  (hs : M.SeqRep4 s h S) (TV : α)
include R

theorem listClause_iff (C : α) (i j n : Nat) (τ : Nat → {x // M.mem x dom}) (w : α) (ws : List {x // M.mem x dom})
    (hw : M.RepL w (ws.map Subtype.val)) :
    ListClauseM M.mem C (M.num 0) TV (M.num i) (M.num j) (M.num n) (M.sgT S h τ) w ↔
      G5.listClause (M.Cn C) (M.TVt5 S h TV) (M.TVl5 S h TV) i j n τ ws := by
  unfold ListClauseM G5.listClause
  simp only []
  constructor
  · rintro (⟨hn, hij, he⟩ | ⟨n0, hn0, hs0, hc⟩)
    · rw [M.empty_iff] at hn
      have hw0 := (M.repL_nil w).mpr he
      have := M.repL_unique hw hw0
      exact Or.inl ⟨M.num_inj hn, M.num_inj hij, List.map_eq_nil.mp this⟩
    · obtain ⟨n0', rfl, rfl⟩ := M.succ_into_num hs0
      have via : ∀ m, m ≤ j → (InCert M.mem C (M.num i) (M.num m) (fun k => k = M.num 0) ∧
          Tv M.mem TV (M.num i) (M.num m) (fun k => k = M.num 0) (M.sgT S h τ) (fun v =>
            Tv M.mem TV (M.num m) (M.num j) (Plus2 M.mem (M.num n0')) (M.sgT S h τ) (fun w2 => ConsM M.mem v w2 w))) →
          G5.listClause (M.Cn C) (M.TVt5 S h TV) (M.TVl5 S h TV) i j (n0' + 1) τ ws := by
        rintro m hm ⟨hcm, htv⟩
        rw [M.tv_split] at htv
        obtain ⟨v, hv, htv2⟩ := htv
        rw [M.tv_kp TV _ _ (M.plus2_kp n0'), M.tv_split] at htv2
        obtain ⟨w2, hw2, hcons⟩ := htv2
        cases ws with
        | nil =>
          exfalso
          obtain ⟨⟨z, _, q, hq, _⟩, _, _⟩ := hcons
          rw [List.map_nil, M.repL_nil] at hw
          exact hw q hq
        | cons x l =>
          rw [List.map_cons] at hw
          obtain ⟨rfl, hl⟩ := M.cons_inv hcons hw
          exact Or.inr ⟨n0', rfl, m, hm, hcm, x, l, hv, ⟨w2, hw2, hl⟩, rfl⟩
      rcases hc with ⟨m, hm, hvia⟩ | hvia
      · obtain ⟨m', hm', rfl⟩ := (M.num_mem j m).mp hm
        exact via m' (Nat.le_of_lt hm') hvia
      · exact via j (Nat.le_refl _) hvia
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨n0, rfl, m, hm, hcm, v, ws2, hv, ⟨w2, hw2, hl⟩, rfl⟩)
    · rw [List.map_nil, M.repL_nil] at hw
      exact Or.inl ⟨(M.empty_iff _).mpr rfl, rfl, hw⟩
    · refine Or.inr ⟨M.num n0, M.num_lt (by omega), (M.succ_num_iff n0 _).mpr rfl, ?_⟩
      rw [List.map_cons] at hw
      have hcons := M.cons_of_rep hl hw
      have hvia : InCert M.mem C (M.num i) (M.num m) (fun k => k = M.num 0) ∧
          Tv M.mem TV (M.num i) (M.num m) (fun k => k = M.num 0) (M.sgT S h τ) (fun v =>
            Tv M.mem TV (M.num m) (M.num j) (Plus2 M.mem (M.num n0)) (M.sgT S h τ) (fun w2 => ConsM M.mem v w2 w)) := by
        refine ⟨hcm, (M.tv_split _ _ _ _ _ _).mpr ⟨v.1, hv, ?_⟩⟩
        rw [M.tv_kp TV _ _ (M.plus2_kp n0), M.tv_split]
        exact ⟨w2, hw2, hcons⟩
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact Or.inl ⟨M.num m, M.num_lt hm, hvia⟩
      · exact Or.inr hvia

end Clauses2

theorem sgT_upd {dom : α} (S : Nat → Nat → Nat) (h : Nat) (τ : Nat → {x // M.mem x dom}) (k : Nat) (x : {x // M.mem x dom}) :
    M.sgT S h (G5.upd τ k x) = M.sgOf (NsL S h) (Tr.upd (fun k => (τ k).1) k x.1) := by
  unfold sgT
  congr 1
  funext k'
  unfold G5.upd Tr.upd
  split <;> rfl

section Clauses3
variable {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}} {s : α} {h : Nat} {S : Nat → Nat → Nat} (R : M.Rep5T dom E Cn Fn Rel M5 S h)
  (hs : M.SeqRep4 s h S) (TV : α)
include hs

omit hs in
theorem infixS_iff' (C : α) (i j : Nat) (op : α → Prop) (x : Tok) (kind : Nat) (comb : α → α → α → α → Prop)
    (hs : M.SeqRep4 s h S) (hop : ∀ m, At M.mem s (M.num m) op ↔ str S h m = some x) :
    InfixS M.mem s C (M.num i) (M.num j) op (M.num kind) comb ↔
      (str S h i = some .lp ∧ ∃ j1, j = j1 + 1 ∧ str S h j1 = some .rp ∧
        ∃ m, m < j ∧ M.Cn C (i + 1) m kind ∧ str S h m = some x ∧ M.Cn C (m + 1) j1 kind ∧
          comb (M.num (i + 1)) (M.num m) (M.num (m + 1)) (M.num j1)) := by
  unfold InfixS
  rw [M.at_punct hs i 4 (by decide), M.nxt_iff, M.prv_iff]
  simp only [M.at_punct hs _ 5 (by decide)]
  constructor
  · rintro ⟨hl, j1, rfl, hr, m, hm, hc1, hop', hn⟩
    obtain ⟨m', rfl⟩ := M.at_num hs hop'
    rw [M.nxt_iff] at hn
    exact ⟨hl, j1, rfl, hr, m', (M.num_mem_iff).mp hm, hc1, (hop m').mp hop', hn.1, hn.2⟩
  · rintro ⟨hl, j1, rfl, hr, m, hm, hc1, hx, hc2, hcomb⟩
    exact ⟨hl, j1, rfl, hr, M.num m, M.num_lt hm, hc1, (hop m).mpr hx, (M.nxt_iff m _).mpr ⟨hc2, hcomb⟩⟩

include R

theorem formClause_iff (C SS Ns : α) (hNs : ∀ x, M.mem x Ns ↔ ∃ k, k ∈ NsL S h ∧ x = M.num k)
    (i j : Nat) (τ : Nat → {x // M.mem x dom})
    (htdom : ∀ a b v, M.Cn C a b 0 →
      Tv M.mem TV (M.num a) (M.num b) (fun k => k = M.num 0) (M.sgT S h τ) (fun x => x = v) → M.mem v dom)
    (hlist : ∀ r a j1 w, str S h i = some (.rel r a) → j = j1 + 1 →
      Tv M.mem TV (M.num (i + 2)) (M.num j1) (fun k => k = M.num (a + 2)) (M.sgT S h τ) (fun x => x = w) →
      ∃ ws : List {x // M.mem x dom}, ws.length = a ∧ M.RepL w (ws.map Subtype.val)) :
    FormClauseM M.mem s dom E Rel Ns C (M.num 0) (M.num 1) TV SS (M.num i) (M.num j) (M.sgT S h τ) ↔
      G5.formClause M5 (str S h) (M.Cn C) (M.TVt5 S h TV) (M.TVl5 S h TV) (M.S5 S h SS) i j τ := by
  have hτ : ∀ k, M.H (τ k).1 := fun k => R.domH _ (τ k).2
  unfold FormClauseM G5.formClause
  apply or_congr
  · constructor
    · rintro ⟨_, _, hne⟩; exact absurd rfl hne
    · rintro ⟨_, _, f⟩; exact f.elim
  apply or_congr
  · rw [M.infixS_iff' C i j _ .elem 0 _ hs (M.at_elem hs)]
    constructor
    · rintro ⟨hl, j1, rfl, hr, m, hm, hc1, hx, hc2, hcomb⟩
      refine ⟨hl, j1, rfl, hr, m, hm, hc1, hx, hc2, ?_⟩
      rw [M.tv_split] at hcomb
      obtain ⟨v1, hv1, hcomb⟩ := hcomb
      rw [M.tv_split] at hcomb
      obtain ⟨v2, hv2, hE⟩ := hcomb
      have d1 := htdom _ _ _ hc1 hv1
      have d2 := htdom _ _ _ hc2 hv2
      exact ⟨⟨v1, d1⟩, ⟨v2, d2⟩, hv1, hv2, (R.hE ⟨v1, d1⟩ ⟨v2, d2⟩).mp hE⟩
    · rintro ⟨hl, j1, rfl, hr, m, hm, hc1, hx, hc2, v1, v2, hv1, hv2, hE⟩
      refine ⟨hl, j1, rfl, hr, m, hm, hc1, hx, hc2, ?_⟩
      rw [M.tv_split]
      refine ⟨v1.1, hv1, ?_⟩
      rw [M.tv_split]
      exact ⟨v2.1, hv2, (R.hE v1 v2).mpr hE⟩
  apply or_congr
  · rw [M.at_tok2 hs i _ (fun x => ∃ r a j1, j = j1 + 1 ∧ x = some (.rel r a) ∧ str S h (i + 1) = some .lp ∧
        str S h j1 = some .rp ∧ ∃ ws, M.TVl5 S h TV (i + 2) j1 a τ ws ∧ M5.Rel r a ws)]
    · intro t ht hi
      rw [M.rel_iff ht, M.comp_iff ht (by decide), M.nxt_iff, M.nxt_iff, M.prv_iff]
      simp only [M.at_punct hs _ 4 (by decide), M.at_punct hs _ 5 (by decide), punctTok]
      constructor
      · rintro ⟨⟨r, hr⟩, j1, rfl, hl, hrp, htv⟩
        rw [M.tv_kp TV _ _ (M.plus2_kp (S i 3)), M.tv_split] at htv
        obtain ⟨w, htw, hin⟩ := htv
        obtain ⟨ws, hlen, hws⟩ := hlist r _ _ _ (str_some.mpr ⟨hi, hr⟩) rfl htw
        exact ⟨r, S i 3, j1, rfl, hr, hl, hrp, ws, ⟨w, htw, hws⟩, (R.hRel t _ r _ ⟨i, hi, rfl⟩ ht hr w ws hlen hws).mp hin⟩
      · rintro ⟨r, a, j1, rfl, hr, hl, hrp, ws, ⟨w, htw, hws⟩, hrel⟩
        have ea := tok_rel_arity hr
        subst ea
        refine ⟨⟨r, hr⟩, j1, rfl, hl, hrp, ?_⟩
        rw [M.tv_kp TV _ _ (M.plus2_kp (S i 3)), M.tv_split]
        obtain ⟨ws', hlen', hws'⟩ := hlist r _ _ _ (str_some.mpr ⟨hi, hr⟩) rfl htw
        have hlen : ws.length = S i 3 := by
          have := congrArg List.length (M.repL_unique hws hws'); simp only [List.length_map] at this; omega
        exact ⟨w, htw, (R.hRel t _ r _ ⟨i, hi, rfl⟩ ht hr w ws hlen hws).mpr hrel⟩
    · simp
  apply or_congr
  · rw [M.infixS_iff' C i j _ .imp 1 _ hs (M.at_punct hs · 1 (by decide))]
    try simp only [punctTok]
    constructor
    · rintro ⟨hl, j1, rfl, hr, m, hm, hc1, hx, hc2, hcomb⟩
      refine ⟨hl, j1, rfl, hr, m, hm, hc1, hx, hc2, fun h1 => ?_⟩
      rcases hcomb with h' | h'
      · exact absurd h1 h'
      · exact h'
    · rintro ⟨hl, j1, rfl, hr, m, hm, hc1, hx, hc2, himp⟩
      refine ⟨hl, j1, rfl, hr, m, hm, hc1, hx, hc2, ?_⟩
      by_cases h1 : M.S5 S h SS (i + 1) m τ
      · exact Or.inr (himp h1)
      · exact Or.inl h1
  apply or_congr
  · rw [M.at_punct hs i 2 (by decide), M.nxt_iff]
    try simp only [punctTok]
    rfl
  · rw [M.at_punct hs i 3 (by decide), M.nxt_iff]
    try simp only [punctTok]
    apply and_congr Iff.rfl
    rw [M.at_tok2 hs (i + 1) _ (fun x => ∃ k, x = some (.var k) ∧ str S h (i + 2) = some .lp ∧
        ∃ j1, j = j1 + 1 ∧ str S h j1 = some .rp ∧ M.Cn C (i + 3) j1 1 ∧ ∃ x, M.S5 S h SS (i + 3) j1 (G5.upd τ k x))]
    · intro t ht hi
      rw [M.var_iff ht, M.comp_iff ht (by decide), M.nxt_iff, M.at_punct hs _ 4 (by decide), M.nxt_iff, M.prv_iff]
      simp only [M.at_punct hs _ 5 (by decide), punctTok]
      have upd_iff : ∀ k, k ∈ NsL S h → ∀ j1,
          (∃ a, M.mem a dom ∧ ∃ sg2, UpdateM M.mem Ns dom (M.sgT S h τ) (M.num k) a sg2 ∧
            InS M.mem SS (M.num (i + 3)) (M.num j1) sg2) ↔ ∃ x, M.S5 S h SS (i + 3) j1 (G5.upd τ k x) := by
        intro k hk j1
        constructor
        · rintro ⟨a, ha, sg2, hu, hin⟩
          rw [show M.sgT S h τ = M.sgOf (NsL S h) (fun k => (τ k).1) from rfl,
            M.update_sgOf (NsL S h) _ hτ Ns dom hNs (fun k => (τ k).2) k hk a sg2 ha (R.domH a ha)] at hu
          subst hu
          refine ⟨⟨a, ha⟩, ?_⟩
          unfold S5; rw [M.sgT_upd]; exact hin
        · rintro ⟨x, hx⟩
          unfold S5 at hx; rw [M.sgT_upd] at hx
          refine ⟨x.1, x.2, _, ?_, hx⟩
          rw [show M.sgT S h τ = M.sgOf (NsL S h) (fun k => (τ k).1) from rfl,
            M.update_sgOf (NsL S h) _ hτ Ns dom hNs (fun k => (τ k).2) k hk x.1 _ x.2 (R.domH _ x.2)]
      constructor
      · rintro ⟨⟨k, hk⟩, hl, j1, rfl, hr, hc, hex⟩
        rw [tok_var_idx hk] at hex
        have hkL : k ∈ NsL S h := (mem_NsL S h k).mpr ⟨i + 1, hi, hk⟩
        exact ⟨k, hk, hl, j1, rfl, hr, hc, (upd_iff k hkL j1).mp hex⟩
      · rintro ⟨k, hk, hl, j1, rfl, hr, hc, hex⟩
        have hkL : k ∈ NsL S h := (mem_NsL S h k).mpr ⟨i + 1, hi, hk⟩
        refine ⟨⟨k, hk⟩, hl, j1, rfl, hr, hc, ?_⟩
        rw [tok_var_idx hk]
        exact (upd_iff k hkL j1).mpr hex
    · simp

end Clauses3

section Main
variable {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}} {s : α} {h : Nat} {S : Nat → Nat → Nat} (R : M.Rep5T dom E Cn Fn Rel M5 S h)
  (hs : M.SeqRep4 s h S)
include R hs

theorem termClause_dom {TV Ns sg i j v : α} (hA : AssignM M.mem Ns dom sg)
    (hc : TermClauseM M.mem s Cn Fn TV i j sg v) : M.mem v dom := by
  rcases hc with ⟨_, q, hq, t, hpt, _, kk, _, q2, _, k, _, q3, hq3, b, hpb, rfl⟩ |
    ⟨_, q, hq, t, hpt, hcst, hin⟩ | ⟨q, hq, t, hpt, _, kk, _, q2, _, ar, _, i1, _, i2, _, j1, _, _, _, _, htv⟩
  · obtain ⟨k', a', hp', _, ha'⟩ := hA.1 q3 hq3
    obtain ⟨_, rfl⟩ := M.pair_unique hpb hp'
    exact ha'
  · obtain ⟨i', hi', t', hp', hrep⟩ := hs.1 q hq
    obtain ⟨_, rfl⟩ := M.pair_unique hpt hp'
    obtain ⟨k, hk⟩ := (M.const_iff hrep).mp hcst
    rw [(R.hCn t _ k ⟨i', hi', rfl⟩ hrep hk v).mp hin]
    exact (M5.Cn k).2
  · rw [M.tv_split] at htv
    obtain ⟨w, _, hin⟩ := htv
    exact R.hFnd _ _ _ hin

omit R in
theorem term_end_cn {C : α} (hC : CertOk M.mem s C (M.num 0) (M.num 1)) {i m m' : Nat}
    (h1 : M.Cn C i m 0) (h2 : M.Cn C i m' 0) : m = m' := by
  have hJ := M.cert_sound hs C hC
  obtain ⟨t1, hw1, ho1, e1⟩ := G5.sound (str S h) (M.Cn C) h (str_fin S h) hJ m 0 i h1
  obtain ⟨t2, hw2, ho2, e2⟩ := G5.sound (str S h) (M.Cn C) h (str_fin S h) hJ m' 0 i h2
  have := G5.term_ur (str S h) t1 t2 i hw1 hw2 ho1 ho2
  subst this; omega

/-- 表の条件（certificate_ok・TV の条件・S の条件）が成り立てば、根の項目の S は Tarski の充足と一致する。 -/
theorem tables_sat (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
    {Ns C TV SS : α} (hNs : ∀ x, M.mem x Ns ↔ ∃ k, k ∈ NsL S h ∧ x = M.num k)
    (hroot : M.Cn C 0 h 1) (hC : CertOk M.mem s C (M.num 0) (M.num 1))
    (hTV : TvOk M.mem s dom Cn Fn Ns C (M.num 0) TV) (hSo : SOk M.mem s dom E Rel Ns C (M.num 0) (M.num 1) TV SS)
    (τ : Nat → {x // M.mem x dom}) : M.S5 S h SS 0 h τ ↔ φ.sat M5 τ := by
  have hJ := M.cert_sound hs C hC
  have hτH : ∀ (τ' : Nat → {x // M.mem x dom}) k, M.H (τ' k).1 := fun τ' k => R.domH _ (τ' k).2
  have hAs : ∀ τ' : Nat → {x // M.mem x dom}, AssignM M.mem Ns dom (M.sgT S h τ') :=
    fun τ' => M.assign_sgOf (NsL S h) (fun k => (τ' k).1) (hτH τ') Ns dom hNs (fun k => (τ' k).2)
  -- 行の取り出し
  have row : ∀ i j k, M.Cn C i j k → ∃ p, M.mem p C ∧ Triple M.mem p (M.num i) (M.num j) (M.num k) := by
    rintro i j k ⟨p, hp, kk, htr, rfl⟩; exact ⟨p, hp, htr⟩
  -- 項の値
  have tval : ∀ i j (τ' : Nat → {x // M.mem x dom}) v, M.Cn C i j 0 →
      Tv M.mem TV (M.num i) (M.num j) (fun k => k = M.num 0) (M.sgT S h τ') (fun x => x = v) →
      TermClauseM M.mem s Cn Fn TV (M.num i) (M.num j) (M.sgT S h τ') v ∧ M.mem v dom := by
    intro i j τ' v hc htv
    obtain ⟨p, hp, htr⟩ := row i j 0 hc
    obtain ⟨i', j', k', htr', hterm, _⟩ := hTV p hp
    obtain ⟨rfl, rfl, rfl⟩ := M.triple_unique htr' htr
    have hcl := M.tvall_val htv ((hterm rfl _ (hAs τ')).2)
    exact ⟨hcl, M.termClause_dom R hs (hAs τ') hcl⟩
  -- 項の列の値
  have lval : ∀ n i j (τ' : Nat → {x // M.mem x dom}) w, M.Cn C i j (n + 2) →
      Tv M.mem TV (M.num i) (M.num j) (fun k => k = M.num (n + 2)) (M.sgT S h τ') (fun x => x = w) →
      ∃ ws : List {x // M.mem x dom}, ws.length = n ∧ M.RepL w (ws.map Subtype.val) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro i j τ' w hc htv
    obtain ⟨p, hp, htr⟩ := row i j _ hc
    obtain ⟨i', j', k', htr', _, hlist⟩ := hTV p hp
    obtain ⟨rfl, rfl, rfl⟩ := M.triple_unique htr' htr
    have hcl := M.tvall_val htv ((hlist (M.num (n + 1)) (M.num_lt (by omega)) (M.num n) (M.num_lt (by omega))
      ((M.plus2_iff n _).mpr rfl) _ (hAs τ')).2)
    rcases hcl with ⟨hn, _, he⟩ | ⟨n0, hn0, hs0, hvia⟩
    · have := M.num_inj ((M.empty_iff _).mp hn)
      exact ⟨[], by simp [this], (M.repL_nil w).mpr he⟩
    · obtain ⟨n0', rfl, rfl⟩ := M.succ_into_num hs0
      have via : ∀ m, m ≤ j → (InCert M.mem C (M.num i) (M.num m) (fun k => k = M.num 0) ∧
          Tv M.mem TV (M.num i) (M.num m) (fun k => k = M.num 0) (M.sgT S h τ') (fun v =>
            Tv M.mem TV (M.num m) (M.num j) (Plus2 M.mem (M.num n0')) (M.sgT S h τ') (fun w2 => ConsM M.mem v w2 w))) →
          ∃ ws : List {x // M.mem x dom}, ws.length = n0' + 1 ∧ M.RepL w (ws.map Subtype.val) := by
        rintro m hm ⟨hcm, htv1⟩
        rw [M.tv_split] at htv1
        obtain ⟨v, hv, htv2⟩ := htv1
        rw [M.tv_kp TV _ _ (M.plus2_kp n0'), M.tv_split] at htv2
        obtain ⟨w2, hw2, hcons⟩ := htv2
        have hvd := (tval i m τ' v hcm hv).2
        -- 部分列の行 (m, j, n0' + 2) も証明書にある
        have hJl := hJ i j (n0' + 1 + 2) hc
        simp only [Just, listOk] at hJl
        rcases hJl with ⟨e, _⟩ | ⟨n0b, e, mb, _, hc1, hc2⟩
        · omega
        · have e1 : n0b = n0' := by omega
          subst e1
          have := M.term_end_cn hs hC hcm hc1
          subst this
          obtain ⟨ws2, hlen2, hws2⟩ := ih _ (by omega) _ j τ' w2 hc2 hw2
          exact ⟨⟨v, hvd⟩ :: ws2, by simp [hlen2], by rw [List.map_cons]; exact M.cons_rep hcons hws2⟩
      rcases hvia with ⟨m, hm, hv⟩ | hv
      · obtain ⟨m', hm', rfl⟩ := (M.num_mem j m).mp hm
        exact via m' (Nat.le_of_lt hm') hv
      · exact via j (Nat.le_refl _) hv
  -- G5 の表の条件
  have hTVt : ∀ i j, M.Cn C i j 0 → ∀ (τ' : Nat → {x // M.mem x dom}), (∃ v, M.TVt5 S h TV i j τ' v) ∧
      ∀ v, M.TVt5 S h TV i j τ' v → G5.termClause M5 (str S h) (M.TVl5 S h TV) i j τ' v := by
    intro i j hc τ'
    obtain ⟨p, hp, htr⟩ := row i j 0 hc
    obtain ⟨i', j', k', htr', hterm, _⟩ := hTV p hp
    obtain ⟨rfl, rfl, rfl⟩ := M.triple_unique htr' htr
    constructor
    · have := (hterm rfl _ (hAs τ')).1
      rw [M.tv_split] at this
      obtain ⟨v, hv, _⟩ := this
      exact ⟨⟨v, (tval i j τ' v hc hv).2⟩, hv⟩
    · intro v hv
      refine (M.termClause_iff R hs TV i j τ' v ?_).mp (tval i j τ' v.1 hc hv).1
      intro f a j1 w hf hj htw
      have hJt := hJ i j 0 hc
      simp only [Just, termOk] at hJt
      rcases hJt with ⟨_, ⟨k, hk⟩ | ⟨k, hk⟩⟩ | ⟨f', a', j1', e, hf', _, _, hc2⟩
      · rw [hf] at hk; cases hk
      · rw [hf] at hk; cases hk
      · rw [hf] at hf'; cases hf'
        have : j1 = j1' := by omega
        subst this
        exact lval a (i + 2) j1 τ' w hc2 htw
  have hTVl : ∀ i j n, M.Cn C i j (n + 2) → ∀ (τ' : Nat → {x // M.mem x dom}), (∃ ws, M.TVl5 S h TV i j n τ' ws) ∧
      ∀ ws, M.TVl5 S h TV i j n τ' ws → G5.listClause (M.Cn C) (M.TVt5 S h TV) (M.TVl5 S h TV) i j n τ' ws := by
    intro i j n hc τ'
    obtain ⟨p, hp, htr⟩ := row i j _ hc
    obtain ⟨i', j', k', htr', _, hlist⟩ := hTV p hp
    obtain ⟨rfl, rfl, rfl⟩ := M.triple_unique htr' htr
    have hl := hlist (M.num (n + 1)) (M.num_lt (by omega)) (M.num n) (M.num_lt (by omega))
      ((M.plus2_iff n _).mpr rfl) _ (hAs τ')
    constructor
    · have := hl.1
      rw [M.tv_split] at this
      obtain ⟨w, hw, _⟩ := this
      obtain ⟨ws, _, hws⟩ := lval n i j τ' w hc hw
      exact ⟨ws, w, hw, hws⟩
    · rintro ws ⟨w, hw, hws⟩
      exact (M.listClause_iff R TV C i j n τ' w ws hws).mp (M.tvall_val hw hl.2)
  have hS : ∀ i j, M.Cn C i j 1 → ∀ (τ' : Nat → {x // M.mem x dom}), (M.S5 S h SS i j τ' ↔
      G5.formClause M5 (str S h) (M.Cn C) (M.TVt5 S h TV) (M.TVl5 S h TV) (M.S5 S h SS) i j τ') := by
    intro i j hc τ'
    obtain ⟨p, hp, htr⟩ := row i j 1 hc
    obtain ⟨i', j', k', htr', hform⟩ := hSo p hp
    obtain ⟨rfl, rfl, rfl⟩ := M.triple_unique htr' htr
    rw [← M.formClause_iff R hs TV C SS Ns hNs i j τ' (fun a b v hc' hv => (tval a b τ' v hc' hv).2)]
    · exact hform rfl _ (hAs τ')
    · intro r a j1 w hr hj htw
      have hJf := hJ i j 1 hc
      simp only [Just, formOk] at hJf
      rcases hJf with ⟨_, hb⟩ | ⟨hl', _⟩ | ⟨r', a', j1', e, hr', _, _, hc2⟩ | ⟨hl', _⟩ | ⟨hn, _⟩ | ⟨hx, _⟩
      · rw [hr] at hb; cases hb
      · rw [hr] at hl'; cases hl'
      · rw [hr] at hr'; cases hr'
        have : j1 = j1' := by omega
        subst this
        exact lval a (i + 2) j1 τ' w hc2 htw
      · rw [hr] at hl'; cases hl'
      · rw [hr] at hn; cases hn
      · rw [hr] at hx; cases hx
  have hroot' : M.Cn C 0 (0 + φ.toks.length) 1 := by rw [Nat.zero_add, ← hl]; exact hroot
  have key := G5.form_sat M5 (str S h) (M.Cn C) h (str_fin S h) hJ (M.TVt5 S h TV) (M.TVl5 S h TV) (M.S5 S h SS)
    hTVt hTVl hS φ 0 hw ho hroot' τ
  rw [Nat.zero_add, ← hl] at key
  exact key

/-- 健全性：sat の式が sgT τ で成り立てば、φ は τ の下で真。 -/
theorem sat_sound (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
    (τ : Nat → {x // M.mem x dom}) :
    SatM M.mem s dom E Cn Fn Rel (M.sgT S h τ) → φ.sat M5 τ := by
  rintro ⟨K0, he0, K1, he1, h', hsw, Ns, hvs, hA, C, hroot, hC, TV, hTV, SS, hSo, hin⟩
  rw [M.empty_iff] at he0; subst he0
  rw [M.succ_num_iff] at he1; subst he1
  have eh := M.seqWith_dom (SeqRep4.dom M hs) hsw; subst eh
  have hNs := (M.varset_iff hs Ns).mp hvs
  exact (M.tables_sat R hs φ hw ho hl hNs hroot hC hTV hSo τ).mp hin

end Main

/-! ### 完全性のための集合の構成 -/

/-- 完全性で使う、H（V_κ）の閉包性。M = (V_{κ+1})^L で H = V_κ（κ は L で到達不能）なら成り立つ。 -/
structure Zax : Prop where
  H_trans : ∀ x y, M.H y → M.mem x y → M.H x
  union : ∀ A, M.H A → ∃ U, M.H U ∧ ∀ x, M.mem x U ↔ ∃ y, M.mem y A ∧ M.mem x y
  pow : ∀ A, M.H A → ∃ P, M.H P ∧ ∀ x, M.mem x P ↔ (M.H x ∧ ∀ y, M.mem y x → M.mem y A)
  sep : ∀ A (P : α → Prop), M.H A → ∃ B, M.H B ∧ ∀ x, M.mem x B ↔ M.mem x A ∧ P x
  repl : ∀ A (F : α → α), M.H A → (∀ x, M.mem x A → M.H (F x)) →
    ∃ B, M.H B ∧ ∀ y, M.mem y B ↔ ∃ x, M.mem x A ∧ y = F x

section Constr
variable (Z : M.Zax)
include Z

/-- 像 { F x : x ∈ A }。 -/
theorem image_ex (A : α) (F : α → α) (hA : M.H A) (hF : ∀ x, M.mem x A → M.H (F x)) :
    ∃ B, M.H B ∧ ∀ y, M.mem y B ↔ ∃ x, M.mem x A ∧ y = F x := Z.repl A F hA hF

open Classical in
/-- 直積 X × Y（順序対 pr x y の集合）。 -/
theorem prod_ex (X Y : α) (hX : M.H X) (hY : M.H Y) :
    ∃ P, M.H P ∧ ∀ p, M.mem p P ↔ ∃ x y, M.mem x X ∧ M.mem y Y ∧ p = M.pr x y := by
  have hpr : ∀ x y, M.mem x X → M.mem y Y → M.H (M.pr x y) := fun x y hx hy =>
    (M.pr_spec (Z.H_trans x X hX hx) (Z.H_trans y Y hY hy)).1
  have hrow : ∀ x, M.mem x X → ∃ B, M.H B ∧ ∀ p, M.mem p B ↔ ∃ y, M.mem y Y ∧ p = M.pr x y :=
    fun x hx => Z.repl Y (M.pr x) hY (fun y hy => hpr x y hx hy)
  let row : α → α := fun x => if hx : M.mem x X then Classical.choose (hrow x hx) else M.num 0
  have hrowS : ∀ x (hx : M.mem x X), M.H (row x) ∧ ∀ p, M.mem p (row x) ↔ ∃ y, M.mem y Y ∧ p = M.pr x y := by
    intro x hx; simp only [row, hx, dite_true]; exact Classical.choose_spec (hrow x hx)
  obtain ⟨R, hR, hRm⟩ := Z.repl X row hX (fun x hx => (hrowS x hx).1)
  obtain ⟨U, hU, hUm⟩ := Z.union R hR
  refine ⟨U, hU, fun p => ?_⟩
  rw [hUm]
  constructor
  · rintro ⟨r, hr, hp⟩
    obtain ⟨x, hx, rfl⟩ := (hRm r).mp hr
    obtain ⟨y, hy, rfl⟩ := ((hrowS x hx).2 p).mp hp
    exact ⟨x, y, hx, hy, rfl⟩
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨row x, (hRm _).mpr ⟨x, hx, rfl⟩, ((hrowS x hx).2 _).mpr ⟨y, hy, rfl⟩⟩

end Constr

end Model

/-! ### G5 の条件の、表の取り替えについての性質（行の終わりが j 以下の項目だけが効く） -/
section Congr
variable {β : Type} (M5 : G5.Model β) (s : Str)

theorem termClause_mono {TVl TVl' : Nat → Nat → Nat → (Nat → β) → List β → Prop} {i j : Nat} {σ : Nat → β} {v : β}
    (hm : ∀ a b n ws, b < j → TVl a b n σ ws → TVl' a b n σ ws) :
    G5.termClause M5 s TVl i j σ v → G5.termClause M5 s TVl' i j σ v := by
  rintro (h1 | h2 | ⟨f, a, j1, e, hf, hl, hr, w, hw, hv⟩)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨f, a, j1, e, hf, hl, hr, w, hm _ _ _ _ (by omega) hw, hv⟩)

theorem listClause_mono {C C' : Nat → Nat → Nat → Prop} {TVt TVt' : Nat → Nat → (Nat → β) → β → Prop}
    {TVl TVl' : Nat → Nat → Nat → (Nat → β) → List β → Prop} {i j n : Nat} {σ : Nat → β} {w : List β}
    (hC : ∀ a b k, b ≤ j → C a b k → C' a b k) (ht : ∀ a b v, b ≤ j → TVt a b σ v → TVt' a b σ v)
    (hl : ∀ a b n ws, b ≤ j → TVl a b n σ ws → TVl' a b n σ ws) :
    G5.listClause C TVt TVl i j n σ w → G5.listClause C' TVt' TVl' i j n σ w := by
  rintro (h1 | ⟨n0, e, m, hm, hc, v, w2, hv, hw2, hw⟩)
  · exact Or.inl h1
  · exact Or.inr ⟨n0, e, m, hm, hC _ _ _ hm hc, v, w2, ht _ _ _ hm hv, hl _ _ _ _ (Nat.le_refl _) hw2, hw⟩

theorem formClause_congr {C C' : Nat → Nat → Nat → Prop} {TVt TVt' : Nat → Nat → (Nat → β) → β → Prop}
    {TVl TVl' : Nat → Nat → Nat → (Nat → β) → List β → Prop} {S S' : Nat → Nat → (Nat → β) → Prop}
    {i j : Nat} {σ : Nat → β}
    (hC : ∀ a b k, b ≤ j → (C a b k ↔ C' a b k)) (ht : ∀ a b v, b ≤ j → (TVt a b σ v ↔ TVt' a b σ v))
    (hl : ∀ a b n ws, b ≤ j → (TVl a b n σ ws ↔ TVl' a b n σ ws))
    (hS : ∀ a b, b ≤ j → (S a b σ ↔ S' a b σ))
    (hSx : ∀ a b k x, b ≤ j → s (i + 1) = some (.var k) → (S a b (G5.upd σ k x) ↔ S' a b (G5.upd σ k x))) :
    G5.formClause M5 s C TVt TVl S i j σ ↔ G5.formClause M5 s C' TVt' TVl' S' i j σ := by
  unfold G5.formClause
  apply or_congr Iff.rfl
  apply or_congr
  · constructor
    · rintro ⟨hl0, j1, e, hr, m, hm, c1, hx, c2, v1, v2, h1, h2, hE⟩
      exact ⟨hl0, j1, e, hr, m, hm, (hC _ _ _ (by omega)).mp c1, hx, (hC _ _ _ (by omega)).mp c2, v1, v2,
        (ht _ _ _ (by omega)).mp h1, (ht _ _ _ (by omega)).mp h2, hE⟩
    · rintro ⟨hl0, j1, e, hr, m, hm, c1, hx, c2, v1, v2, h1, h2, hE⟩
      exact ⟨hl0, j1, e, hr, m, hm, (hC _ _ _ (by omega)).mpr c1, hx, (hC _ _ _ (by omega)).mpr c2, v1, v2,
        (ht _ _ _ (by omega)).mpr h1, (ht _ _ _ (by omega)).mpr h2, hE⟩
  apply or_congr
  · constructor
    · rintro ⟨r, a, j1, e, h1, h2, h3, w, hw, hR⟩
      exact ⟨r, a, j1, e, h1, h2, h3, w, (hl _ _ _ _ (by omega)).mp hw, hR⟩
    · rintro ⟨r, a, j1, e, h1, h2, h3, w, hw, hR⟩
      exact ⟨r, a, j1, e, h1, h2, h3, w, (hl _ _ _ _ (by omega)).mpr hw, hR⟩
  apply or_congr
  · constructor
    · rintro ⟨hl0, j1, e, hr, m, hm, c1, hx, c2, himp⟩
      exact ⟨hl0, j1, e, hr, m, hm, (hC _ _ _ (by omega)).mp c1, hx, (hC _ _ _ (by omega)).mp c2,
        fun h1 => (hS _ _ (by omega)).mp (himp ((hS _ _ (by omega)).mpr h1))⟩
    · rintro ⟨hl0, j1, e, hr, m, hm, c1, hx, c2, himp⟩
      exact ⟨hl0, j1, e, hr, m, hm, (hC _ _ _ (by omega)).mpr c1, hx, (hC _ _ _ (by omega)).mpr c2,
        fun h1 => (hS _ _ (by omega)).mpr (himp ((hS _ _ (by omega)).mp h1))⟩
  apply or_congr
  · constructor
    · rintro ⟨hn, c, hs'⟩
      exact ⟨hn, (hC _ _ _ (Nat.le_refl _)).mp c, fun h' => hs' ((hS _ _ (Nat.le_refl _)).mpr h')⟩
    · rintro ⟨hn, c, hs'⟩
      exact ⟨hn, (hC _ _ _ (Nat.le_refl _)).mpr c, fun h' => hs' ((hS _ _ (Nat.le_refl _)).mp h')⟩
  · constructor
    · rintro ⟨hx, k, hk, hl0, j1, e, hr, c, x, hsx⟩
      exact ⟨hx, k, hk, hl0, j1, e, hr, (hC _ _ _ (by omega)).mp c, x, (hSx _ _ _ _ (by omega) hk).mp hsx⟩
    · rintro ⟨hx, k, hk, hl0, j1, e, hr, c, x, hsx⟩
      exact ⟨hx, k, hk, hl0, j1, e, hr, (hC _ _ _ (by omega)).mpr c, x, (hSx _ _ _ _ (by omega) hk).mpr hsx⟩

/-- 本当の値は一意。 -/
theorem tvtrue_unique {i j : Nat} {σ : Nat → β} {v v' : β} (h1 : G5.TVtrue M5 s i j σ v) (h2 : G5.TVtrue M5 s i j σ v') :
    v = v' := by
  obtain ⟨t, hw, ho, _, rfl⟩ := h1
  obtain ⟨t', hw', ho', _, rfl⟩ := h2
  rw [G5.term_ur s t t' i hw hw' ho ho']
theorem tvltrue_unique {i j n : Nat} {σ : Nat → β} {w w' : List β} (h1 : G5.TVltrue M5 s i j n σ w)
    (h2 : G5.TVltrue M5 s i j n σ w') : w = w' := by
  obtain ⟨ts, hw, hn, ho, _, rfl⟩ := h1
  obtain ⟨ts', hw', hn', ho', _, rfl⟩ := h2
  rw [G5.terms_ur s ts ts' i hw hw' (hn.trans hn'.symm) ho ho']

end Congr

namespace Model
variable {α : Type} (M : Model α)

/-! ### 標準の割当て τc：集合の割当て sg から G5 の割当てを作る -/

section Canon
variable {dom : α} (S : Nat → Nat → Nat) (h : Nat) (σ0 : Nat → {x // M.mem x dom})

open Classical in
noncomputable def τc (sg : α) : Nat → {x // M.mem x dom} := fun k =>
  if hk : k ∈ NsL S h ∧ ∃ a : {x // M.mem x dom}, At M.mem sg (M.num k) (fun x => x = a.1) then Classical.choose hk.2
  else σ0 k

theorem τc_out (sg : α) (k : Nat) (hk : k ∉ NsL S h) : M.τc S h σ0 sg k = σ0 k := by
  unfold τc; rw [dif_neg]; exact fun h' => hk h'.1

theorem τc_at (sg : α) (k : Nat) (hk : k ∈ NsL S h) (hex : ∃ a : {x // M.mem x dom}, At M.mem sg (M.num k) (fun x => x = a.1)) :
    At M.mem sg (M.num k) (fun x => x = (M.τc S h σ0 sg k).1) := by
  unfold τc; rw [dif_pos ⟨hk, hex⟩]; exact Classical.choose_spec hex

theorem τc_sgT (hH : ∀ x, M.mem x dom → M.H x) (σ : Nat → {x // M.mem x dom}) (k : Nat) (hk : k ∈ NsL S h) :
    M.τc S h σ0 (M.sgT S h σ) k = σ k := by
  have hτ : ∀ k, M.H (σ k).1 := fun k => hH _ (σ k).2
  have hex : ∃ a : {x // M.mem x dom}, At M.mem (M.sgT S h σ) (M.num k) (fun x => x = a.1) :=
    ⟨σ k, (M.at_sgT S h σ hτ k hk _).mpr rfl⟩
  have := M.τc_at S h σ0 _ k hk hex
  rw [M.at_sgT S h σ hτ k hk] at this
  exact Subtype.ext this.symm

theorem sgT_τc (hH : ∀ x, M.mem x dom → M.H x) {Ns sg : α} (hNs : ∀ x, M.mem x Ns ↔ ∃ k, k ∈ NsL S h ∧ x = M.num k)
    (hA : AssignM M.mem Ns dom sg) : M.sgT S h (M.τc S h σ0 sg) = sg := by
  have hτ : ∀ k, M.H (M.τc S h σ0 sg k).1 := fun k => hH _ (M.τc S h σ0 sg k).2
  -- sg の k での値
  have val : ∀ k, k ∈ NsL S h → ∃ a : {x // M.mem x dom}, At M.mem sg (M.num k) (fun x => x = a.1) := by
    intro k hk
    obtain ⟨q, hq, a, hp⟩ := hA.2.1 (M.num k) ((hNs _).mpr ⟨k, hk, rfl⟩)
    obtain ⟨k', a', hp', _, ha'⟩ := hA.1 q hq
    obtain ⟨_, rfl⟩ := M.pair_unique hp hp'
    exact ⟨⟨a, ha'⟩, q, hq, a, hp, rfl⟩
  apply M.ext
  intro q
  unfold sgT
  rw [M.sgOf_spec _ _ hτ]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨q', hq', b, hp', hb⟩ := M.τc_at S h σ0 sg k hk (val k hk)
    rw [hb] at hp'
    rw [← M.pair_ext hp' (M.pr_spec (M.H_num k) (hτ k)).2]; exact hq'
  · intro hq
    obtain ⟨kk, a, hp, hkk, _⟩ := hA.1 q hq
    obtain ⟨k, hk, rfl⟩ := (hNs kk).mp hkk
    obtain ⟨q', hq', b, hp', hb⟩ := M.τc_at S h σ0 sg k hk (val k hk)
    have := M.assign_func hA hq hp hq' hp'
    subst this
    refine ⟨k, hk, ?_⟩
    rw [hb] at hp
    exact M.pair_ext hp (M.pr_spec (M.H_num k) (hτ k)).2

/-- 標準の割当ての更新もまた標準。 -/
theorem τc_upd (hH : ∀ x, M.mem x dom → M.H x) {Ns sg : α} (hNs : ∀ x, M.mem x Ns ↔ ∃ k, k ∈ NsL S h ∧ x = M.num k)
    (hA : AssignM M.mem Ns dom sg) (k : Nat) (hk : k ∈ NsL S h) (x : {x // M.mem x dom}) :
    M.τc S h σ0 (M.sgT S h (G5.upd (M.τc S h σ0 sg) k x)) = G5.upd (M.τc S h σ0 sg) k x := by
  funext k'
  by_cases hk' : k' ∈ NsL S h
  · exact M.τc_sgT S h σ0 hH _ k' hk'
  · rw [M.τc_out S h σ0 _ k' hk']
    have : k' ≠ k := fun e => hk' (e ▸ hk)
    simp only [G5.upd, this, ite_false]
    rw [M.τc_out S h σ0 _ k' hk']

theorem τc_canon (hH : ∀ x, M.mem x dom → M.H x) {Ns sg : α} (hNs : ∀ x, M.mem x Ns ↔ ∃ k, k ∈ NsL S h ∧ x = M.num k)
    (hA : AssignM M.mem Ns dom sg) : M.τc S h σ0 (M.sgT S h (M.τc S h σ0 sg)) = M.τc S h σ0 sg := by
  rw [M.sgT_τc S h σ0 hH hNs hA]

end Canon

/-! ### 列の集合 lset -/

noncomputable def lpairs : List α → Nat → List α
  | [], _ => []
  | a :: l, k => M.pr (M.num k) a :: lpairs l (k + 1)

theorem lpairs_mem : ∀ (l : List α) (k : Nat) (x : α),
    x ∈ M.lpairs l k ↔ ∃ i a, l.get? i = some a ∧ x = M.pr (M.num (k + i)) a
  | [], k, x => by simp [lpairs]
  | a :: l, k, x => by
    simp only [lpairs, List.mem_cons]
    rw [lpairs_mem l (k + 1) x]
    constructor
    · rintro (rfl | ⟨i, b, hb, rfl⟩)
      · exact ⟨0, a, rfl, by simp⟩
      · exact ⟨i + 1, b, by simpa using hb, by rw [show k + 1 + i = k + (i + 1) by omega]⟩
    · rintro ⟨i, b, hb, rfl⟩
      cases i with
      | zero => simp at hb; subst hb; exact Or.inl (by simp)
      | succ i =>
        rw [List.get?_cons_succ] at hb
        exact Or.inr ⟨i, b, hb, by rw [show k + (i + 1) = k + 1 + i by omega]⟩

noncomputable def lset (l : List α) : α := M.set (M.lpairs l 0)

theorem lset_rep (l : List α) (hl : ∀ a, a ∈ l → M.H a) : M.H (M.lset l) ∧ M.RepL (M.lset l) l := by
  have hH : ∀ x, x ∈ M.lpairs l 0 → M.H x := by
    intro x hx
    obtain ⟨i, a, ha, rfl⟩ := (M.lpairs_mem l 0 x).mp hx
    exact (M.pr_spec (M.H_num _) (hl a (List.get?_mem ha))).1
  have hs := M.set_spec (M.lpairs l 0) hH
  refine ⟨hs.1, ?_, ?_⟩
  · intro x hx
    rw [lset, hs.2, M.lpairs_mem] at hx
    obtain ⟨i, a, ha, rfl⟩ := hx
    rw [Nat.zero_add]
    exact ⟨i, a, ha, (M.pr_spec (M.H_num _) (hl a (List.get?_mem ha))).2⟩
  · intro i a ha
    refine ⟨M.pr (M.num i) a, ?_, (M.pr_spec (M.H_num _) (hl a (List.get?_mem ha))).2⟩
    rw [lset, hs.2, M.lpairs_mem]
    exact ⟨i, a, ha, by rw [Nat.zero_add]⟩

theorem map_val_inj {dom : α} : ∀ {l l' : List {x // M.mem x dom}}, l.map Subtype.val = l'.map Subtype.val → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Subtype.ext h.1, map_val_inj h.2]

/-! ### 完全性：本当の表から集合 TV・S を作る -/

section Complete
variable {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}}  {s : α} {h : Nat} {S : Nat → Nat → Nat}
  (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Z : M.Zax) (hdom : M.H dom)
  (hs : M.SeqRep4 s h S) (σ0 : Nat → {x // M.mem x dom})

noncomputable def Ns0 (S : Nat → Nat → Nat) (h : Nat) : α := M.set ((NsL S h).map M.num)

theorem Ns0_spec (S : Nat → Nat → Nat) (h : Nat) :
    M.H (M.Ns0 S h) ∧ ∀ x, M.mem x (M.Ns0 S h) ↔ ∃ k, k ∈ NsL S h ∧ x = M.num k := by
  have := M.set_spec ((NsL S h).map M.num)
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨k, _, rfl⟩ := hx; exact M.H_num k)
  refine ⟨this.1, fun x => ?_⟩
  rw [Ns0, this.2, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

include R Z hdom in
theorem asg_ex (S' : Nat → Nat → Nat) (h' : Nat) :
    ∃ A, M.H A ∧ ∀ sg, M.mem sg A ↔ AssignM M.mem (M.Ns0 S' h') dom sg := by
  obtain ⟨hN, hNs⟩ := M.Ns0_spec S' h'
  obtain ⟨P, hP, hPm⟩ := M.prod_ex Z (M.Ns0 S' h') dom hN hdom
  obtain ⟨Pw, hPw, hPwm⟩ := Z.pow P hP
  obtain ⟨A, hA, hAm⟩ := Z.sep Pw (AssignM M.mem (M.Ns0 S' h') dom) hPw
  refine ⟨A, hA, fun sg => ?_⟩
  rw [hAm]
  constructor
  · exact fun h' => h'.2
  · intro ha
    have sub : ∀ q, M.mem q sg → M.mem q P := by
      intro q hq
      obtain ⟨k, a, hp, hk, hd⟩ := ha.1 q hq
      rw [hPm]
      refine ⟨k, a, hk, hd, M.pair_ext hp (M.pr_spec (Z.H_trans k _ hN hk) (R.domH a hd)).2⟩
    obtain ⟨B, hB, hBm⟩ := Z.sep P (fun x => M.mem x sg) hP
    have : B = sg := M.ext B sg (fun x => by rw [hBm]; exact ⟨fun h' => h'.2, fun h' => ⟨sub x h', h'⟩⟩)
    subst this
    exact ⟨(hPwm B).mpr ⟨hB, sub⟩, ha⟩

open Classical in
noncomputable def vT (M5 : G5.Model {x // M.mem x dom}) (S : Nat → Nat → Nat) (h : Nat) (σ0 : Nat → {x // M.mem x dom})
    (i j : Nat) (σ : Nat → {x // M.mem x dom}) : {x // M.mem x dom} :=
  if hh : ∃ v, G5.TVtrue M5 (str S h) i j σ v then Classical.choose hh else σ0 0

open Classical in
noncomputable def vL (M5 : G5.Model {x // M.mem x dom}) (S : Nat → Nat → Nat) (h : Nat)
    (i j n : Nat) (σ : Nat → {x // M.mem x dom}) : List {x // M.mem x dom} :=
  if hh : ∃ ws, G5.TVltrue M5 (str S h) i j n σ ws then Classical.choose hh else []

/-- 表 TV の値。 -/
noncomputable def val (M5 : G5.Model {x // M.mem x dom}) (S : Nat → Nat → Nat) (h : Nat) (σ0 : Nat → {x // M.mem x dom})
    (i j k : Nat) (sg : α) : α :=
  match k with
  | 0 => (M.vT M5 S h σ0 i j (M.τc S h σ0 sg)).1
  | 1 => M.num 0
  | n + 2 => M.lset ((M.vL M5 S h i j n (M.τc S h σ0 sg)).map Subtype.val)

include R in
theorem val_H (i j k : Nat) (sg : α) : M.H (M.val M5 S h σ0 i j k sg) := by
  match k with
  | 0 => exact R.domH _ (M.vT M5 S h σ0 i j _).2
  | 1 => exact M.H_num 0
  | n + 2 =>
    refine (M.lset_rep _ ?_).1
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    exact R.domH _ b.2

noncomputable def tvE (i j k : Nat) (sg v : α) : α := M.pr (M.pr (M.pr (M.num i) (M.num j)) (M.num k)) (M.pr sg v)

theorem tvE_H {i j k : Nat} {sg v : α} (hsg : M.H sg) (hv : M.H v) : M.H (M.tvE i j k sg v) ∧
    Pair M.mem (M.tvE i j k sg v) (M.pr (M.pr (M.num i) (M.num j)) (M.num k)) (M.pr sg v) ∧
    Pair M.mem (M.pr (M.pr (M.num i) (M.num j)) (M.num k)) (M.pr (M.num i) (M.num j)) (M.num k) ∧
    Pair M.mem (M.pr (M.num i) (M.num j)) (M.num i) (M.num j) ∧ Pair M.mem (M.pr sg v) sg v := by
  have h1 := M.pr_spec (M.H_num i) (M.H_num j)
  have h2 := M.pr_spec h1.1 (M.H_num k)
  have h3 := M.pr_spec hsg hv
  have h4 := M.pr_spec h2.1 h3.1
  exact ⟨h4.1, h4.2, h2.2, h1.2, h3.2⟩

include R Z hdom in
theorem tv_ex : ∃ TV, M.H TV ∧ ∀ e, M.mem e TV ↔
    ∃ i j k sg, PB S h i j k ∧ AssignM M.mem (M.Ns0 S h) dom sg ∧ e = M.tvE i j k sg (M.val M5 S h σ0 i j k sg) := by
  obtain ⟨A, hA, hAm⟩ := M.asg_ex R Z hdom S h
  have hsgH : ∀ sg, M.mem sg A → M.H sg := fun sg hsg => Z.H_trans sg A hA hsg
  have himg : ∀ r : Nat × Nat × Nat, ∃ B, M.H B ∧ ∀ y, M.mem y B ↔ ∃ x, M.mem x A ∧
      y = M.tvE r.1 r.2.1 r.2.2 x (M.val M5 S h σ0 r.1 r.2.1 r.2.2 x) :=
    fun r => Z.repl A _ hA (fun x hx => (M.tvE_H (hsgH x hx) (M.val_H R σ0 _ _ _ x)).1)
  let img := fun r => Classical.choose (himg r)
  have himgS := fun r => Classical.choose_spec (himg r)
  have := M.set_spec ((rows S h).map img) (by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨r, _, rfl⟩ := hx; exact (himgS r).1)
  obtain ⟨U, hU, hUm⟩ := Z.union _ this.1
  refine ⟨U, hU, fun e => ?_⟩
  rw [hUm]
  constructor
  · rintro ⟨y, hy, he⟩
    rw [this.2, List.mem_map] at hy
    obtain ⟨⟨i, j, k⟩, hr, rfl⟩ := hy
    obtain ⟨x, hx, rfl⟩ := ((himgS _).2 e).mp he
    exact ⟨i, j, k, x, (rows_mem S h i j k).mp hr, (hAm x).mp hx, rfl⟩
  · rintro ⟨i, j, k, sg, hpb, hsg, rfl⟩
    exact ⟨img (i, j, k), (this.2 _).mpr (List.mem_map.mpr ⟨(i, j, k), (rows_mem S h i j k).mpr hpb, rfl⟩),
      ((himgS (i, j, k)).2 _).mpr ⟨sg, (hAm sg).mpr hsg, rfl⟩⟩

include R Z hdom in
theorem ss_ex : ∃ SS, M.H SS ∧ ∀ e, M.mem e SS ↔
    ∃ i j sg, PB S h i j 1 ∧ AssignM M.mem (M.Ns0 S h) dom sg ∧
      G5.Strue M5 (str S h) i j (M.τc S h σ0 sg) ∧ e = M.pr (M.pr (M.num i) (M.num j)) sg := by
  obtain ⟨A, hA, hAm⟩ := M.asg_ex R Z hdom S h
  have hsgH : ∀ sg, M.mem sg A → M.H sg := fun sg hsg => Z.H_trans sg A hA hsg
  have hsub : ∀ r : Nat × Nat, ∃ B, M.H B ∧ ∀ x, M.mem x B ↔ M.mem x A ∧
      G5.Strue M5 (str S h) r.1 r.2 (M.τc S h σ0 x) := fun r => Z.sep A _ hA
  let sub := fun r => Classical.choose (hsub r)
  have hsubS := fun r => Classical.choose_spec (hsub r)
  have himg : ∀ r : Nat × Nat, ∃ B, M.H B ∧ ∀ y, M.mem y B ↔ ∃ x, M.mem x (sub r) ∧
      y = M.pr (M.pr (M.num r.1) (M.num r.2)) x := fun r => Z.repl (sub r) _ (hsubS r).1 (fun x hx =>
        (M.pr_spec (M.pr_spec (M.H_num _) (M.H_num _)).1 (hsgH x (((hsubS r).2 x).mp hx).1)).1)
  let img := fun r => Classical.choose (himg r)
  have himgS := fun r => Classical.choose_spec (himg r)
  let rs := (rows S h).map fun r => (r.1, r.2.1)
  have := M.set_spec ((rows S h).filterMap fun r => if r.2.2 = 1 then some (img (r.1, r.2.1)) else none) (by
    intro x hx; simp only [List.mem_filterMap] at hx; obtain ⟨r, _, hr⟩ := hx
    split at hr
    · cases hr; exact (himgS _).1
    · cases hr)
  obtain ⟨U, hU, hUm⟩ := Z.union _ this.1
  refine ⟨U, hU, fun e => ?_⟩
  rw [hUm]
  constructor
  · rintro ⟨y, hy, he⟩
    rw [this.2, List.mem_filterMap] at hy
    obtain ⟨⟨i, j, k⟩, hr, hy⟩ := hy
    split at hy
    · rename_i hk
      cases hy
      simp only at hk
      subst hk
      obtain ⟨x, hx, rfl⟩ := ((himgS _).2 e).mp he
      obtain ⟨hxA, hst⟩ := ((hsubS _).2 x).mp hx
      exact ⟨i, j, x, (rows_mem S h i j 1).mp hr, (hAm x).mp hxA, hst, rfl⟩
    · cases hy
  · rintro ⟨i, j, sg, hpb, hsg, hst, rfl⟩
    refine ⟨img (i, j), (this.2 _).mpr (List.mem_filterMap.mpr ⟨(i, j, 1), (rows_mem S h i j 1).mpr hpb, by simp⟩), ?_⟩
    exact ((himgS (i, j)).2 _).mpr ⟨sg, ((hsubS (i, j)).2 sg).mpr ⟨(hAm sg).mpr hsg, hst⟩, rfl⟩

end Complete

section Complete2
variable {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}}  {s : α} {h : Nat} {S : Nat → Nat → Nat}
  (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Z : M.Zax) (hdom : M.H dom)
  (hs : M.SeqRep4 s h S) (σ0 : Nat → {x // M.mem x dom})
  {TV SS : α}
  (hTVm : ∀ e, M.mem e TV ↔ ∃ i j k sg, PB S h i j k ∧ AssignM M.mem (M.Ns0 S h) dom sg ∧
      e = M.tvE i j k sg (M.val M5 S h σ0 i j k sg))
  (hSSm : ∀ e, M.mem e SS ↔ ∃ i j sg, PB S h i j 1 ∧ AssignM M.mem (M.Ns0 S h) dom sg ∧
      G5.Strue M5 (str S h) i j (M.τc S h σ0 sg) ∧ e = M.pr (M.pr (M.num i) (M.num j)) sg)

include R Z hdom in
theorem assign_H {sg : α} (ha : AssignM M.mem (M.Ns0 S h) dom sg) : M.H sg := by
  obtain ⟨A, hA, hAm⟩ := M.asg_ex R Z hdom S h
  exact Z.H_trans sg A hA ((hAm sg).mpr ha)

include R Z hdom hTVm in
theorem tv_char {sg : α} (hA : AssignM M.mem (M.Ns0 S h) dom sg) (i j k : Nat) (v : α) :
    Tv M.mem TV (M.num i) (M.num j) (fun x => x = M.num k) sg (fun x => x = v) ↔
      PB S h i j k ∧ v = M.val M5 S h σ0 i j k sg := by
  constructor
  · rintro ⟨e, he, a, b, hp, ⟨ij, kk, ha, hij, hkk⟩, sg2, v', hb, hsg2, hv'⟩
    obtain ⟨i', j', k', sg', hpb, hA', rfl⟩ := (hTVm e).mp he
    obtain ⟨_, he1, he2, he3, he4⟩ := M.tvE_H (M.assign_H R Z hdom hA') (M.val_H R σ0 i' j' k' sg')
    obtain ⟨rfl, rfl⟩ := M.pair_unique hp he1
    obtain ⟨rfl, rfl⟩ := M.pair_unique ha he2
    obtain ⟨e1, e2⟩ := M.pair_unique hij he3
    obtain ⟨rfl, rfl⟩ := M.pair_unique hb he4
    subst hsg2; subst hv'
    have q1 := M.num_inj e1; have q2 := M.num_inj e2; have q3 := M.num_inj hkk
    subst q1; subst q2; subst q3
    exact ⟨hpb, rfl⟩
  · rintro ⟨hpb, rfl⟩
    obtain ⟨_, he1, he2, he3, he4⟩ := M.tvE_H (k := k) (i := i) (j := j) (M.assign_H R Z hdom hA) (M.val_H R σ0 i j k sg)
    exact ⟨_, (hTVm _).mpr ⟨i, j, k, sg, hpb, hA, rfl⟩, _, _, he1, ⟨_, _, he2, he3, rfl⟩, _, _, he4, rfl, rfl⟩

include R Z hdom hTVm in
theorem tvall_char {sg : α} (i j k : Nat) (vp : α → Prop) (hv : PB S h i j k → vp (M.val M5 S h σ0 i j k sg)) :
    TvAll M.mem TV (M.num i) (M.num j) (fun x => x = M.num k) sg vp := by
  intro e he
  obtain ⟨i', j', k', sg', hpb, hA', rfl⟩ := (hTVm e).mp he
  obtain ⟨_, he1, he2, he3, he4⟩ := M.tvE_H (M.assign_H R Z hdom hA') (M.val_H R σ0 i' j' k' sg')
  refine ⟨_, _, he1, ?_⟩
  rintro ⟨ij, kk, ha, hij, hkk⟩
  obtain ⟨rfl, rfl⟩ := M.pair_unique ha he2
  obtain ⟨e1, e2⟩ := M.pair_unique hij he3
  refine ⟨_, _, he4, fun hsg => ?_⟩
  subst hsg
  have q1 := M.num_inj e1; have q2 := M.num_inj e2; have q3 := M.num_inj hkk
  subst q1; subst q2; subst q3
  exact hv hpb

include R Z hdom hSSm in
theorem ins_char {sg : α} (hA : AssignM M.mem (M.Ns0 S h) dom sg) (i j : Nat) :
    InS M.mem SS (M.num i) (M.num j) sg ↔ PB S h i j 1 ∧ G5.Strue M5 (str S h) i j (M.τc S h σ0 sg) := by
  constructor
  · rintro ⟨e, he, ij, sg2, hp, hij, hsg2⟩
    obtain ⟨i', j', sg', hpb, hA', hst, rfl⟩ := (hSSm e).mp he
    have h1 := M.pr_spec (M.H_num i') (M.H_num j')
    have h2 := M.pr_spec h1.1 (M.assign_H R Z hdom hA')
    obtain ⟨rfl, rfl⟩ := M.pair_unique hp h2.2
    obtain ⟨e1, e2⟩ := M.pair_unique hij h1.2
    subst hsg2
    have q1 := M.num_inj e1; have q2 := M.num_inj e2
    subst q1; subst q2
    exact ⟨hpb, hst⟩
  · rintro ⟨hpb, hst⟩
    have h1 := M.pr_spec (M.H_num i) (M.H_num j)
    have h2 := M.pr_spec h1.1 (M.assign_H R Z hdom hA)
    exact ⟨_, (hSSm _).mpr ⟨i, j, sg, hpb, hA, hst, rfl⟩, _, _, h2.2, h1.2, rfl⟩

end Complete2

section Complete3
variable {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}} {s : α} {h : Nat} {S : Nat → Nat → Nat}
  {TV SS : α}

theorem vT_spec (σ0 : Nat → {x // M.mem x dom}) {i j : Nat} {σ : Nat → {x // M.mem x dom}}
    (hp : Parses (str S h) i j 0) : G5.TVtrue M5 (str S h) i j σ (M.vT M5 S h σ0 i j σ) := by
  have hex := (G5.tvtrue_ok M5 (str S h) i j hp σ).1
  unfold vT; rw [dif_pos hex]; exact Classical.choose_spec hex

theorem vL_spec {i j n : Nat} {σ : Nat → {x // M.mem x dom}} (hp : Parses (str S h) i j (n + 2)) :
    G5.TVltrue M5 (str S h) i j n σ (M.vL M5 S h i j n σ) := by
  have hex := (G5.tvltrue_ok M5 (str S h) i j n hp σ).1
  unfold vL; rw [dif_pos hex]; exact Classical.choose_spec hex

theorem vL_length {i j n : Nat} {σ : Nat → {x // M.mem x dom}} (hp : Parses (str S h) i j (n + 2)) :
    (M.vL M5 S h i j n σ).length = n := by
  have hex := (G5.tvltrue_ok M5 (str S h) i j n hp σ).1
  unfold vL; rw [dif_pos hex]
  obtain ⟨ts, _, hlen, _, _, he⟩ := Classical.choose_spec hex
  rw [he, terms_eval_length]; exact hlen

theorem vL_rep (R : M.Rep5T dom E Cn Fn Rel M5 S h) (i j n : Nat) (σ : Nat → {x // M.mem x dom}) :
    M.RepL (M.lset ((M.vL M5 S h i j n σ).map Subtype.val)) ((M.vL M5 S h i j n σ).map Subtype.val) := by
  refine (M.lset_rep _ ?_).2
  intro a ha; simp only [List.mem_map] at ha; obtain ⟨b, _, rfl⟩ := ha; exact R.domH _ b.2

section
variable (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Z : M.Zax) (hdom : M.H dom) (σ0 : Nat → {x // M.mem x dom})
  (hTVm : ∀ e, M.mem e TV ↔ ∃ i j k sg, PB S h i j k ∧ AssignM M.mem (M.Ns0 S h) dom sg ∧
      e = M.tvE i j k sg (M.val M5 S h σ0 i j k sg))
  (hSSm : ∀ e, M.mem e SS ↔ ∃ i j sg, PB S h i j 1 ∧ AssignM M.mem (M.Ns0 S h) dom sg ∧
      G5.Strue M5 (str S h) i j (M.τc S h σ0 sg) ∧ e = M.pr (M.pr (M.num i) (M.num j)) sg)
  {sg : α} (hA : AssignM M.mem (M.Ns0 S h) dom sg) (hsgσ : M.sgT S h (M.τc S h σ0 sg) = sg)
include R Z hdom hTVm hA hsgσ

/-- 標準の割当て σc での、集合から作った G5 の表と本当の表の一致（行の終わりが h 以下）。 -/
theorem TVt5_c (a b : Nat) (v : {x // M.mem x dom}) (hb : b ≤ h) :
    M.TVt5 S h TV a b (M.τc S h σ0 sg) v ↔ G5.TVtrue M5 (str S h) a b (M.τc S h σ0 sg) v := by
  unfold TVt5
  rw [hsgσ, M.tv_char R Z hdom σ0 hTVm hA a b 0 v.1]
  constructor
  · rintro ⟨hpb, hv⟩
    have hex := (G5.tvtrue_ok M5 (str S h) a b hpb.1 (M.τc S h σ0 sg)).1
    rw [show v = M.vT M5 S h σ0 a b (M.τc S h σ0 sg) from Subtype.ext hv]
    unfold vT; rw [dif_pos hex]; exact Classical.choose_spec hex
  · intro ht
    obtain ⟨tm, hw, ho, he, hev⟩ := ht
    have hp : Parses (str S h) a b 0 := ⟨tm, hw, ho, he⟩
    have hex := (G5.tvtrue_ok M5 (str S h) a b hp (M.τc S h σ0 sg)).1
    have hsp : G5.TVtrue M5 (str S h) a b (M.τc S h σ0 sg) (M.vT M5 S h σ0 a b (M.τc S h σ0 sg)) := by
      unfold vT; rw [dif_pos hex]; exact Classical.choose_spec hex
    exact ⟨⟨hp, hb⟩, congrArg Subtype.val (tvtrue_unique M5 (str S h) ⟨tm, hw, ho, he, hev⟩ hsp)⟩

theorem TVl5_c (a b n : Nat) (ws : List {x // M.mem x dom}) (hb : b ≤ h) :
    M.TVl5 S h TV a b n (M.τc S h σ0 sg) ws ↔ G5.TVltrue M5 (str S h) a b n (M.τc S h σ0 sg) ws := by
  unfold TVl5
  rw [hsgσ]
  simp only [M.tv_char R Z hdom σ0 hTVm hA a b (n + 2)]
  constructor
  · rintro ⟨w, ⟨hpb, rfl⟩, hw⟩
    have hex := (G5.tvltrue_ok M5 (str S h) a b n hpb.1 (M.τc S h σ0 sg)).1
    have hsp : G5.TVltrue M5 (str S h) a b n (M.τc S h σ0 sg) (M.vL M5 S h a b n (M.τc S h σ0 sg)) := by
      unfold vL; rw [dif_pos hex]; exact Classical.choose_spec hex
    have e := M.map_val_inj (M.repL_unique (M.vL_rep R a b n _) hw)
    rw [← e]; exact hsp
  · intro ht
    obtain ⟨ts, hw, hn, ho, he, hev⟩ := ht
    have hp : Parses (str S h) a b (n + 2) := ⟨ts, hw, hn, ho, he⟩
    have hex := (G5.tvltrue_ok M5 (str S h) a b n hp (M.τc S h σ0 sg)).1
    have hsp : G5.TVltrue M5 (str S h) a b n (M.τc S h σ0 sg) (M.vL M5 S h a b n (M.τc S h σ0 sg)) := by
      unfold vL; rw [dif_pos hex]; exact Classical.choose_spec hex
    have e := tvltrue_unique M5 (str S h) ⟨ts, hw, hn, ho, he, hev⟩ hsp
    refine ⟨_, ⟨⟨hp, hb⟩, rfl⟩, ?_⟩
    show M.RepL (M.lset ((M.vL M5 S h a b n (M.τc S h σ0 sg)).map Subtype.val)) (ws.map Subtype.val)
    rw [e]; exact M.vL_rep R a b n _

end

section
variable (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Z : M.Zax) (hdom : M.H dom) (σ0 : Nat → {x // M.mem x dom})
  (hTVm : ∀ e, M.mem e TV ↔ ∃ i j k sg, PB S h i j k ∧ AssignM M.mem (M.Ns0 S h) dom sg ∧
      e = M.tvE i j k sg (M.val M5 S h σ0 i j k sg))
  (hSSm : ∀ e, M.mem e SS ↔ ∃ i j sg, PB S h i j 1 ∧ AssignM M.mem (M.Ns0 S h) dom sg ∧
      G5.Strue M5 (str S h) i j (M.τc S h σ0 sg) ∧ e = M.pr (M.pr (M.num i) (M.num j)) sg)

include R Z hdom hSSm in
theorem S5_c (σ' : Nat → {x // M.mem x dom}) (hA' : AssignM M.mem (M.Ns0 S h) dom (M.sgT S h σ'))
    (hcan : M.τc S h σ0 (M.sgT S h σ') = σ') (a b : Nat) (hb : b ≤ h) :
    M.S5 S h SS a b σ' ↔ G5.Strue M5 (str S h) a b σ' := by
  unfold S5
  rw [M.ins_char R Z hdom σ0 hSSm hA' a b, hcan]
  constructor
  · exact fun h' => h'.2
  · intro hst
    have hst' := hst
    obtain ⟨φ, hw, ho, he, _⟩ := hst'
    exact ⟨⟨⟨φ, hw, ho, he⟩, hb⟩, hst⟩

include R Z hdom hTVm in
theorem tvok (hs : M.SeqRep4 s h S) : TvOk M.mem s dom Cn Fn (M.Ns0 S h) (M.ctab S h) (M.num 0) TV := by
  have hNs := (M.Ns0_spec S h).2
  intro p hp
  obtain ⟨i, j, k, hpb, rfl⟩ := (M.ctab_mem S h p).mp hp
  refine ⟨M.num i, M.num j, M.num k, (M.nt3_spec i j k).2, ?_, ?_⟩
  · intro hk sg hA
    have := M.num_inj hk; subst this
    have hsgσ := M.sgT_τc S h σ0 R.domH hNs hA
    refine ⟨(M.tv_split _ _ _ _ _ _).mpr ⟨_, (M.tv_char R Z hdom σ0 hTVm hA i j 0 _).mpr ⟨hpb, rfl⟩, rfl⟩, ?_⟩
    refine M.tvall_char R Z hdom σ0 hTVm i j 0 _ (fun _ => ?_)
    let σc := M.τc S h σ0 sg
    have hex := (G5.tvtrue_ok M5 (str S h) i j hpb.1 σc).1
    have hsp : G5.TVtrue M5 (str S h) i j σc (M.vT M5 S h σ0 i j σc) := by
      unfold vT; rw [dif_pos hex]; exact Classical.choose_spec hex
    have htc := (G5.tvtrue_ok M5 (str S h) i j hpb.1 σc).2 _ hsp
    have htc' : G5.termClause M5 (str S h) (M.TVl5 S h TV) i j σc (M.vT M5 S h σ0 i j σc) :=
      termClause_mono M5 (str S h) (fun a b n ws hb hw =>
        (M.TVl5_c R Z hdom σ0 hTVm hA hsgσ a b n ws (by have := hpb.2; omega)).mpr hw) htc
    have key := (M.termClause_iff R hs TV i j σc _ (fun f a j1 w _ _ htw => by
      rw [hsgσ, M.tv_char R Z hdom σ0 hTVm hA (i + 2) j1 (a + 2) w] at htw
      obtain ⟨hpb2, rfl⟩ := htw
      exact ⟨_, M.vL_length hpb2.1, M.vL_rep R (i + 2) j1 a _⟩)).mpr htc'
    rw [hsgσ] at key
    exact key
  · intro nn1 _ n _ hplus sg hA
    obtain ⟨n', rfl, rfl⟩ := M.plus2_num hplus
    have hsgσ := M.sgT_τc S h σ0 R.domH hNs hA
    refine ⟨(M.tv_split _ _ _ _ _ _).mpr ⟨_, (M.tv_char R Z hdom σ0 hTVm hA i j _ _).mpr ⟨hpb, rfl⟩, rfl⟩, ?_⟩
    refine M.tvall_char R Z hdom σ0 hTVm i j _ _ (fun _ => ?_)
    let σc := M.τc S h σ0 sg
    have hex := (G5.tvltrue_ok M5 (str S h) i j n' hpb.1 σc).1
    have hsp : G5.TVltrue M5 (str S h) i j n' σc (M.vL M5 S h i j n' σc) := by
      unfold vL; rw [dif_pos hex]; exact Classical.choose_spec hex
    have hlc := (G5.tvltrue_ok M5 (str S h) i j n' hpb.1 σc).2 _ hsp
    have hlc' : G5.listClause (M.Cn (M.ctab S h)) (M.TVt5 S h TV) (M.TVl5 S h TV) i j n' σc (M.vL M5 S h i j n' σc) :=
      listClause_mono (C := Parses (str S h))
        (fun a b k hb hc => (M.cn_ctab S h a b k).mpr ⟨hc, by have := hpb.2; omega⟩)
        (fun a b v hb hv => (M.TVt5_c R Z hdom σ0 hTVm hA hsgσ a b v (by have := hpb.2; omega)).mpr hv)
        (fun a b n ws hb hw => (M.TVl5_c R Z hdom σ0 hTVm hA hsgσ a b n ws (by have := hpb.2; omega)).mpr hw) hlc
    have key := (M.listClause_iff R TV (M.ctab S h) i j n' σc _ _ (M.vL_rep R i j n' σc)).mpr hlc'
    rw [hsgσ] at key
    exact key

include R Z hdom hTVm hSSm in
theorem sok (hs : M.SeqRep4 s h S) :
    SOk M.mem s dom E Rel (M.Ns0 S h) (M.ctab S h) (M.num 0) (M.num 1) TV SS := by
  have hNs := (M.Ns0_spec S h).2
  intro p hp
  obtain ⟨i, j, k, hpb, rfl⟩ := (M.ctab_mem S h p).mp hp
  refine ⟨M.num i, M.num j, M.num k, (M.nt3_spec i j k).2, fun hk sg hA => ?_⟩
  have := M.num_inj hk; subst this
  have hsgσ := M.sgT_τc S h σ0 R.domH hNs hA
  let σc := M.τc S h σ0 sg
  have hjh := hpb.2
  have hτH : ∀ (τ' : Nat → {x // M.mem x dom}) k, M.H (τ' k).1 := fun τ' k => R.domH _ (τ' k).2
  have hAs : ∀ τ' : Nat → {x // M.mem x dom}, AssignM M.mem (M.Ns0 S h) dom (M.sgT S h τ') :=
    fun τ' => M.assign_sgOf (NsL S h) (fun k => (τ' k).1) (hτH τ') _ dom hNs (fun k => (τ' k).2)
  have key : InS M.mem SS (M.num i) (M.num j) (M.sgT S h σc) ↔
      FormClauseM M.mem s dom E Rel (M.Ns0 S h) (M.ctab S h) (M.num 0) (M.num 1) TV SS (M.num i) (M.num j) (M.sgT S h σc) := by
    rw [M.formClause_iff R hs TV (M.ctab S h) SS (M.Ns0 S h) hNs i j σc
      (fun a b v _ hv => by
        rw [hsgσ, M.tv_char R Z hdom σ0 hTVm hA a b 0 v] at hv
        obtain ⟨_, rfl⟩ := hv
        exact (M.vT M5 S h σ0 a b _).2)
      (fun r a j1 w _ _ htw => by
        rw [hsgσ, M.tv_char R Z hdom σ0 hTVm hA (i + 2) j1 (a + 2) w] at htw
        obtain ⟨hpb2, rfl⟩ := htw
        exact ⟨_, M.vL_length hpb2.1, M.vL_rep R (i + 2) j1 a _⟩)]
    show M.S5 S h SS i j σc ↔ _
    rw [M.S5_c R Z hdom σ0 hSSm σc (hAs σc) (by show M.τc S h σ0 (M.sgT S h (M.τc S h σ0 sg)) = _; rw [hsgσ]) i j hjh,
      G5.strue_ok M5 (str S h) h (str_fin S h) i j hpb.1 σc]
    apply formClause_congr
    · intro a b k hb; exact ((M.cn_ctab S h a b k).trans ⟨fun h' => h'.1, fun h' => ⟨h', by omega⟩⟩).symm
    · intro a b v hb; exact (M.TVt5_c R Z hdom σ0 hTVm hA hsgσ a b v (by omega)).symm
    · intro a b n ws hb; exact (M.TVl5_c R Z hdom σ0 hTVm hA hsgσ a b n ws (by omega)).symm
    · intro a b hb
      exact (M.S5_c R Z hdom σ0 hSSm σc (hAs σc) (by show M.τc S h σ0 (M.sgT S h (M.τc S h σ0 sg)) = _; rw [hsgσ]) a b (by omega)).symm
    · intro a b kk x hb hk
      have hkL : kk ∈ NsL S h := by
        rw [str_some] at hk
        exact (mem_NsL S h kk).mpr ⟨i + 1, hk.1, hk.2⟩
      exact (M.S5_c R Z hdom σ0 hSSm _ (hAs _) (M.τc_upd S h σ0 R.domH hNs hA kk hkL x) a b (by omega)).symm
  rw [hsgσ] at key
  exact key

end

end Complete3


/-! ### 主定理：sat の意味 -/

section SatMain
variable {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}}
  {s : α} {h : Nat} {S : Nat → Nat → Nat}

/-- 完全性：φ が τ の下で真なら、sat の式が sgT τ で成り立つ。 -/
theorem sat_complete (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Z : M.Zax) (hdom : M.H dom) (hs : M.SeqRep4 s h S)
    (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
    (τ : Nat → {x // M.mem x dom}) (hsat : φ.sat M5 τ) :
    SatM M.mem s dom E Cn Fn Rel (M.sgT S h τ) := by
  obtain ⟨_, hNs⟩ := M.Ns0_spec S h
  obtain ⟨TV, _, hTVm⟩ := M.tv_ex R Z hdom (h := h) (S := S) τ
  obtain ⟨SS, _, hSSm⟩ := M.ss_ex R Z hdom (h := h) (S := S) τ
  have hτH : ∀ k, M.H (τ k).1 := fun k => R.domH _ (τ k).2
  have hA : AssignM M.mem (M.Ns0 S h) dom (M.sgT S h τ) :=
    M.assign_sgOf (NsL S h) (fun k => (τ k).1) hτH _ dom hNs (fun k => (τ k).2)
  have hpb : PB S h 0 h 1 := ⟨⟨φ, hw, ho, by omega⟩, Nat.le_refl _⟩
  have hroot : M.Cn (M.ctab S h) 0 h 1 := (M.cn_ctab S h 0 h 1).mpr hpb
  have hC := M.ctab_ok hs
  have hTV := M.tvok R Z hdom τ hTVm hs
  have hSo := M.sok R Z hdom τ hTVm hSSm hs
  refine ⟨M.num 0, (M.empty_iff _).mpr rfl, M.num 1, (M.succ_num_iff 0 _).mpr rfl, M.num h, M.seqWith4 hs,
    M.Ns0 S h, (M.varset_iff hs _).mpr hNs, hA, M.ctab S h, hroot, hC, TV, hTV, SS, hSo, ?_⟩
  exact (M.tables_sat R hs φ hw ho hl hNs hroot hC hTV hSo τ).mpr hsat

/-- 充足関係の層の主定理：s が論理式 φ を表し、集合 dom, E, Cn, Fn, Rel が構造 M5 を表すとき、
    sat(s, dom, E, Cn, Fn, Rel, sgT τ) ⟺ φ は τ の下で（Tarski の意味で）真。 -/
theorem sat_iff (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Z : M.Zax) (hdom : M.H dom) (hs : M.SeqRep4 s h S)
    (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
    (τ : Nat → {x // M.mem x dom}) :
    SatM M.mem s dom E Cn Fn Rel (M.sgT S h τ) ↔ φ.sat M5 τ :=
  ⟨M.sat_sound R hs φ hw ho hl τ, M.sat_complete R Z hdom hs φ hw ho hl τ⟩

/-- extended 版：σ の割当て集合が、s の変数を含むより多くの変数 L の上のものでもよい。 -/
theorem satExt_iff (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Z : M.Zax) (hdom : M.H dom) (hs : M.SeqRep4 s h S)
    (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
    (τ : Nat → {x // M.mem x dom}) (L : List Nat) (hL : ∀ k, k ∈ NsL S h → k ∈ L) :
    SatExtM M.mem s dom E Cn Fn Rel (M.sgOf L (fun k => (τ k).1)) ↔ φ.sat M5 τ := by
  have hτH : ∀ k, M.H (τ k).1 := fun k => R.domH _ (τ k).2
  constructor
  · rintro ⟨K0, he0, K1, he1, h', hsw, Ns, hvs, sr, hA, hsub, C, hroot, hC, TV, hTV, SS, hSo, hin⟩
    rw [M.empty_iff] at he0; subst he0
    rw [M.succ_num_iff] at he1; subst he1
    have eh := M.seqWith_dom (SeqRep4.dom M hs) hsw; subst eh
    have hNs := (M.varset_iff hs Ns).mp hvs
    have esr : sr = M.sgT S h τ := by
      apply M.ext
      intro q
      unfold sgT
      rw [M.sgOf_spec _ _ hτH]
      constructor
      · intro hq
        obtain ⟨kk, a, hp, hkk, _⟩ := hA.1 q hq
        obtain ⟨k, hk, rfl⟩ := (hNs kk).mp hkk
        obtain ⟨k', _, e1, rfl⟩ := M.sgOf_pair L _ hτH (hsub q hq) hp
        have := M.num_inj e1; subst this
        exact ⟨k, hk, M.pair_ext hp (M.pr_spec (M.H_num k) (hτH k)).2⟩
      · rintro ⟨k, hk, rfl⟩
        obtain ⟨q', hq', a, hp⟩ := hA.2.1 (M.num k) ((hNs _).mpr ⟨k, hk, rfl⟩)
        obtain ⟨k', _, e1, rfl⟩ := M.sgOf_pair L _ hτH (hsub q' hq') hp
        have := M.num_inj e1; subst this
        rw [← M.pair_ext hp (M.pr_spec (M.H_num k) (hτH k)).2]; exact hq'
    subst esr
    exact (M.tables_sat R hs φ hw ho hl hNs hroot hC hTV hSo τ).mp hin
  · intro hsat
    obtain ⟨K0, he0, K1, he1, h', hsw, Ns, hvs, hA, C, hroot, hC, TV, hTV, SS, hSo, hin⟩ :=
      M.sat_complete R Z hdom hs φ hw ho hl τ hsat
    refine ⟨K0, he0, K1, he1, h', hsw, Ns, hvs, M.sgT S h τ, hA, ?_, C, hroot, hC, TV, hTV, SS, hSo, hin⟩
    intro q hq
    unfold sgT at hq
    rw [M.sgOf_spec _ _ hτH] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    exact (M.sgOf_spec L _ hτH _).mpr ⟨k, hL k hk, rfl⟩

/-- sat の式（Lean で組み立てた式 full_sat について。生成プログラムの出力との一致は tr_expand_check.py で確認）。 -/
theorem full_sat_nat (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Z : M.Zax) (hdom : M.H dom) (hs : M.SeqRep4 s h S)
    (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
    (τ : Nat → {x // M.mem x dom}) (Rr : Nm → List α → Prop) (e : Nat → α)
    (e0 : e 0 = s) (e1 : e 1 = dom) (e2 : e 2 = E) (e3 : e 3 = Cn) (e4 : e 4 = Fn) (e5 : e 5 = Rel)
    (e6 : e 6 = M.sgT S h τ) :
    ev M.mem Rr full_sat e ↔ φ.sat M5 τ := by
  rw [mean_full_sat]
  show SatM M.mem (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) ↔ _
  rw [e0, e1, e2, e3, e4, e5, e6]
  exact M.sat_iff R Z hdom hs φ hw ho hl τ

/-- sat の extended 版（Lean で組み立てた式 full_sat_ext について。Python の出力との記号列の照合は Lean では行っていない）。 -/
theorem full_sat_ext_nat (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Z : M.Zax) (hdom : M.H dom) (hs : M.SeqRep4 s h S)
    (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
    (τ : Nat → {x // M.mem x dom}) (L : List Nat) (hL : ∀ k, k ∈ NsL S h → k ∈ L)
    (Rr : Nm → List α → Prop) (e : Nat → α)
    (e0 : e 0 = s) (e1 : e 1 = dom) (e2 : e 2 = E) (e3 : e 3 = Cn) (e4 : e 4 = Fn) (e5 : e 5 = Rel)
    (e6 : e 6 = M.sgOf L (fun k => (τ k).1)) :
    ev M.mem Rr full_sat_ext e ↔ φ.sat M5 τ := by
  rw [mean_full_sat_ext]
  show SatExtM M.mem (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) ↔ _
  rw [e0, e1, e2, e3, e4, e5, e6]
  exact M.satExt_iff R Z hdom hs φ hw ho hl τ L hL

end SatMain

#print axioms sat_iff
#print axioms full_sat_nat
#print axioms full_sat_ext_nat

end Model
end Tr
