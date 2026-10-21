/-
  別紙 G の補題 G13（L の段階の整列順序）の順序に関する部分の形式化（改訂38）。

  ・lexN_wf：長さが同じ有限列の辞書式順序は、要素の順序が整礎なら整礎（パラメータ τ の比較）。
  ・定義の順序 ≺ = (式の番号, パラメータ列) の辞書式順序。整礎・推移的・（同じ番号なら同じ長さのとき）全順序。
  ・newLess a b :=「a のある定義が b のどの定義よりも ≺ で小さい」（生成プログラムの new_less の形）。
      newLess_iff_min：これは「a の最小の定義 ≺ b の最小の定義」と同値。
      newLess は新しい元の上の整礎な狭義全順序。
  ・succ_wf：古い元を前に、新しい元を newLess で並べた順序は整礎（次の段 <_{β+1}）。
  ・union_wf：終切片への延長の列の和は整礎（極限段階）。
  （集合論的な符号化と Def(X) の中身は扱わない。ここで示すのは、G13 の証明が使う順序の性質である。）
-/
namespace G13

-- ---------- 長さが同じ列の辞書式順序 ----------
def lexR {α : Type} (R : α → α → Prop) : List α → List α → Prop
  | x :: l, y :: l' => R x y ∨ (x = y ∧ lexR R l l')
  | _, _ => False

def lexN {α : Type} (R : α → α → Prop) (l l' : List α) : Prop := l.length = l'.length ∧ lexR R l l'

theorem lexN_wf {α : Type} (R : α → α → Prop) (wf : WellFounded R) : WellFounded (lexN R) := by
  constructor
  suffices H : ∀ n (l : List α), l.length = n → Acc (lexN R) l from fun l => H _ l rfl
  intro n
  induction n with
  | zero =>
    intro l hl
    constructor
    intro y ⟨hlen, hr⟩
    cases l with
    | nil => cases y <;> simp [lexR] at hr
    | cons _ _ => simp at hl
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp at hl
    | cons x t =>
      have ht : t.length = n := by simpa using hl
      -- 先頭について整礎な帰納法、その中で尾についての Acc に関する帰納法
      suffices H : ∀ x (t : List α), t.length = n → Acc (lexN R) (x :: t) from H x t ht
      intro x
      induction x using wf.induction with
      | _ x ihx =>
      intro t ht
      have acct := ih t ht
      induction acct with
      | intro t _ iht =>
      constructor
      intro y ⟨hlen, hr⟩
      cases y with
      | nil => simp [lexR] at hr
      | cons y t' =>
        have ht' : t'.length = n := by simp at hlen; omega
        simp only [lexR] at hr
        rcases hr with hyx | ⟨e, hr'⟩
        · exact ihx y hyx t' ht'
        · subst e
          exact iht t' ⟨by omega, hr'⟩ ht'

theorem lexR_trans {α : Type} (R : α → α → Prop) (tr : ∀ a b c, R a b → R b c → R a c) :
    ∀ (l1 l2 l3 : List α), lexR R l1 l2 → lexR R l2 l3 → lexR R l1 l3
  | x :: l1, y :: l2, z :: l3, h1, h2 => by
    simp only [lexR] at h1 h2 ⊢
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · exact Or.inl (tr _ _ _ h1 h2)
    · subst e2; exact Or.inl h1
    · subst e1; exact Or.inl h2
    · subst e1; subst e2; exact Or.inr ⟨rfl, lexR_trans R tr l1 l2 l3 h1 h2⟩
  | [], _, _, h1, _ => by simp [lexR] at h1
  | _ :: _, [], _, h1, _ => by simp [lexR] at h1
  | _ :: _, _ :: _, [], _, h2 => by simp [lexR] at h2

theorem lexR_irrefl {α : Type} (R : α → α → Prop) (irr : ∀ a, ¬ R a a) : ∀ l : List α, ¬ lexR R l l
  | [] => by simp [lexR]
  | x :: l => by
    simp only [lexR]
    intro h
    rcases h with h | ⟨_, h⟩
    · exact irr x h
    · exact lexR_irrefl R irr l h

theorem lexR_total {α : Type} (R : α → α → Prop) (X : α → Prop)
    (tot : ∀ a b, X a → X b → a ≠ b → R a b ∨ R b a) :
    ∀ (l l' : List α), l.length = l'.length → (∀ x, x ∈ l → X x) → (∀ x, x ∈ l' → X x) →
      l ≠ l' → lexR R l l' ∨ lexR R l' l
  | [], [], _, _, _, hne => absurd rfl hne
  | x :: l, y :: l', hlen, hx, hy, hne => by
    simp only [lexR]
    by_cases e : x = y
    · subst e
      have hne' : l ≠ l' := fun h => hne (by rw [h])
      rcases lexR_total R X tot l l' (by simpa using hlen) (fun z hz => hx z (List.mem_cons_of_mem _ hz))
          (fun z hz => hy z (List.mem_cons_of_mem _ hz)) hne' with h | h
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr (Or.inr ⟨rfl, h⟩)
    · rcases tot x y (hx x (List.mem_cons_self _ _)) (hy y (List.mem_cons_self _ _)) e with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
  | [], _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _ => by simp at hlen

-- ---------- 定義の順序 ----------
/-- 定義 (n, τ) の順序：番号 n、次にパラメータ列 τ の辞書式順序（同じ長さ）。 -/
def defLt {α : Type} (R : α → α → Prop) (d d' : Nat × List α) : Prop :=
  d.1 < d'.1 ∨ (d.1 = d'.1 ∧ lexN R d.2 d'.2)

theorem defLt_wf {α : Type} (R : α → α → Prop) (wf : WellFounded R) : WellFounded (defLt R) := by
  have w : WellFounded (Prod.Lex (· < ·) (lexN R) : Nat × List α → Nat × List α → Prop) :=
    (Prod.lex ⟨_, Nat.lt_wfRel.wf⟩ ⟨_, lexN_wf R wf⟩).wf
  apply Subrelation.wf _ w
  intro a b h
  rcases a with ⟨n, l⟩; rcases b with ⟨n', l'⟩
  rcases h with h | ⟨e, h⟩
  · exact Prod.Lex.left _ _ h
  · simp only at e; subst e; exact Prod.Lex.right _ h

theorem defLt_trans {α : Type} (R : α → α → Prop) (tr : ∀ a b c, R a b → R b c → R a c)
    (d1 d2 d3 : Nat × List α) : defLt R d1 d2 → defLt R d2 d3 → defLt R d1 d3 := by
  intro h1 h2
  rcases h1 with h1 | ⟨e1, l1, h1⟩ <;> rcases h2 with h2 | ⟨e2, l2, h2⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, by omega, lexR_trans R tr _ _ _ h1 h2⟩

theorem defLt_irrefl {α : Type} (R : α → α → Prop) (irr : ∀ a, ¬ R a a) (d : Nat × List α) : ¬ defLt R d d := by
  intro h
  rcases h with h | ⟨_, _, h⟩
  · exact Nat.lt_irrefl _ h
  · exact lexR_irrefl R irr _ h

-- ---------- 新しい元の比較 ----------
section New
variable {α : Type} (R : α → α → Prop) (X : α → Prop)
  (irr : ∀ a, ¬ R a a) (tr : ∀ a b c, R a b → R b c → R a c)
  (tot : ∀ a b, X a → X b → a ≠ b → R a b ∨ R b a) (wf : WellFounded R)
  (len : Nat → Nat)                                  -- 式の番号からパラメータの個数
  (defines : Nat × List α → α → Prop)                -- (n, τ) が y を定義する
  (dfun : ∀ d y y', defines d y → defines d y' → y = y')
  (dok : ∀ d y, defines d y → d.2.length = len d.1 ∧ ∀ x, x ∈ d.2 → X x)

def newLess (a b : α) : Prop := ∃ d, defines d a ∧ ∀ d', defines d' b → defLt R d d'

def isMin (d : Nat × List α) (a : α) : Prop := defines d a ∧ ∀ d', defines d' a → ¬ defLt R d' d

include wf in
theorem min_exists (a : α) (h : ∃ d, defines d a) : ∃ d, isMin R defines d a := by
  obtain ⟨d0, h0⟩ := h
  refine Classical.byContradiction (fun hno => ?_)
  have : ∀ d, ¬ defines d a := by
    intro d
    induction d using (defLt_wf R wf).induction with
    | _ d ih => intro hd; exact hno ⟨d, hd, fun d' hd' hlt => ih d' hlt hd'⟩
  exact this d0 h0

include irr tot dok in
/-- 同じ元の二つの定義は、等しいか、どちらかが ≺ で小さい。 -/
theorem def_cmp (d d' : Nat × List α) (a b : α) (hd : defines d a) (hd' : defines d' b) :
    d = d' ∨ defLt R d d' ∨ defLt R d' d := by
  rcases d with ⟨n, l⟩; rcases d' with ⟨n', l'⟩
  rcases Nat.lt_trichotomy n n' with h | h | h
  · exact Or.inr (Or.inl (Or.inl h))
  · subst h
    have ⟨hl, hx⟩ := dok _ _ hd
    have ⟨hl', hx'⟩ := dok _ _ hd'
    have e1 : l.length = l'.length := by
      have a1 : l.length = len n := hl
      have a2 : l'.length = len n := hl'
      omega
    by_cases e : l = l'
    · subst e; exact Or.inl rfl
    · rcases lexR_total R X tot l l' e1 hx hx' e with h | h
      · exact Or.inr (Or.inl (Or.inr ⟨rfl, e1, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, e1.symm, h⟩))
  · exact Or.inr (Or.inr (Or.inl h))

include irr tr tot dok dfun in
/-- 生成プログラムの new_less（∃∀ の形）は、最小の定義どうしの比較と同値。 -/
theorem newLess_iff_min (a b : α) (hab : a ≠ b) (da db : Nat × List α)
    (ha : isMin R defines da a) (hb : isMin R defines db b) :
    newLess R defines a b ↔ defLt R da db := by
  constructor
  · intro ⟨d, hd, hall⟩
    have h1 := hall db hb.1
    -- da ≼ d
    rcases def_cmp R X irr tot len defines dok da d a a ha.1 hd with e | h | h
    · subst e; exact h1
    · exact defLt_trans R tr _ _ _ h h1
    · exact absurd h (ha.2 d hd)
  · intro h
    refine ⟨da, ha.1, fun d' hd' => ?_⟩
    rcases def_cmp R X irr tot len defines dok db d' b b hb.1 hd' with e | h' | h'
    · subst e; exact h
    · exact defLt_trans R tr _ _ _ h h'
    · exact absurd h' (hb.2 d' hd')

include irr tr dfun in
theorem newLess_irrefl (a : α) : ¬ newLess R defines a a := by
  intro ⟨d, hd, hall⟩
  exact defLt_irrefl R irr d (hall d hd)

include tr in
theorem newLess_trans (a b c : α) (hb : ∃ d, defines d b) :
    newLess R defines a b → newLess R defines b c → newLess R defines a c := by
  intro ⟨d1, hd1, h1⟩ ⟨d2, hd2, h2⟩
  exact ⟨d1, hd1, fun d' hd' => defLt_trans R tr _ _ _ (h1 d2 hd2) (h2 d' hd')⟩

include irr tr tot wf dok dfun in
theorem newLess_total (a b : α) (hab : a ≠ b) (ha : ∃ d, defines d a) (hb : ∃ d, defines d b) :
    newLess R defines a b ∨ newLess R defines b a := by
  obtain ⟨da, hma⟩ := min_exists R wf defines a ha
  obtain ⟨db, hmb⟩ := min_exists R wf defines b hb
  rcases def_cmp R X irr tot len defines dok da db a b hma.1 hmb.1 with e | h | h
  · subst e; exact absurd (dfun _ _ _ hma.1 hmb.1) hab
  · exact Or.inl ((newLess_iff_min R X irr tr tot len defines dfun dok a b hab da db hma hmb).mpr h)
  · exact Or.inr ((newLess_iff_min R X irr tr tot len defines dfun dok b a (Ne.symm hab) db da hmb hma).mpr h)

/-- 新しい元（定義をもつ元）の上で、newLess は整礎。最小の定義への写像で defLt に埋め込む。 -/
def NL (a b : α) : Prop := newLess R defines a b ∧ (∃ d, defines d a) ∧ (∃ d, defines d b)

open Classical in
include irr tr tot dok wf in
theorem newLess_wf : WellFounded (NL R defines) := by
  let μ : α → Nat × List α := fun a =>
    if h : ∃ d, defines d a then Classical.choose (min_exists R wf defines a h) else (0, [])
  have hμ : ∀ a (h : ∃ d, defines d a), isMin R defines (μ a) a := by
    intro a h
    simp only [μ, dif_pos h]
    exact Classical.choose_spec (min_exists R wf defines a h)
  apply Subrelation.wf _ (InvImage.wf μ (defLt_wf R wf))
  intro a b ⟨⟨d, hd, hall⟩, ha, hb⟩
  show defLt R (μ a) (μ b)
  have h1 := hall (μ b) (hμ b hb).1
  rcases def_cmp R X irr tot len defines dok (μ a) d a a (hμ a ha).1 hd with e | h | h
  · rw [e]; exact h1
  · exact defLt_trans R tr _ _ _ h h1
  · exact absurd h ((hμ a ha).2 d hd)

-- ---------- 次の段の順序 ----------
/-- <_{β+1}：古い元どうしは R、古い元は新しい元より前、新しい元どうしは NL。 -/
def succLt (a b : α) : Prop :=
  (X a ∧ X b ∧ R a b) ∨ (X a ∧ ¬ X b) ∨ (¬ X a ∧ ¬ X b ∧ NL R defines a b)

include irr tr tot dok wf in
theorem succ_wf : WellFounded (succLt R X defines) := by
  have accOld : ∀ b, X b → Acc (succLt R X defines) b := by
    intro b
    induction b using wf.induction with
    | _ b ih =>
      intro hb
      constructor
      intro a h
      rcases h with ⟨ha, _, hr⟩ | ⟨_, hnb⟩ | ⟨_, hnb, _⟩
      · exact ih a hr ha
      · exact absurd hb hnb
      · exact absurd hb hnb
  constructor
  intro b
  induction b using (newLess_wf R X irr tr tot wf len defines dok).induction with
  | _ b ih =>
    by_cases hb : X b
    · exact accOld b hb
    · constructor
      intro a h
      rcases h with ⟨_, hb', _⟩ | ⟨ha, _⟩ | ⟨_, _, hnl⟩
      · exact absurd hb' hb
      · exact accOld a ha
      · exact ih a hnl

end New

-- ---------- 極限段階 ----------
/-- 終切片への延長の族 (X_β, R_β) の和は整礎。β ≤ γ なら X_β ⊆ X_γ、R_γ は X_β 上で R_β と一致し、
    X_β の元の R_γ に関する前者はすべて X_β に属する（X_β は始切片）。 -/
theorem union_wf {α ι : Type} (le : ι → ι → Prop) (ltot : ∀ β γ, le β γ ∨ le γ β)
    (X : ι → α → Prop) (R : ι → α → α → Prop)
    (hR : ∀ β a b, R β a b → X β a ∧ X β b)
    (wfR : ∀ β, WellFounded (R β))
    (sub : ∀ β γ, le β γ → ∀ a, X β a → X γ a)
    (agree : ∀ β γ, le β γ → ∀ a b, X β a → X β b → (R γ a b ↔ R β a b))
    (initial : ∀ β γ, le β γ → ∀ a b, X β b → R γ a b → X β a) :
    WellFounded (fun a b => ∃ β, R β a b) := by
  constructor
  intro b
  by_cases hb : ∃ β, X β b
  · obtain ⟨β, hbβ⟩ := hb
    revert hbβ
    induction b using (wfR β).induction with
    | _ b ih =>
      intro hbβ
      constructor
      intro a ⟨γ, hγ⟩
      have ⟨haγ, hbγ⟩ := hR γ a b hγ
      rcases ltot γ β with h | h
      · -- γ ≤ β：a, b ∈ X_γ ⊆ X_β、R_β a b
        have haβ := sub γ β h a haγ
        have hbβ' := sub γ β h b hbγ
        have : R β a b := (agree γ β h a b haγ hbγ).mpr hγ
        exact ih a this haβ
      · -- β ≤ γ：b ∈ X_β なので a ∈ X_β、R_β a b
        have haβ := initial β γ h a b hbβ hγ
        exact ih a ((agree β γ h a b haβ hbβ).mp hγ) haβ
  · constructor
    intro a ⟨γ, hγ⟩
    exact absurd ⟨γ, (hR γ a b hγ).2⟩ hb

#print axioms succ_wf
#print axioms union_wf
#print axioms newLess_iff_min
#print axioms lexN_wf


end G13
