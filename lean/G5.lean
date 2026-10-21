/-
  別紙 G の補題 G5（充足関係）の形式化（改訂37）

  semantics.py の sat は「証明書 C・項の値の表 TV・充足の表 S が存在し、根の項目が S に入る」と述べる。
  ここでは C・TV・S の条件を semantics.py / parse.py のとおりに書き写し、次を示す。
    sound      ：条件を満たす証明書の項目は、本当の構文木に対応する（有限の列についての整礎な帰納法）
    term_ur 等 ：一意読み（同じ位置から読める項・論理式は一つ）
    term_val 等：TV の値は項の本当の値
    form_sat   ：S は Tarski の充足関係と一致する
  集合による符号化（順序対・lookup・割当ての集合表現）は扱わない（別紙 G.6 とテストによる）。
  割当ては全域関数 Nat → α とする（生成プログラムは式に現れる変数の上の有限関数を使うが、
  式の真偽は現れる変数の値だけで決まる）。関数記号の解釈は関数（生成プログラムでは fn_ok が関数性を課す）。
-/
namespace G5

inductive Tok where
  | bot | imp | neg | ex | lp | rp
  | var (i : Nat) | cst (i : Nat) | fn (i a : Nat) | elem | rel (i a : Nat)
deriving DecidableEq

abbrev Str := Nat → Option Tok

def Occ (s : Str) : Nat → List Tok → Prop
  | _, [] => True
  | i, t :: l => s i = some t ∧ Occ s (i + 1) l

theorem occ_append (s : Str) : ∀ (i : Nat) (l1 l2 : List Tok),
    Occ s i (l1 ++ l2) ↔ Occ s i l1 ∧ Occ s (i + l1.length) l2
  | i, [], l2 => by simp [Occ]
  | i, t :: l1, l2 => by
    have ih := occ_append s (i + 1) l1 l2
    have e : i + 1 + l1.length = i + (l1.length + 1) := by omega
    simp only [List.cons_append, Occ, List.length_cons]
    rw [show l1.append l2 = l1 ++ l2 from rfl, ih, e]
    exact and_assoc.symm

mutual
inductive Term where
  | var (i : Nat) | cst (i : Nat) | app (f a : Nat) (ts : Terms)
inductive Terms where
  | nil | cons (t : Term) (ts : Terms)
end

inductive Form where
  | bot | elem (t u : Term) | rel (r a : Nat) (ts : Terms)
  | imp (p q : Form) | neg (p : Form) | ex (k : Nat) (p : Form)

mutual
def Term.toks : Term → List Tok
  | .var i => [.var i]
  | .cst i => [.cst i]
  | .app f a ts => .fn f a :: .lp :: (Terms.toks ts ++ [.rp])
def Terms.toks : Terms → List Tok
  | .nil => []
  | .cons t ts => Term.toks t ++ Terms.toks ts
end

def Terms.len : Terms → Nat
  | .nil => 0
  | .cons _ ts => ts.len + 1

mutual
def Term.wf : Term → Prop
  | .var _ => True
  | .cst _ => True
  | .app _ a ts => ts.len = a ∧ Terms.wf ts
def Terms.wf : Terms → Prop
  | .nil => True
  | .cons t ts => Term.wf t ∧ Terms.wf ts
end

def Form.toks : Form → List Tok
  | .bot => [.bot]
  | .elem t u => .lp :: (t.toks ++ .elem :: (u.toks ++ [.rp]))
  | .rel r a ts => .rel r a :: .lp :: (ts.toks ++ [.rp])
  | .imp p q => .lp :: (p.toks ++ .imp :: (q.toks ++ [.rp]))
  | .neg p => .neg :: p.toks
  | .ex k p => .ex :: .var k :: .lp :: (p.toks ++ [.rp])

def Form.wf : Form → Prop
  | .bot => True
  | .elem t u => t.wf ∧ u.wf
  | .rel _ a ts => ts.len = a ∧ ts.wf
  | .imp p q => p.wf ∧ q.wf
  | .neg p => p.wf
  | .ex _ p => p.wf

-- ---------- 先頭の記号 ----------
def termHead : Tok → Prop
  | .var _ => True | .cst _ => True | .fn _ _ => True | _ => False
def formHead : Tok → Prop
  | .bot => True | .lp => True | .rel _ _ => True | .neg => True | .ex => True | _ => False

theorem term_head (t : Term) : ∃ x l, t.toks = x :: l ∧ termHead x := by
  cases t with
  | var i => exact ⟨_, _, rfl, trivial⟩
  | cst i => exact ⟨_, _, rfl, trivial⟩
  | app f a ts => exact ⟨_, _, rfl, trivial⟩

theorem terms_toks_ne (t : Term) (ts : Terms) : (Terms.cons t ts).toks ≠ [] := by
  obtain ⟨x, l, h, _⟩ := term_head t
  simp [Terms.toks, h]

theorem form_head (p : Form) : ∃ x l, p.toks = x :: l ∧ formHead x := by
  cases p <;> exact ⟨_, _, rfl, trivial⟩

theorem heads_disjoint (x : Tok) (h1 : termHead x) (h2 : formHead x) : False := by
  cases x <;> simp [termHead, formHead] at h1 h2

theorem occ_head {s : Str} {i : Nat} {l : List Tok} {x : Tok} {r : List Tok}
    (hl : l = x :: r) (h : Occ s i l) : s i = some x := by
  subst hl; exact h.1

-- ---------- 一意読み ----------
mutual
theorem term_ur (s : Str) : ∀ (t t' : Term) (i : Nat), t.wf → t'.wf →
    Occ s i t.toks → Occ s i t'.toks → t = t'
  | .var k, .var k', i, _, _, h, h' => by
    simp [Term.toks, Occ] at h h'; rw [h] at h'; cases h'; rfl
  | .var k, .cst k', i, _, _, h, h' => by
    simp [Term.toks, Occ] at h h'; rw [h] at h'; cases h'
  | .var k, .app f a ts, i, _, _, h, h' => by
    simp [Term.toks, Occ] at h h'; rw [h] at h'; cases h'.1
  | .cst k, .var k', i, _, _, h, h' => by
    simp [Term.toks, Occ] at h h'; rw [h] at h'; cases h'
  | .cst k, .cst k', i, _, _, h, h' => by
    simp [Term.toks, Occ] at h h'; rw [h] at h'; cases h'; rfl
  | .cst k, .app f a ts, i, _, _, h, h' => by
    simp [Term.toks, Occ] at h h'; rw [h] at h'; cases h'.1
  | .app f a ts, .var k', i, _, _, h, h' => by
    simp [Term.toks, Occ] at h h'; rw [h.1] at h'; cases h'
  | .app f a ts, .cst k', i, _, _, h, h' => by
    simp [Term.toks, Occ] at h h'; rw [h.1] at h'; cases h'
  | .app f a ts, .app f' a' ts', i, hw, hw', h, h' => by
    simp only [Term.toks, Occ] at h h'
    have e : some (Tok.fn f a) = some (Tok.fn f' a') := h.1.symm.trans h'.1
    cases e
    have o := ((occ_append s (i + 1 + 1) _ _).mp h.2.2).1
    have o' := ((occ_append s (i + 1 + 1) _ _).mp h'.2.2).1
    simp only [Term.wf] at hw hw'
    have := terms_ur s ts ts' (i + 1 + 1) hw.2 hw'.2 (hw.1.trans hw'.1.symm) o o'
    rw [this]
theorem terms_ur (s : Str) : ∀ (ts ts' : Terms) (i : Nat), ts.wf → ts'.wf → ts.len = ts'.len →
    Occ s i ts.toks → Occ s i ts'.toks → ts = ts'
  | .nil, .nil, _, _, _, _, _, _ => rfl
  | .nil, .cons _ _, _, _, _, hl, _, _ => by simp [Terms.len] at hl
  | .cons _ _, .nil, _, _, _, hl, _, _ => by simp [Terms.len] at hl
  | .cons t ts, .cons t' ts', i, hw, hw', hl, h, h' => by
    simp only [Terms.toks] at h h'
    have a := (occ_append s i _ _).mp h
    have a' := (occ_append s i _ _).mp h'
    simp only [Terms.wf] at hw hw'
    have et := term_ur s t t' i hw.1 hw'.1 a.1 a'.1
    subst et
    simp only [Terms.len] at hl
    have ets := terms_ur s ts ts' (i + t.toks.length) hw.2 hw'.2 (by omega) a.2 a'.2
    rw [ets]
end

theorem occ_term_head {s : Str} {i : Nat} (t : Term) (rest : List Tok) (h : Occ s i (t.toks ++ rest)) :
    ∃ x, s i = some x ∧ termHead x := by
  obtain ⟨x, l, hl, hx⟩ := term_head t
  exact ⟨x, occ_head (by rw [hl]; rfl) h, hx⟩

theorem occ_form_head {s : Str} {i : Nat} (p : Form) (rest : List Tok) (h : Occ s i (p.toks ++ rest)) :
    ∃ x, s i = some x ∧ formHead x := by
  obtain ⟨x, l, hl, hx⟩ := form_head p
  exact ⟨x, occ_head (by rw [hl]; rfl) h, hx⟩

theorem form_ur (s : Str) : ∀ (p q : Form) (i : Nat), p.wf → q.wf → Occ s i p.toks → Occ s i q.toks → p = q := by
  intro p
  induction p with
  | bot =>
    intro q i _ _ h h'
    cases q <;> simp [Form.toks, Occ] at h h' <;> (try rw [h] at h') <;> (try simp at h') <;> rfl
  | elem t u =>
    intro q i hw hw' h h'
    cases q with
    | elem t' u' =>
      simp only [Form.toks, Occ] at h h'
      have a := (occ_append s (i+1) _ _).mp h.2
      have a' := (occ_append s (i+1) _ _).mp h'.2
      simp only [Form.wf] at hw hw'
      have et := term_ur s t t' (i+1) hw.1 hw'.1 a.1 a'.1
      subst et
      have b := (occ_append s (i + 1 + t.toks.length + 1) _ _).mp a.2.2
      have b' := (occ_append s (i + 1 + t.toks.length + 1) _ _).mp a'.2.2
      have eu := term_ur s u u' _ hw.2 hw'.2 b.1 b'.1
      rw [eu]
    | imp p' q' =>
      simp only [Form.toks, Occ] at h h'
      obtain ⟨x, hx, hxt⟩ := occ_term_head t _ h.2
      obtain ⟨y, hy, hyf⟩ := occ_form_head p' _ h'.2
      rw [hx] at hy; cases hy; exact (heads_disjoint x hxt hyf).elim
    | _ => simp [Form.toks, Occ] at h h' <;> (try rw [h.1] at h') <;> simp_all
  | rel r a ts =>
    intro q i hw hw' h h'
    cases q with
    | rel r' a' ts' =>
      simp only [Form.toks, Occ] at h h'
      have e : some (Tok.rel r a) = some (Tok.rel r' a') := h.1.symm.trans h'.1
      cases e
      have o := ((occ_append s (i + 1 + 1) _ _).mp h.2.2).1
      have o' := ((occ_append s (i + 1 + 1) _ _).mp h'.2.2).1
      simp only [Form.wf] at hw hw'
      rw [terms_ur s ts ts' (i+1+1) hw.2 hw'.2 (hw.1.trans hw'.1.symm) o o']
    | _ => simp [Form.toks, Occ] at h h' <;> (try rw [h.1] at h') <;> simp_all
  | imp p q ihp ihq =>
    intro r i hw hw' h h'
    cases r with
    | imp p' q' =>
      simp only [Form.toks, Occ] at h h'
      have a := (occ_append s (i+1) _ _).mp h.2
      have a' := (occ_append s (i+1) _ _).mp h'.2
      simp only [Form.wf] at hw hw'
      have ep := ihp p' (i+1) hw.1 hw'.1 a.1 a'.1
      subst ep
      have b := (occ_append s (i + 1 + p.toks.length + 1) _ _).mp a.2.2
      have b' := (occ_append s (i + 1 + p.toks.length + 1) _ _).mp a'.2.2
      rw [ihq q' _ hw.2 hw'.2 b.1 b'.1]
    | elem t' u' =>
      simp only [Form.toks, Occ] at h h'
      obtain ⟨x, hx, hxf⟩ := occ_form_head p _ h.2
      obtain ⟨y, hy, hyt⟩ := occ_term_head t' _ h'.2
      rw [hx] at hy; cases hy; exact (heads_disjoint x hyt hxf).elim
    | _ => simp [Form.toks, Occ] at h h' <;> (try rw [h.1] at h') <;> simp_all
  | neg p ih =>
    intro q i hw hw' h h'
    cases q with
    | neg p' =>
      simp only [Form.toks, Occ, Form.wf] at h h' hw hw'
      rw [ih p' (i+1) hw hw' h.2 h'.2]
    | _ => simp [Form.toks, Occ] at h h' <;> (try rw [h.1] at h') <;> simp_all
  | ex k p ih =>
    intro q i hw hw' h h'
    cases q with
    | ex k' p' =>
      simp only [Form.toks, Occ, Form.wf] at h h' hw hw'
      have e : some (Tok.var k) = some (Tok.var k') := h.2.1.symm.trans h'.2.1
      cases e
      have a := ((occ_append s (i+1+1+1) _ _).mp h.2.2.2).1
      have a' := ((occ_append s (i+1+1+1) _ _).mp h'.2.2.2).1
      rw [ih p' _ hw hw' a a']
    | _ => simp [Form.toks, Occ] at h h' <;> (try rw [h.1] at h') <;> simp_all


-- ---------- 証明書（parse.py の certificate_ok の書き写し） ----------
/-- 項目 (i, j, k)：k = 0 は項、k = 1 は論理式、k = n + 2 は n 個の項の列。 -/
def termOk (s : Str) (C : Nat → Nat → Nat → Prop) (i j : Nat) : Prop :=
  (j = i + 1 ∧ ((∃ k, s i = some (.var k)) ∨ (∃ k, s i = some (.cst k)))) ∨
  (∃ f a j1, j = j1 + 1 ∧ s i = some (.fn f a) ∧ s (i + 1) = some .lp ∧ s j1 = some .rp ∧ C (i + 2) j1 (a + 2))

def formOk (s : Str) (C : Nat → Nat → Nat → Prop) (i j : Nat) : Prop :=
  (j = i + 1 ∧ s i = some .bot) ∨
  (s i = some .lp ∧ ∃ j1, j = j1 + 1 ∧ s j1 = some .rp ∧
      ∃ m, m < j ∧ C (i + 1) m 0 ∧ s m = some .elem ∧ C (m + 1) j1 0) ∨
  (∃ r a j1, j = j1 + 1 ∧ s i = some (.rel r a) ∧ s (i + 1) = some .lp ∧ s j1 = some .rp ∧ C (i + 2) j1 (a + 2)) ∨
  (s i = some .lp ∧ ∃ j1, j = j1 + 1 ∧ s j1 = some .rp ∧
      ∃ m, m < j ∧ C (i + 1) m 1 ∧ s m = some .imp ∧ C (m + 1) j1 1) ∨
  (s i = some .neg ∧ C (i + 1) j 1) ∨
  (s i = some .ex ∧ (∃ k, s (i + 1) = some (.var k)) ∧ s (i + 2) = some .lp ∧
      ∃ j1, j = j1 + 1 ∧ s j1 = some .rp ∧ C (i + 3) j1 1)

def listOk (C : Nat → Nat → Nat → Prop) (i j n : Nat) : Prop :=
  (n = 0 ∧ i = j) ∨ (∃ n0, n = n0 + 1 ∧ ∃ m, m ≤ j ∧ C i m 0 ∧ C m j (n0 + 2))

def Just (s : Str) (C : Nat → Nat → Nat → Prop) (i j : Nat) : Nat → Prop
  | 0 => termOk s C i j
  | 1 => formOk s C i j
  | n + 2 => listOk C i j n

/-- 項目が本当の構文木に対応すること。 -/
def Parses (s : Str) (i j : Nat) : Nat → Prop
  | 0 => ∃ t : Term, t.wf ∧ Occ s i t.toks ∧ j = i + t.toks.length
  | 1 => ∃ p : Form, p.wf ∧ Occ s i p.toks ∧ j = i + p.toks.length
  | n + 2 => ∃ ts : Terms, ts.wf ∧ ts.len = n ∧ Occ s i ts.toks ∧ j = i + ts.toks.length

def rk : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => n + 1

theorem occ_lt {s : Str} {h : Nat} (hfin : ∀ n, h ≤ n → s n = none) {i : Nat} {x : Tok}
    (hx : s i = some x) : i < h := by
  rcases Nat.lt_or_ge i h with hl | hge
  · exact hl
  · have := hfin i hge
    rw [this] at hx; cases hx

/-- 健全性：すべての項目が C の中で正当化されている（certificate_ok）なら、各項目は本当の構文木に対応する。
    尺度は (j, rk k, h − i) の辞書式順序。 -/
theorem sound (s : Str) (C : Nat → Nat → Nat → Prop) (h : Nat) (hfin : ∀ n, h ≤ n → s n = none)
    (hC : ∀ i j k, C i j k → Just s C i j k) :
    ∀ (j k i : Nat), C i j k → Parses s i j k := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ihj =>
  intro k
  -- k を項・論理式・列に分け、論理式の否定（同じ j）だけは h − i に関する帰納法で処理する
  match k with
  | 0 =>
    intro i hc
    have hj := hC i j 0 hc
    simp only [Just, termOk] at hj
    rcases hj with ⟨hj, ⟨kk, hk⟩ | ⟨kk, hk⟩⟩ | ⟨f, a, j1, hj, hf, hl, hr, hc2⟩
    · exact ⟨.var kk, trivial, by simp [Term.toks, Occ, hk], by simp [Term.toks]; omega⟩
    · exact ⟨.cst kk, trivial, by simp [Term.toks, Occ, hk], by simp [Term.toks]; omega⟩
    · obtain ⟨ts, hw, hlen, ho, he⟩ := ihj j1 (by omega) (a + 2) (i + 2) hc2
      refine ⟨.app f a ts, ⟨hlen, hw⟩, ?_, ?_⟩
      · simp only [Term.toks, Occ]
        refine ⟨hf, hl, (occ_append s (i + 1 + 1) _ _).mpr ⟨ho, ?_⟩⟩
        have : i + 1 + 1 + ts.toks.length = j1 := by omega
        rw [this]; simp [Occ, hr]
      · simp [Term.toks]; omega
  | n + 2 =>
    -- 列：個数 n に関する帰納法（j は固定）
    induction n with
    | zero =>
      intro i hc
      have hj := hC i j 2 hc
      simp only [Just, listOk] at hj
      rcases hj with ⟨_, hij⟩ | ⟨n0, hn0, _⟩
      · exact ⟨.nil, trivial, rfl, by simp [Terms.toks, Occ], by simp [Terms.toks]; omega⟩
      · omega
    | succ n0 ihn =>
      intro i hc
      have hj := hC i j (n0 + 1 + 2) hc
      simp only [Just, listOk] at hj
      rcases hj with ⟨hn, _⟩ | ⟨n1, hn1, m, hm, hcm, hcl⟩
      · omega
      · have hn1' : n1 = n0 := by omega
        subst hn1'
        -- 先頭の項
        have ht : Parses s i m 0 := by
          rcases Nat.lt_or_eq_of_le hm with hlt | heq
          · exact ihj m hlt 0 i hcm
          · subst heq
            -- m = j のとき：項 (i, j, 0)。ここでは j についての帰納法の仮定は使えないので、項の場合を直接示す
            have hj0 := hC i m 0 hcm
            simp only [Just, termOk] at hj0
            rcases hj0 with ⟨hj, ⟨kk, hk⟩ | ⟨kk, hk⟩⟩ | ⟨f, a, j1, hj, hf, hl, hr, hc2⟩
            · exact ⟨.var kk, trivial, by simp [Term.toks, Occ, hk], by simp [Term.toks]; omega⟩
            · exact ⟨.cst kk, trivial, by simp [Term.toks, Occ, hk], by simp [Term.toks]; omega⟩
            · obtain ⟨ts, hw, hlen, ho, he⟩ := ihj j1 (by omega) (a + 2) (i + 2) hc2
              refine ⟨.app f a ts, ⟨hlen, hw⟩, ?_, ?_⟩
              · simp only [Term.toks, Occ]
                refine ⟨hf, hl, (occ_append s (i + 1 + 1) _ _).mpr ⟨ho, ?_⟩⟩
                have : i + 1 + 1 + ts.toks.length = j1 := by omega
                rw [this]; simp [Occ, hr]
              · simp [Term.toks]; omega
        obtain ⟨t, htw, hto, hte⟩ := ht
        obtain ⟨ts, hw, hlen, ho, he⟩ := ihn m hcl
        refine ⟨.cons t ts, ⟨htw, hw⟩, by simp [Terms.len, hlen], ?_, ?_⟩
        · simp only [Terms.toks]
          exact (occ_append s i _ _).mpr ⟨hto, by rw [← hte]; exact ho⟩
        · simp [Terms.toks]; omega
  | 1 =>
    -- 論理式：h − i に関する帰納法（否定の規則は同じ j で i を一つ進める）
    suffices H : ∀ d i, h - i = d → C i j 1 → Parses s i j 1 from fun i hc => H (h - i) i rfl hc
    intro d
    induction d using Nat.strongRecOn with
    | _ d ihd =>
    intro i hd hc
    have hj := hC i j 1 hc
    simp only [Just, formOk] at hj
    rcases hj with ⟨hj, hb⟩ | ⟨hl, j1, hj, hr, m, hm, hc1, he, hc2⟩ | ⟨r, a, j1, hj, hf, hl, hr, hc2⟩ |
        ⟨hl, j1, hj, hr, m, hm, hc1, he, hc2⟩ | ⟨hn, hc1⟩ | ⟨hx, ⟨kk, hk⟩, hl, j1, hj, hr, hc1⟩
    · exact ⟨.bot, trivial, by simp [Form.toks, Occ, hb], by simp [Form.toks]; omega⟩
    · obtain ⟨t, htw, hto, hte⟩ := ihj m hm 0 (i + 1) hc1
      obtain ⟨u, huw, huo, hue⟩ := ihj j1 (by omega) 0 (m + 1) hc2
      refine ⟨.elem t u, ⟨htw, huw⟩, ?_, ?_⟩
      · simp only [Form.toks, Occ]
        refine ⟨hl, (occ_append s (i + 1) _ _).mpr ⟨hto, ?_⟩⟩
        rw [← hte]; simp only [Occ]
        refine ⟨he, (occ_append s (m + 1) _ _).mpr ⟨huo, ?_⟩⟩
        rw [← hue]; simp [Occ, hr]
      · simp [Form.toks]; omega
    · obtain ⟨ts, hw, hlen, ho, he⟩ := ihj j1 (by omega) (a + 2) (i + 2) hc2
      refine ⟨.rel r a ts, ⟨hlen, hw⟩, ?_, ?_⟩
      · simp only [Form.toks, Occ]
        refine ⟨hf, hl, (occ_append s (i + 1 + 1) _ _).mpr ⟨ho, ?_⟩⟩
        have : i + 1 + 1 + ts.toks.length = j1 := by omega
        rw [this]; simp [Occ, hr]
      · simp [Form.toks]; omega
    · obtain ⟨p, hpw, hpo, hpe⟩ := ihj m hm 1 (i + 1) hc1
      obtain ⟨q, hqw, hqo, hqe⟩ := ihj j1 (by omega) 1 (m + 1) hc2
      refine ⟨.imp p q, ⟨hpw, hqw⟩, ?_, ?_⟩
      · simp only [Form.toks, Occ]
        refine ⟨hl, (occ_append s (i + 1) _ _).mpr ⟨hpo, ?_⟩⟩
        rw [← hpe]; simp only [Occ]
        refine ⟨he, (occ_append s (m + 1) _ _).mpr ⟨hqo, ?_⟩⟩
        rw [← hqe]; simp [Occ, hr]
      · simp [Form.toks]; omega
    · have hih : i < h := occ_lt hfin hn
      obtain ⟨p, hpw, hpo, hpe⟩ := ihd (h - (i + 1)) (by omega) (i + 1) rfl hc1
      refine ⟨.neg p, hpw, ⟨hn, hpo⟩, by simp [Form.toks]; omega⟩
    · obtain ⟨p, hpw, hpo, hpe⟩ := ihj j1 (by omega) 1 (i + 3) hc1
      refine ⟨.ex kk p, hpw, ?_, by simp [Form.toks]; omega⟩
      simp only [Form.toks, Occ]
      refine ⟨hx, hk, hl, (occ_append s (i + 1 + 1 + 1) _ _).mpr ⟨hpo, ?_⟩⟩
      have : i + 1 + 1 + 1 + p.toks.length = j1 := by omega
      rw [this]; simp [Occ, hr]

-- ---------- 意味論 ----------
structure Model (α : Type) where
  E : α → α → Prop
  Cn : Nat → α
  Fn : Nat → Nat → List α → α
  Rel : Nat → Nat → List α → Prop

mutual
def Term.eval {α : Type} (M : Model α) (σ : Nat → α) : Term → α
  | .var i => σ i
  | .cst i => M.Cn i
  | .app f a ts => M.Fn f a (Terms.eval M σ ts)
def Terms.eval {α : Type} (M : Model α) (σ : Nat → α) : Terms → List α
  | .nil => []
  | .cons t ts => Term.eval M σ t :: Terms.eval M σ ts
end

def upd {α : Type} (σ : Nat → α) (k : Nat) (x : α) : Nat → α := fun n => if n = k then x else σ n

/-- Tarski の充足関係（構文木の上の素直な再帰）。 -/
def Form.sat {α : Type} (M : Model α) : Form → (Nat → α) → Prop
  | .bot, _ => False
  | .elem t u, σ => M.E (t.eval M σ) (u.eval M σ)
  | .rel r a ts, σ => M.Rel r a (ts.eval M σ)
  | .imp p q, σ => Form.sat M p σ → Form.sat M q σ
  | .neg p, σ => ¬ Form.sat M p σ
  | .ex k p, σ => ∃ x, Form.sat M p (upd σ k x)

-- ---------- TV と S の条件（semantics.py の書き写し） ----------
section Tables
variable {α : Type} (M : Model α) (s : Str) (C : Nat → Nat → Nat → Prop)
  (TVt : Nat → Nat → (Nat → α) → α → Prop) (TVl : Nat → Nat → Nat → (Nat → α) → List α → Prop)
  (S : Nat → Nat → (Nat → α) → Prop)

def termClause (i j : Nat) (σ : Nat → α) (v : α) : Prop :=
  (j = i + 1 ∧ ∃ k, s i = some (.var k) ∧ v = σ k) ∨
  (j = i + 1 ∧ ∃ k, s i = some (.cst k) ∧ v = M.Cn k) ∨
  (∃ f a j1, j = j1 + 1 ∧ s i = some (.fn f a) ∧ s (i + 1) = some .lp ∧ s j1 = some .rp ∧
      ∃ w, TVl (i + 2) j1 a σ w ∧ v = M.Fn f a w)

def listClause (i j n : Nat) (σ : Nat → α) (w : List α) : Prop :=
  (n = 0 ∧ i = j ∧ w = []) ∨
  (∃ n0, n = n0 + 1 ∧ ∃ m, m ≤ j ∧ C i m 0 ∧ ∃ v w2, TVt i m σ v ∧ TVl m j n0 σ w2 ∧ w = v :: w2)

def formClause (i j : Nat) (σ : Nat → α) : Prop :=
  (j = i + 1 ∧ s i = some .bot ∧ False) ∨
  (s i = some .lp ∧ ∃ j1, j = j1 + 1 ∧ s j1 = some .rp ∧
      ∃ m, m < j ∧ C (i + 1) m 0 ∧ s m = some .elem ∧ C (m + 1) j1 0 ∧
        ∃ v1 v2, TVt (i + 1) m σ v1 ∧ TVt (m + 1) j1 σ v2 ∧ M.E v1 v2) ∨
  (∃ r a j1, j = j1 + 1 ∧ s i = some (.rel r a) ∧ s (i + 1) = some .lp ∧ s j1 = some .rp ∧
      ∃ w, TVl (i + 2) j1 a σ w ∧ M.Rel r a w) ∨
  (s i = some .lp ∧ ∃ j1, j = j1 + 1 ∧ s j1 = some .rp ∧
      ∃ m, m < j ∧ C (i + 1) m 1 ∧ s m = some .imp ∧ C (m + 1) j1 1 ∧ (S (i + 1) m σ → S (m + 1) j1 σ)) ∨
  (s i = some .neg ∧ C (i + 1) j 1 ∧ ¬ S (i + 1) j σ) ∨
  (s i = some .ex ∧ ∃ k, s (i + 1) = some (.var k) ∧ s (i + 2) = some .lp ∧
      ∃ j1, j = j1 + 1 ∧ s j1 = some .rp ∧ C (i + 3) j1 1 ∧ ∃ x, S (i + 3) j1 (upd σ k x))

end Tables

-- ---------- 主定理 ----------
section Main
variable {α : Type} (M : Model α) (s : Str) (C : Nat → Nat → Nat → Prop) (h : Nat)
  (hfin : ∀ n, h ≤ n → s n = none) (hC : ∀ i j k, C i j k → Just s C i j k)
  (TVt : Nat → Nat → (Nat → α) → α → Prop) (TVl : Nat → Nat → Nat → (Nat → α) → List α → Prop)
  (S : Nat → Nat → (Nat → α) → Prop)
  (hTVt : ∀ i j, C i j 0 → ∀ σ, (∃ v, TVt i j σ v) ∧ ∀ v, TVt i j σ v → termClause M s TVl i j σ v)
  (hTVl : ∀ i j n, C i j (n + 2) → ∀ σ, (∃ w, TVl i j n σ w) ∧
      ∀ w, TVl i j n σ w → listClause C TVt TVl i j n σ w)
  (hS : ∀ i j, C i j 1 → ∀ σ, (S i j σ ↔ formClause M s C TVt TVl S i j σ))

include hfin hC in
theorem term_end {t : Term} {i m : Nat} (hw : t.wf) (ho : Occ s i t.toks) (hc : C i m 0) :
    m = i + t.toks.length := by
  obtain ⟨t', hw', ho', he⟩ := sound s C h hfin hC m 0 i hc
  have := term_ur s t' t i hw' hw ho' ho
  subst this; exact he

include hfin hC in
theorem form_end {p : Form} {i m : Nat} (hw : p.wf) (ho : Occ s i p.toks) (hc : C i m 1) :
    m = i + p.toks.length := by
  obtain ⟨p', hw', ho', he⟩ := sound s C h hfin hC m 1 i hc
  have := form_ur s p' p i hw' hw ho' ho
  subst this; exact he

include hfin hC in
theorem c_term_head {a b : Nat} (hc : C a b 0) : ∃ x, s a = some x ∧ termHead x := by
  obtain ⟨t, _, ho, _⟩ := sound s C h hfin hC b 0 a hc
  obtain ⟨x, l, hl, hx⟩ := term_head t
  exact ⟨x, occ_head hl ho, hx⟩

include hfin hC in
theorem c_form_head {a b : Nat} (hc : C a b 1) : ∃ x, s a = some x ∧ formHead x := by
  obtain ⟨p, _, ho, _⟩ := sound s C h hfin hC b 1 a hc
  obtain ⟨x, l, hl, hx⟩ := form_head p
  exact ⟨x, occ_head hl ho, hx⟩

include hfin hC hTVt hTVl in
mutual
theorem term_val : ∀ (t : Term) (i : Nat), t.wf → Occ s i t.toks → C i (i + t.toks.length) 0 →
    ∀ σ v, TVt i (i + t.toks.length) σ v → v = t.eval M σ
  | .var k, i, _, ho, hc, σ, v, hv => by
    simp only [Term.toks, Occ] at ho
    rcases (hTVt i _ hc σ).2 v hv with ⟨_, k', hk', hv'⟩ | ⟨_, k', hk', _⟩ | ⟨f, a, j1, _, hf, _⟩
    · rw [ho.1] at hk'; cases hk'; rw [hv']; rfl
    · rw [ho.1] at hk'; cases hk'
    · rw [ho.1] at hf; cases hf
  | .cst k, i, _, ho, hc, σ, v, hv => by
    simp only [Term.toks, Occ] at ho
    rcases (hTVt i _ hc σ).2 v hv with ⟨_, k', hk', _⟩ | ⟨_, k', hk', hv'⟩ | ⟨f, a, j1, _, hf, _⟩
    · rw [ho.1] at hk'; cases hk'
    · rw [ho.1] at hk'; cases hk'; rw [hv']; rfl
    · rw [ho.1] at hf; cases hf
  | .app f a ts, i, hw, ho, hc, σ, v, hv => by
    have hlen : (Term.app f a ts).toks.length = ts.toks.length + 3 := by simp [Term.toks]
    simp only [Term.toks, Occ] at ho
    have hots := ((occ_append s (i + 1 + 1) _ _).mp ho.2.2).1
    simp only [Term.wf] at hw
    rcases (hTVt i _ hc σ).2 v hv with ⟨_, k', hk', _⟩ | ⟨_, k', hk', _⟩ |
        ⟨f', a', j1, hj, hf, _, _, w, hw', hv'⟩
    · rw [ho.1] at hk'; cases hk'
    · rw [ho.1] at hk'; cases hk'
    · rw [ho.1] at hf; cases hf
      have hJ := hC i _ 0 hc
      simp only [Just, termOk] at hJ
      rcases hJ with ⟨_, ⟨k'', hk''⟩ | ⟨k'', hk''⟩⟩ | ⟨f'', a'', j1', hj', hf'', _, _, hc2⟩
      · rw [ho.1] at hk''; cases hk''
      · rw [ho.1] at hk''; cases hk''
      · rw [ho.1] at hf''; cases hf''
        have e1 : j1' = j1 := by omega
        subst e1
        have e2 : j1' = i + 2 + ts.toks.length := by rw [hlen] at hj; omega
        rw [e2] at hc2 hw'
        have := terms_val ts (i + 2) a hw.2 hw.1 hots hc2 σ w hw'
        rw [hv', this]; rfl
theorem terms_val : ∀ (ts : Terms) (i n : Nat), ts.wf → ts.len = n → Occ s i ts.toks →
    C i (i + ts.toks.length) (n + 2) → ∀ σ w, TVl i (i + ts.toks.length) n σ w → w = ts.eval M σ
  | .nil, i, n, _, hn, _, hc, σ, w, hw => by
    simp only [Terms.len] at hn; subst hn
    rcases (hTVl i _ 0 hc σ).2 w hw with ⟨_, _, hw'⟩ | ⟨n0, hn0, _⟩
    · rw [hw']; rfl
    · omega
  | .cons t ts, i, n, hwf, hn, ho, hc, σ, w, hw => by
    simp only [Terms.len] at hn
    simp only [Terms.wf] at hwf
    simp only [Terms.toks] at ho
    have o := (occ_append s i _ _).mp ho
    rcases (hTVl i _ n hc σ).2 w hw with ⟨hn0, _, _⟩ | ⟨n0, hn0, m, _, hcm, v, w2, hv, hw2, hwe⟩
    · omega
    · have em : m = i + t.toks.length := term_end s C h hfin hC hwf.1 o.1 hcm
      subst em
      have hJ := hC i _ (n + 2) hc
      simp only [Just, listOk] at hJ
      rcases hJ with ⟨hn1, _⟩ | ⟨n1, hn1, m', _, hcm', hcl⟩
      · omega
      · have em' : m' = i + t.toks.length := term_end s C h hfin hC hwf.1 o.1 hcm'
        subst em'
        have e1 : n1 = n0 := by omega
        subst e1
        have ej : i + (Terms.cons t ts).toks.length = i + t.toks.length + ts.toks.length := by
          simp [Terms.toks]; omega
        rw [ej] at hcl hw2
        have ev := term_val t i hwf.1 o.1 hcm σ v hv
        have ew := terms_val ts (i + t.toks.length) n1 hwf.2 (by omega) o.2 hcl σ w2 hw2
        rw [hwe, ev, ew]; rfl
end

set_option linter.unusedSectionVars false

include hfin hC hTVt hTVl in
theorem tv_term {t : Term} {i : Nat} (hw : t.wf) (ho : Occ s i t.toks) (hc : C i (i + t.toks.length) 0)
    (σ : Nat → α) : TVt i (i + t.toks.length) σ (t.eval M σ) := by
  obtain ⟨v, hv⟩ := (hTVt i _ hc σ).1
  have := term_val M s C h hfin hC TVt TVl hTVt hTVl t i hw ho hc σ v hv
  rw [← this]; exact hv

include hfin hC hTVt hTVl in
theorem tv_terms {ts : Terms} {i n : Nat} (hw : ts.wf) (hn : ts.len = n) (ho : Occ s i ts.toks)
    (hc : C i (i + ts.toks.length) (n + 2)) (σ : Nat → α) : TVl i (i + ts.toks.length) n σ (ts.eval M σ) := by
  obtain ⟨w, hv⟩ := (hTVl i _ n hc σ).1
  have := terms_val M s C h hfin hC TVt TVl hTVt hTVl ts i n hw hn ho hc σ w hv
  rw [← this]; exact hv

include hfin hC hTVt hTVl in
/-- 一段分の Tarski の条件：より短い論理式の項目で S が充足関係と一致するなら、formClause は φ の充足と同値。 -/
theorem clause_iff : ∀ (φ : Form) (i : Nat), φ.wf → Occ s i φ.toks → C i (i + φ.toks.length) 1 →
    (∀ (ψ : Form) (i' : Nat), ψ.toks.length < φ.toks.length → ψ.wf → Occ s i' ψ.toks →
      C i' (i' + ψ.toks.length) 1 → ∀ τ, (S i' (i' + ψ.toks.length) τ ↔ ψ.sat M τ)) →
    ∀ σ, (formClause M s C TVt TVl S i (i + φ.toks.length) σ ↔ φ.sat M σ) := by
  intro φ
  cases φ with
  | bot =>
    intro i _ ho hc _ σ
    simp only [Form.toks, Occ] at ho
    simp only [Form.sat, iff_false]
    intro hcl
    rcases hcl with ⟨_, _, hf⟩ | ⟨hl, _⟩ | ⟨_, _, _, _, hl, _⟩ | ⟨hl, _⟩ | ⟨hl, _⟩ | ⟨hl, _⟩
    · exact hf
    all_goals (rw [ho.1] at hl; cases hl)
  | elem t u =>
    intro i hw ho hc hsub σ
    simp only [Form.wf] at hw
    have hlen : (Form.elem t u).toks.length = t.toks.length + u.toks.length + 3 := by
      simp [Form.toks]; omega
    simp only [Form.toks, Occ] at ho
    have o1 := (occ_append s (i + 1) _ _).mp ho.2
    simp only [Occ] at o1
    have o2 := (occ_append s (i + 1 + t.toks.length + 1) _ _).mp o1.2.2
    simp only [Occ] at o2
    simp only [Form.sat]
    constructor
    · intro hcl
      rcases hcl with ⟨_, hl, _⟩ | ⟨_, j1, hj, _, m, _, hc1, _, hc2, v1, v2, hv1, hv2, hE⟩ |
          ⟨_, _, _, _, hl, _⟩ | ⟨_, j1, _, _, m, _, hc1, _⟩ | ⟨hl, _⟩ | ⟨hl, _⟩
      · rw [ho.1] at hl; cases hl
      · have em := term_end s C h hfin hC hw.1 o1.1 hc1
        subst em
        have ej : j1 = i + 1 + t.toks.length + 1 + u.toks.length := by rw [hlen] at hj; omega
        subst ej
        have e1 := term_val M s C h hfin hC TVt TVl hTVt hTVl t (i + 1) hw.1 o1.1 hc1 σ v1 hv1
        have e2 := term_val M s C h hfin hC TVt TVl hTVt hTVl u _ hw.2 o2.1 hc2 σ v2 hv2
        rw [← e1, ← e2]; exact hE
      · rw [ho.1] at hl; cases hl
      · obtain ⟨x, hx, hxf⟩ := c_form_head s C h hfin hC hc1
        obtain ⟨y, hy, hyt⟩ := occ_term_head t _ ho.2
        rw [hx] at hy; cases hy; exact (heads_disjoint x hyt hxf).elim
      · rw [ho.1] at hl; cases hl
      · rw [ho.1] at hl; cases hl
    · intro hE
      have hJ := hC i _ 1 hc
      simp only [Just, formOk] at hJ
      rcases hJ with ⟨_, hl⟩ | ⟨_, j1, hj, hr, m, hm, hc1, he, hc2⟩ | ⟨_, _, _, _, hl, _⟩ |
          ⟨_, j1, _, _, m, _, hc1, _⟩ | ⟨hl, _⟩ | ⟨hl, _⟩
      · rw [ho.1] at hl; cases hl
      · have em := term_end s C h hfin hC hw.1 o1.1 hc1
        subst em
        have ej : j1 = i + 1 + t.toks.length + 1 + u.toks.length := by rw [hlen] at hj; omega
        subst ej
        refine Or.inr (Or.inl ⟨ho.1, _, hj, hr, _, hm, hc1, he, hc2, t.eval M σ, u.eval M σ, ?_, ?_, hE⟩)
        · exact tv_term M s C h hfin hC TVt TVl hTVt hTVl hw.1 o1.1 hc1 σ
        · exact tv_term M s C h hfin hC TVt TVl hTVt hTVl hw.2 o2.1 hc2 σ
      · rw [ho.1] at hl; cases hl
      · obtain ⟨x, hx, hxf⟩ := c_form_head s C h hfin hC hc1
        obtain ⟨y, hy, hyt⟩ := occ_term_head t _ ho.2
        rw [hx] at hy; cases hy; exact (heads_disjoint x hyt hxf).elim
      · rw [ho.1] at hl; cases hl
      · rw [ho.1] at hl; cases hl
  | rel r a ts =>
    intro i hw ho hc hsub σ
    simp only [Form.wf] at hw
    have hlen : (Form.rel r a ts).toks.length = ts.toks.length + 3 := by simp [Form.toks]
    simp only [Form.toks, Occ] at ho
    have hots := ((occ_append s (i + 1 + 1) _ _).mp ho.2.2).1
    simp only [Form.sat]
    have hJ := hC i _ 1 hc
    simp only [Just, formOk] at hJ
    rcases hJ with ⟨_, hl⟩ | ⟨hl, _⟩ | ⟨r', a', j1, hj, hf, _, hr, hc2⟩ | ⟨hl, _⟩ | ⟨hl, _⟩ | ⟨hl, _⟩
    all_goals try (rw [ho.1] at hl; cases hl)
    rw [ho.1] at hf; cases hf
    have ej : j1 = i + 2 + ts.toks.length := by rw [hlen] at hj; omega
    subst ej
    constructor
    · intro hcl
      rcases hcl with ⟨_, hl, _⟩ | ⟨hl, _⟩ | ⟨r'', a'', j2, hj2, hf2, _, _, w, hw2, hR⟩ | ⟨hl, _⟩ | ⟨hl, _⟩ | ⟨hl, _⟩
      all_goals try (rw [ho.1] at hl; cases hl)
      rw [ho.1] at hf2; cases hf2
      have e2 : j2 = i + 2 + ts.toks.length := by omega
      subst e2
      have := terms_val M s C h hfin hC TVt TVl hTVt hTVl ts (i + 2) a hw.2 hw.1 hots hc2 σ w hw2
      rw [← this]; exact hR
    · intro hR
      exact Or.inr (Or.inr (Or.inl ⟨r, a, _, hj, ho.1, ho.2.1, hr, ts.eval M σ,
        tv_terms M s C h hfin hC TVt TVl hTVt hTVl hw.2 hw.1 hots hc2 σ, hR⟩))
  | imp p q =>
    intro i hw ho hc hsub σ
    simp only [Form.wf] at hw
    have hlen : (Form.imp p q).toks.length = p.toks.length + q.toks.length + 3 := by
      simp [Form.toks]; omega
    simp only [Form.toks, Occ] at ho
    have o1 := (occ_append s (i + 1) _ _).mp ho.2
    simp only [Occ] at o1
    have o2 := (occ_append s (i + 1 + p.toks.length + 1) _ _).mp o1.2.2
    simp only [Occ] at o2
    simp only [Form.sat]
    -- 証明書から、本当の分け方の項目を取り出す
    have hJ := hC i _ 1 hc
    simp only [Just, formOk] at hJ
    rcases hJ with ⟨_, hl⟩ | ⟨_, j1, _, _, m, _, hc1, _⟩ | ⟨_, _, _, _, hl, _⟩ |
        ⟨_, j1, hj, hr, m, hm, hc1, he, hc2⟩ | ⟨hl, _⟩ | ⟨hl, _⟩
    all_goals try (rw [ho.1] at hl; cases hl)
    · obtain ⟨x, hx, hxt⟩ := c_term_head s C h hfin hC hc1
      obtain ⟨y, hy, hyf⟩ := occ_form_head p _ ho.2
      rw [hx] at hy; cases hy; exact (heads_disjoint x hxt hyf).elim
    have em := form_end s C h hfin hC hw.1 o1.1 hc1
    subst em
    have ej : j1 = i + 1 + p.toks.length + 1 + q.toks.length := by rw [hlen] at hj; omega
    subst ej
    have ep := hsub p (i + 1) (by rw [hlen]; omega) hw.1 o1.1 hc1 σ
    have eq := hsub q _ (by rw [hlen]; omega) hw.2 o2.1 hc2 σ
    constructor
    · intro hcl
      rcases hcl with ⟨_, hl, _⟩ | ⟨_, j2, _, _, m2, _, hc3, _⟩ | ⟨_, _, _, _, hl, _⟩ |
          ⟨_, j2, hj2, _, m2, _, hc3, _, hc4, himp⟩ | ⟨hl, _⟩ | ⟨hl, _⟩
      all_goals try (rw [ho.1] at hl; cases hl)
      · obtain ⟨x, hx, hxt⟩ := c_term_head s C h hfin hC hc3
        obtain ⟨y, hy, hyf⟩ := occ_form_head p _ ho.2
        rw [hx] at hy; cases hy; exact (heads_disjoint x hxt hyf).elim
      · have em2 := form_end s C h hfin hC hw.1 o1.1 hc3
        subst em2
        have ej2 : j2 = i + 1 + p.toks.length + 1 + q.toks.length := by omega
        subst ej2
        intro hp
        exact eq.mp (himp (ep.mpr hp))
    · intro himp
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ho.1, _, hj, hr, _, hm, hc1, he, hc2,
        fun hs => eq.mpr (himp (ep.mp hs))⟩)))
  | neg p =>
    intro i hw ho hc hsub σ
    simp only [Form.wf] at hw
    have hlen : (Form.neg p).toks.length = p.toks.length + 1 := by simp [Form.toks]
    simp only [Form.toks, Occ] at ho
    simp only [Form.sat]
    have hJ := hC i _ 1 hc
    simp only [Just, formOk] at hJ
    rcases hJ with ⟨_, hl⟩ | ⟨hl, _⟩ | ⟨_, _, _, _, hl, _⟩ | ⟨hl, _⟩ | ⟨_, hc1⟩ | ⟨hl, _⟩
    all_goals try (rw [ho.1] at hl; cases hl)
    have em := form_end s C h hfin hC hw ho.2 hc1
    have e := hsub p (i + 1) (by rw [hlen]; omega) hw ho.2 (by rw [← em]; exact hc1) σ
    rw [← em] at e
    constructor
    · intro hcl
      rcases hcl with ⟨_, hl, _⟩ | ⟨hl, _⟩ | ⟨_, _, _, _, hl, _⟩ | ⟨hl, _⟩ | ⟨_, _, hns⟩ | ⟨hl, _⟩
      all_goals try (rw [ho.1] at hl; cases hl)
      exact fun hp => hns (e.mpr hp)
    · intro hnp
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ho.1, hc1, fun hs => hnp (e.mp hs)⟩))))
  | ex k p =>
    intro i hw ho hc hsub σ
    simp only [Form.wf] at hw
    have hlen : (Form.ex k p).toks.length = p.toks.length + 4 := by simp [Form.toks]
    simp only [Form.toks, Occ] at ho
    have o1 := (occ_append s (i + 1 + 1 + 1) _ _).mp ho.2.2.2
    simp only [Occ] at o1
    simp only [Form.sat]
    have hJ := hC i _ 1 hc
    simp only [Just, formOk] at hJ
    rcases hJ with ⟨_, hl⟩ | ⟨hl, _⟩ | ⟨_, _, _, _, hl, _⟩ | ⟨hl, _⟩ | ⟨hl, _⟩ |
        ⟨_, _, _, j1, hj, hr, hc1⟩
    all_goals try (rw [ho.1] at hl; cases hl)
    have ej : j1 = i + 3 + p.toks.length := by rw [hlen] at hj; omega
    subst ej
    have e := fun τ => hsub p (i + 3) (by rw [hlen]; omega) hw o1.1 hc1 τ
    constructor
    · intro hcl
      rcases hcl with ⟨_, hl, _⟩ | ⟨hl, _⟩ | ⟨_, _, _, _, hl, _⟩ | ⟨hl, _⟩ | ⟨hl, _⟩ |
          ⟨_, k', hk', _, j2, hj2, _, _, x, hx⟩
      all_goals try (rw [ho.1] at hl; cases hl)
      rw [ho.2.1] at hk'; cases hk'
      have e2 : j2 = i + 3 + p.toks.length := by omega
      subst e2
      exact ⟨x, (e _).mp hx⟩
    · intro ⟨x, hx⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ho.1, k, ho.2.1, ho.2.2.1, _, hj, hr, hc1,
        x, (e _).mpr hx⟩))))

include hfin hC hTVt hTVl hS in
/-- 補題 G5 の核心：S は、C のどの論理式の項目でも、Tarski の充足関係と一致する。 -/
theorem form_sat : ∀ (φ : Form) (i : Nat), φ.wf → Occ s i φ.toks → C i (i + φ.toks.length) 1 →
    ∀ σ, (S i (i + φ.toks.length) σ ↔ φ.sat M σ) := by
  suffices H : ∀ n (φ : Form) (i : Nat), φ.toks.length = n → φ.wf → Occ s i φ.toks →
      C i (i + φ.toks.length) 1 → ∀ σ, (S i (i + φ.toks.length) σ ↔ φ.sat M σ) from
    fun φ i => H _ φ i rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro φ i hn hw ho hc σ
  rw [hS i _ hc σ]
  exact clause_iff M s C h hfin hC TVt TVl S hTVt hTVl φ i hw ho hc
    (fun ψ i' hl hw' ho' hc' τ => ih _ (by omega) ψ i' rfl hw' ho' hc' τ) σ

end Main

-- ---------- 存在：本当の表は条件を満たす ----------
section Exist
variable {α : Type} (M : Model α) (s : Str)

def TVtrue (i j : Nat) (σ : Nat → α) (v : α) : Prop :=
  ∃ t : Term, t.wf ∧ Occ s i t.toks ∧ j = i + t.toks.length ∧ v = t.eval M σ
def TVltrue (i j n : Nat) (σ : Nat → α) (w : List α) : Prop :=
  ∃ ts : Terms, ts.wf ∧ ts.len = n ∧ Occ s i ts.toks ∧ j = i + ts.toks.length ∧ w = ts.eval M σ
def Strue (i j : Nat) (σ : Nat → α) : Prop :=
  ∃ φ : Form, φ.wf ∧ Occ s i φ.toks ∧ j = i + φ.toks.length ∧ φ.sat M σ

theorem parses_just : ∀ i j k, Parses s i j k → Just s (Parses s) i j k := by
  intro i j k hp
  match k, hp with
  | 0, ⟨t, hw, ho, he⟩ =>
    simp only [Just, termOk]
    cases t with
    | var kk => simp only [Term.toks, Occ] at ho; exact Or.inl ⟨by simp [Term.toks] at he; omega, Or.inl ⟨kk, ho.1⟩⟩
    | cst kk => simp only [Term.toks, Occ] at ho; exact Or.inl ⟨by simp [Term.toks] at he; omega, Or.inr ⟨kk, ho.1⟩⟩
    | app f a ts =>
      simp only [Term.toks, Occ] at ho
      simp only [Term.wf] at hw
      have o := (occ_append s (i + 1 + 1) _ _).mp ho.2.2
      simp only [Occ] at o
      have hl : (Term.app f a ts).toks.length = ts.toks.length + 3 := by simp [Term.toks]
      refine Or.inr ⟨f, a, i + 2 + ts.toks.length, by rw [hl] at he; omega, ho.1, ho.2.1, o.2.1, ?_⟩
      exact ⟨ts, hw.2, hw.1, o.1, rfl⟩
  | 1, ⟨φ, hw, ho, he⟩ =>
    simp only [Just, formOk]
    cases φ with
    | bot => simp only [Form.toks, Occ] at ho; exact Or.inl ⟨by simp [Form.toks] at he; omega, ho.1⟩
    | elem t u =>
      simp only [Form.toks, Occ] at ho
      simp only [Form.wf] at hw
      have o1 := (occ_append s (i + 1) _ _).mp ho.2
      simp only [Occ] at o1
      have o2 := (occ_append s (i + 1 + t.toks.length + 1) _ _).mp o1.2.2
      simp only [Occ] at o2
      have hl : (Form.elem t u).toks.length = t.toks.length + u.toks.length + 3 := by simp [Form.toks]; omega
      refine Or.inr (Or.inl ⟨ho.1, i + 1 + t.toks.length + 1 + u.toks.length, by rw [hl] at he; omega, o2.2.1,
        i + 1 + t.toks.length, by rw [hl] at he; omega, ⟨t, hw.1, o1.1, rfl⟩, o1.2.1, ⟨u, hw.2, o2.1, rfl⟩⟩)
    | rel r a ts =>
      simp only [Form.toks, Occ] at ho
      simp only [Form.wf] at hw
      have o := (occ_append s (i + 1 + 1) _ _).mp ho.2.2
      simp only [Occ] at o
      have hl : (Form.rel r a ts).toks.length = ts.toks.length + 3 := by simp [Form.toks]
      exact Or.inr (Or.inr (Or.inl ⟨r, a, i + 2 + ts.toks.length, by rw [hl] at he; omega, ho.1, ho.2.1, o.2.1,
        ⟨ts, hw.2, hw.1, o.1, rfl⟩⟩))
    | imp p q =>
      simp only [Form.toks, Occ] at ho
      simp only [Form.wf] at hw
      have o1 := (occ_append s (i + 1) _ _).mp ho.2
      simp only [Occ] at o1
      have o2 := (occ_append s (i + 1 + p.toks.length + 1) _ _).mp o1.2.2
      simp only [Occ] at o2
      have hl : (Form.imp p q).toks.length = p.toks.length + q.toks.length + 3 := by simp [Form.toks]; omega
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ho.1, i + 1 + p.toks.length + 1 + q.toks.length,
        by rw [hl] at he; omega, o2.2.1, i + 1 + p.toks.length, by rw [hl] at he; omega,
        ⟨p, hw.1, o1.1, rfl⟩, o1.2.1, ⟨q, hw.2, o2.1, rfl⟩⟩)))
    | neg p =>
      simp only [Form.toks, Occ] at ho
      simp only [Form.wf] at hw
      have hl : (Form.neg p).toks.length = p.toks.length + 1 := by simp [Form.toks]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ho.1, ⟨p, hw, ho.2, by rw [hl] at he; omega⟩⟩))))
    | ex kk p =>
      simp only [Form.toks, Occ] at ho
      simp only [Form.wf] at hw
      have o := (occ_append s (i + 1 + 1 + 1) _ _).mp ho.2.2.2
      simp only [Occ] at o
      have hl : (Form.ex kk p).toks.length = p.toks.length + 4 := by simp [Form.toks]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ho.1, ⟨kk, ho.2.1⟩, ho.2.2.1, i + 3 + p.toks.length,
        by rw [hl] at he; omega, o.2.1, ⟨p, hw, o.1, rfl⟩⟩))))
  | n + 2, ⟨ts, hw, hn, ho, he⟩ =>
    simp only [Just, listOk]
    cases ts with
    | nil => simp [Terms.len] at hn; exact Or.inl ⟨hn.symm, by simp [Terms.toks] at he; omega⟩
    | cons t ts =>
      simp only [Terms.len] at hn
      simp only [Terms.wf] at hw
      simp only [Terms.toks] at ho
      have o := (occ_append s i _ _).mp ho
      have hl : (Terms.cons t ts).toks.length = t.toks.length + ts.toks.length := by simp [Terms.toks]
      refine Or.inr ⟨ts.len, by omega, i + t.toks.length, by rw [hl] at he; omega, ⟨t, hw.1, o.1, rfl⟩, ?_⟩
      exact ⟨ts, hw.2, rfl, o.2, by rw [hl] at he; omega⟩

theorem tvtrue_ok : ∀ i j, Parses s i j 0 → ∀ σ, (∃ v, TVtrue M s i j σ v) ∧
    ∀ v, TVtrue M s i j σ v → termClause M s (TVltrue M s) i j σ v := by
  intro i j ⟨t, hw, ho, he⟩ σ
  refine ⟨⟨t.eval M σ, t, hw, ho, he, rfl⟩, ?_⟩
  intro v ⟨t', hw', ho', he', hv⟩
  cases t' with
  | var kk => simp only [Term.toks, Occ] at ho'; exact Or.inl ⟨by simp [Term.toks] at he'; omega, kk, ho'.1, hv⟩
  | cst kk => simp only [Term.toks, Occ] at ho'; exact Or.inr (Or.inl ⟨by simp [Term.toks] at he'; omega, kk, ho'.1, hv⟩)
  | app f a ts =>
    simp only [Term.toks, Occ] at ho'
    simp only [Term.wf] at hw'
    have o := (occ_append s (i + 1 + 1) _ _).mp ho'.2.2
    simp only [Occ] at o
    have hl : (Term.app f a ts).toks.length = ts.toks.length + 3 := by simp [Term.toks]
    exact Or.inr (Or.inr ⟨f, a, i + 2 + ts.toks.length, by rw [hl] at he'; omega, ho'.1, ho'.2.1, o.2.1,
      ts.eval M σ, ⟨ts, hw'.2, hw'.1, o.1, rfl, rfl⟩, hv⟩)

theorem tvltrue_ok : ∀ i j n, Parses s i j (n + 2) → ∀ σ, (∃ w, TVltrue M s i j n σ w) ∧
    ∀ w, TVltrue M s i j n σ w → listClause (Parses s) (TVtrue M s) (TVltrue M s) i j n σ w := by
  intro i j n ⟨ts, hw, hn, ho, he⟩ σ
  refine ⟨⟨ts.eval M σ, ts, hw, hn, ho, he, rfl⟩, ?_⟩
  intro w ⟨ts', hw', hn', ho', he', hwe⟩
  cases ts' with
  | nil => simp [Terms.len] at hn'; exact Or.inl ⟨hn'.symm, by simp [Terms.toks] at he'; omega, hwe⟩
  | cons t ts2 =>
    simp only [Terms.len] at hn'
    simp only [Terms.wf] at hw'
    simp only [Terms.toks] at ho'
    have o := (occ_append s i _ _).mp ho'
    have hl : (Terms.cons t ts2).toks.length = t.toks.length + ts2.toks.length := by simp [Terms.toks]
    exact Or.inr ⟨ts2.len, by omega, i + t.toks.length, by rw [hl] at he'; omega, ⟨t, hw'.1, o.1, rfl⟩,
      t.eval M σ, ts2.eval M σ, ⟨t, hw'.1, o.1, rfl, rfl⟩, ⟨ts2, hw'.2, rfl, o.2, by rw [hl] at he'; omega, rfl⟩, hwe⟩

theorem strue_iff {φ : Form} {i : Nat} (hw : φ.wf) (ho : Occ s i φ.toks) (σ : Nat → α) :
    Strue M s i (i + φ.toks.length) σ ↔ φ.sat M σ := by
  constructor
  · intro ⟨φ', hw', ho', he', hs⟩
    have := form_ur s φ' φ i hw' hw ho' ho
    subst this; exact hs
  · intro hs; exact ⟨φ, hw, ho, rfl, hs⟩

theorem strue_ok (h : Nat) (hfin : ∀ n, h ≤ n → s n = none) :
    ∀ i j, Parses s i j 1 → ∀ σ, (Strue M s i j σ ↔
      formClause M s (Parses s) (TVtrue M s) (TVltrue M s) (Strue M s) i j σ) := by
  intro i j ⟨φ, hw, ho, he⟩ σ
  subst he
  rw [strue_iff M s hw ho σ]
  exact (clause_iff M s (Parses s) h hfin (parses_just s) (TVtrue M s) (TVltrue M s) (Strue M s)
    (tvtrue_ok M s) (tvltrue_ok M s) φ i hw ho ⟨φ, hw, ho, rfl⟩
    (fun ψ i' _ hw' ho' _ τ => strue_iff M s hw' ho' τ) σ).symm

end Exist

/-- 補題 G5（生成プログラムの sat の形に合わせた最終形）：長さ h の記号列 s が論理式 φ を表すとき、
    「証明書 C・表 TV・表 S が条件を満たし、根の項目 (0, h) が C と S に入る」ものが存在することは、
    Tarski の意味で φ が σ の下で真であることと同値。 -/
theorem sat_correct {α : Type} (M : Model α) (s : Str) (φ : Form) (hw : φ.wf) (ho : Occ s 0 φ.toks)
    (hfin : ∀ n, φ.toks.length ≤ n → s n = none) (σ : Nat → α) :
    (∃ (C : Nat → Nat → Nat → Prop) (TVt : Nat → Nat → (Nat → α) → α → Prop)
        (TVl : Nat → Nat → Nat → (Nat → α) → List α → Prop) (S : Nat → Nat → (Nat → α) → Prop),
        (∀ i j k, C i j k → Just s C i j k) ∧
        (∀ i j, C i j 0 → ∀ τ, (∃ v, TVt i j τ v) ∧ ∀ v, TVt i j τ v → termClause M s TVl i j τ v) ∧
        (∀ i j n, C i j (n + 2) → ∀ τ, (∃ w, TVl i j n τ w) ∧
            ∀ w, TVl i j n τ w → listClause C TVt TVl i j n τ w) ∧
        (∀ i j, C i j 1 → ∀ τ, (S i j τ ↔ formClause M s C TVt TVl S i j τ)) ∧
        C 0 φ.toks.length 1 ∧ S 0 φ.toks.length σ)
    ↔ φ.sat M σ := by
  constructor
  · intro ⟨C, TVt, TVl, S, hC, hTVt, hTVl, hS, hc, hs⟩
    have := form_sat M s C φ.toks.length hfin hC TVt TVl S hTVt hTVl hS φ 0 hw ho
      (by simpa using hc) σ
    simp only [Nat.zero_add] at this
    exact this.mp hs
  · intro hsat
    refine ⟨Parses s, TVtrue M s, TVltrue M s, Strue M s, parses_just s, tvtrue_ok M s, tvltrue_ok M s,
      strue_ok M s φ.toks.length hfin, ⟨φ, hw, ho, by simp⟩, ⟨φ, hw, ho, by simp, hsat⟩⟩

#print axioms sat_correct

end G5
