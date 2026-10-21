/-
  別紙 G の補題 G6（IsDefinition と Definable）と、別紙 E 第 9 項の一意性の補題の形式化（改訂39）。

  ・原文の代入規則（ブログ「代入」節）：∃y(Q) に変数 x_j を代入するとき y = x_j なら、y を新しい変数に付け替える。
    ここでは x_i に x_j を代入する substV i j を構文木の上で定義する（新しい変数は、式・x_i・x_j に現れる
    どの添字よりも大きいものを選ぶ。原文は「最小のもの」だが、どちらを選んでも意味は同じ）。
  ・subst_lemma：σ ⊨ P[x_j/x_i] ⟺ σ[i := σ(j)] ⊨ P（代入補題）。
  ・isDef_iff：原文の IsDefinition(P) ≡ ∃x0 (P ∧ ∀x1 (P[x1/x0] → x1 = x0)) を全称閉包で読んだものは、
    definable.py の書き換え「∀σ ∃a (σ[0:=a] ⊨ P ∧ ∀b (σ[0:=a][1:=b][0:=b] ⊨ P → b = a))」と同値。
    外側の ∀x1 が P の自由な x1 を捕まえることも、この形にそのまま現れる。
  ・definable_unique：各 P について Definable な m は高々一つ（別紙 E 第 9 項の三段の証明）。
-/
import G14
namespace G5

-- ---------- 変数の出現と大きさ ----------
mutual
def Term.vars : Term → List Nat
  | .var i => [i]
  | .cst _ => []
  | .app _ _ ts => Terms.vars ts
def Terms.vars : Terms → List Nat
  | .nil => []
  | .cons t ts => Term.vars t ++ Terms.vars ts
end

def Form.vars : Form → List Nat
  | .bot => []
  | .elem t u => t.vars ++ u.vars
  | .rel _ _ ts => ts.vars
  | .imp p q => p.vars ++ q.vars
  | .neg p => p.vars
  | .ex k p => k :: p.vars

def Form.size : Form → Nat
  | .bot => 1
  | .elem _ _ => 1
  | .rel _ _ _ => 1
  | .imp p q => p.size + q.size + 1
  | .neg p => p.size + 1
  | .ex _ p => p.size + 1

def maxL : List Nat → Nat
  | [] => 0
  | x :: l => max x (maxL l)

theorem le_maxL : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ maxL l
  | [], _, h => by simp at h
  | y :: l, x, h => by
    simp only [maxL]
    rcases List.mem_cons.mp h with e | h'
    · subst e; exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_maxL l x h') (Nat.le_max_right _ _)

-- ---------- 変数の付け替え（新しい変数への、捕獲の起こらない改名） ----------
mutual
def Term.ren (k n : Nat) : Term → Term
  | .var i => if i = k then .var n else .var i
  | .cst i => .cst i
  | .app f a ts => .app f a (Terms.ren k n ts)
def Terms.ren (k n : Nat) : Terms → Terms
  | .nil => .nil
  | .cons t ts => .cons (Term.ren k n t) (Terms.ren k n ts)
end

def Form.ren (k n : Nat) : Form → Form
  | .bot => .bot
  | .elem t u => .elem (t.ren k n) (u.ren k n)
  | .rel r a ts => .rel r a (ts.ren k n)
  | .imp p q => .imp (p.ren k n) (q.ren k n)
  | .neg p => .neg (p.ren k n)
  | .ex m p => if m = k then .ex m p else .ex m (p.ren k n)

theorem ren_size (k n : Nat) : ∀ p : Form, (p.ren k n).size = p.size := by
  intro p; induction p with
  | bot => rfl
  | elem => rfl
  | rel => rfl
  | imp p q ihp ihq => simp [Form.ren, Form.size, ihp, ihq]
  | neg p ih => simp [Form.ren, Form.size, ih]
  | ex m p ih => by_cases h : m = k <;> simp [Form.ren, Form.size, h, ih]

-- ---------- 原文の代入規則 ----------
def fresh (p : Form) (i j : Nat) : Nat := max (maxL p.vars) (max i j) + 1

def Form.substV (i j : Nat) : Form → Form
  | .bot => .bot
  | .elem t u => .elem (t.ren i j) (u.ren i j)
  | .rel r a ts => .rel r a (ts.ren i j)
  | .imp p q => .imp (p.substV i j) (q.substV i j)
  | .neg p => .neg (p.substV i j)
  | .ex k p =>
    if k = i then .ex k p
    else if k = j then
      let n := fresh (.ex k p) i j
      .ex n ((p.ren k n).substV i j)
    else .ex k (p.substV i j)
termination_by p => p.size
decreasing_by
  all_goals simp_wf
  all_goals (try rw [ren_size])
  all_goals simp [Form.size]
  all_goals omega

section
variable {α : Type} (M : Model α)

theorem upd_comm (σ : Nat → α) {a b : Nat} (x y : α) (h : a ≠ b) :
    upd (upd σ a x) b y = upd (upd σ b y) a x := by
  funext n; simp only [upd]
  by_cases e1 : n = b
  · have e2 : ¬ n = a := fun e => h (e.symm.trans e1)
    simp [e1, e2, Ne.symm h]
  · by_cases e2 : n = a <;> simp [e1, e2, h]

theorem upd_upd (σ : Nat → α) (a : Nat) (x y : α) : upd (upd σ a x) a y = upd σ a y := by
  funext n; simp only [upd]; by_cases e : n = a <;> simp [e]

theorem upd_self (σ : Nat → α) (a : Nat) : upd σ a (σ a) = σ := by
  funext n; simp only [upd]; by_cases e : n = a <;> simp [e]

-- 項の改名：値は「k を n の値にした割当て」での値
mutual
theorem term_ren : ∀ (t : Term) (k n : Nat) (σ : Nat → α), (t.ren k n).eval M σ = t.eval M (upd σ k (σ n))
  | .var i, k, n, σ => by
    simp only [Term.ren]
    by_cases h : i = k
    · simp [h, Term.eval, upd]
    · simp [h, Term.eval, upd]
  | .cst _, _, _, _ => rfl
  | .app f a ts, k, n, σ => by simp only [Term.ren, Term.eval]; rw [terms_ren ts k n σ]
theorem terms_ren : ∀ (ts : Terms) (k n : Nat) (σ : Nat → α), (ts.ren k n).eval M σ = ts.eval M (upd σ k (σ n))
  | .nil, _, _, _ => rfl
  | .cons t ts, k, n, σ => by simp only [Terms.ren, Terms.eval]; rw [term_ren t k n σ, terms_ren ts k n σ]
end

/-- 改名の補題：n が p の束縛変数に現れなければ、σ ⊨ ren k n p ⟺ σ[k := σ(n)] ⊨ p。 -/
theorem form_ren (k n : Nat) : ∀ (p : Form), n ∉ p.vars → ∀ σ : Nat → α,
    ((p.ren k n).sat M σ ↔ p.sat M (upd σ k (σ n))) := by
  intro p
  induction p with
  | bot => intro _ _; exact Iff.rfl
  | elem t u => intro _ σ; simp only [Form.ren, Form.sat]; rw [term_ren M t, term_ren M u]
  | rel r a ts => intro _ σ; simp only [Form.ren, Form.sat]; rw [terms_ren M ts]
  | imp p q ihp ihq =>
    intro hn σ; simp only [Form.vars, List.mem_append, not_or] at hn
    simp only [Form.ren, Form.sat]; rw [ihp hn.1 σ, ihq hn.2 σ]
  | neg p ih => intro hn σ; simp only [Form.vars] at hn; simp only [Form.ren, Form.sat]; rw [ih hn σ]
  | ex m p ih =>
    intro hn σ
    simp only [Form.vars, List.mem_cons, not_or] at hn
    by_cases hm : m = k
    · subst hm
      simp only [Form.ren, if_pos rfl, Form.sat]
      constructor <;> intro ⟨x, hx⟩ <;> refine ⟨x, ?_⟩ <;> rw [upd_upd] at * <;> exact hx
    · simp only [Form.ren, if_neg hm, Form.sat]
      constructor
      · intro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [ih hn.2] at hx
        have e : (upd σ m x) n = σ n := by simp [upd, hn.1]
        rw [e, upd_comm σ x (σ n) hm] at hx
        exact hx
      · intro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [ih hn.2]
        have e : (upd σ m x) n = σ n := by simp [upd, hn.1]
        rw [e, upd_comm σ x (σ n) hm]
        exact hx

theorem vars_fv : ∀ (p : Form) (k : Nat), p.fv k → k ∈ p.vars := by
  intro p; induction p with
  | bot => intro k h; exact h.elim
  | elem t u =>
    intro k h
    have tv : ∀ (t : Term), t.fv k → k ∈ t.vars := by
      intro t; exact term_fv_vars t k
    simp only [Form.fv] at h; simp only [Form.vars, List.mem_append]
    rcases h with h | h
    · exact Or.inl (tv t h)
    · exact Or.inr (tv u h)
  | rel r a ts => intro k h; exact terms_fv_vars ts k h
  | imp p q ihp ihq =>
    intro k h; simp only [Form.fv] at h; simp only [Form.vars, List.mem_append]
    rcases h with h | h
    · exact Or.inl (ihp k h)
    · exact Or.inr (ihq k h)
  | neg p ih => intro k h; exact ih k h
  | ex m p ih => intro k h; exact List.mem_cons_of_mem _ (ih k h.2)
where
  term_fv_vars : ∀ (t : Term) (k : Nat), t.fv k → k ∈ t.vars
    | .var i, k, h => by simp [Term.fv] at h; simp [Term.vars, h]
    | .cst _, _, h => h.elim
    | .app _ _ ts, k, h => terms_fv_vars ts k h
  terms_fv_vars : ∀ (ts : Terms) (k : Nat), ts.fv k → k ∈ ts.vars
    | .nil, _, h => h.elim
    | .cons t ts, k, h => by
      simp only [Terms.fv] at h; simp only [Terms.vars, List.mem_append]
      rcases h with h | h
      · exact Or.inl (term_fv_vars t k h)
      · exact Or.inr (terms_fv_vars ts k h)

/-- 代入補題（原文の代入規則）：σ ⊨ P[x_j/x_i] ⟺ σ[i := σ(j)] ⊨ P。 -/
theorem subst_lemma (i j : Nat) : ∀ (p : Form) (σ : Nat → α),
    ((p.substV i j).sat M σ ↔ p.sat M (upd σ i (σ j))) := by
  suffices H : ∀ (s : Nat) (p : Form), p.size = s → ∀ σ : Nat → α,
      ((p.substV i j).sat M σ ↔ p.sat M (upd σ i (σ j))) from fun p => H _ p rfl
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
  intro p h σ
  cases p with
  | bot => simp [Form.substV, Form.sat]
  | elem t u => simp only [Form.substV, Form.sat]; rw [term_ren M t, term_ren M u]
  | rel r a ts => simp only [Form.substV, Form.sat]; rw [terms_ren M ts]
  | imp p q =>
    simp only [Form.substV, Form.sat]
    rw [ih p.size (by simp [Form.size] at h; omega) p rfl σ, ih q.size (by simp [Form.size] at h; omega) q rfl σ]
  | neg p =>
    simp only [Form.substV, Form.sat]
    rw [ih p.size (by simp [Form.size] at h; omega) p rfl σ]
  | ex k p =>
    by_cases hki : k = i
    · -- x_i は束縛されているので代入しない。左右は x_i の値によらない
      subst hki
      rw [Form.substV, if_pos rfl]
      exact sat_congr M (.ex k p) σ (upd σ k (σ j)) (fun m hm => by
        simp only [Form.fv] at hm; simp [upd, hm.1])
    · rw [Form.substV, if_neg hki]
      by_cases hkj : k = j
      · -- 捕獲を避けるため、k を新しい変数 n に付け替える
        simp only [if_pos hkj]
        subst hkj
        let n := fresh (.ex k p) i k
        have hbig : ∀ v, v ∈ (Form.ex k p).vars → v < n := fun v hv => by
          have := le_maxL _ v hv; simp only [n, fresh]; omega
        have hni : n ≠ i := by simp only [n, fresh]; omega
        have hnk : n ≠ k := by simp only [n, fresh]; omega
        have hnp : n ∉ p.vars := fun hm => by
          have := hbig n (List.mem_cons_of_mem _ hm); omega
        simp only [Form.sat]
        have hsz : (p.ren k n).size < s := by rw [ren_size]; simp [Form.size] at h; omega
        constructor
        · intro ⟨x, hx⟩
          rw [ih _ hsz (p.ren k n) rfl] at hx
          have e1 : (upd σ n x) k = σ k := by simp [upd, Ne.symm hnk]
          rw [e1, form_ren M k n p hnp] at hx
          have e2 : (upd (upd σ n x) i (σ k)) n = x := by simp [upd, hni]
          rw [e2] at hx
          refine ⟨x, ?_⟩
          -- hx : p ⊨ σ[n:=x][i:=σk][k:=x]、n は p に現れないので σ[i:=σk][k:=x] と同じ
          exact (sat_congr M p _ _ (fun m hm => by
            have hmn : m ≠ n := fun e => hnp (e ▸ vars_fv p m hm)
            simp only [upd]
            by_cases a1 : m = k <;> by_cases a2 : m = i <;> simp [a1, a2, hmn])).mp hx
        · intro ⟨x, hx⟩
          refine ⟨x, ?_⟩
          rw [ih _ hsz (p.ren k n) rfl]
          have e1 : (upd σ n x) k = σ k := by simp [upd, Ne.symm hnk]
          rw [e1, form_ren M k n p hnp]
          have e2 : (upd (upd σ n x) i (σ k)) n = x := by simp [upd, hni]
          rw [e2]
          exact (sat_congr M p _ _ (fun m hm => by
            have hmn : m ≠ n := fun e => hnp (e ▸ vars_fv p m hm)
            simp only [upd]
            by_cases a1 : m = k <;> by_cases a2 : m = i <;> simp [a1, a2, hmn])).mp hx
      · simp only [if_neg hkj, Form.sat]
        have hsz : p.size < s := by simp [Form.size] at h; omega
        constructor
        · intro ⟨x, hx⟩
          refine ⟨x, ?_⟩
          rw [ih _ hsz p rfl] at hx
          have e : (upd σ k x) j = σ j := by simp [upd, Ne.symm hkj]
          rw [e, upd_comm σ x (σ j) hki] at hx
          exact hx
        · intro ⟨x, hx⟩
          refine ⟨x, ?_⟩
          rw [ih _ hsz p rfl]
          have e : (upd σ k x) j = σ j := by simp [upd, Ne.symm hkj]
          rw [e, upd_comm σ x (σ j) hki]
          exact hx

-- ---------- IsDefinition と Definable ----------
/-- 原文の IsDefinition(P) を全称閉包で読んだもの（∧, ∀, = は通常の意味。= は領域の元の同一性）。
    σ は x_0, x_1 以外の自由変数への割当てを含む全体の割当て。 -/
def isDefOrig (P : Form) : Prop :=
  ∀ σ : Nat → α, ∃ a, P.sat M (upd σ 0 a) ∧
    ∀ b, (P.substV 0 1).sat M (upd (upd σ 0 a) 1 b) → b = a

/-- definable.py の書き換えた形。 -/
def isDefSem (P : Form) : Prop :=
  ∀ σ : Nat → α, ∃ a, P.sat M (upd σ 0 a) ∧
    ∀ b, P.sat M (upd (upd (upd σ 0 a) 1 b) 0 b) → b = a

theorem isDef_iff (P : Form) : isDefOrig M P ↔ isDefSem M P := by
  have key : ∀ (σ : Nat → α) (a b : α),
      (P.substV 0 1).sat M (upd (upd σ 0 a) 1 b) ↔ P.sat M (upd (upd (upd σ 0 a) 1 b) 0 b) := by
    intro σ a b
    rw [subst_lemma M 0 1 P]
    have : (upd (upd σ 0 a) 1 b) 1 = b := by simp [upd]
    rw [this]
  constructor
  · intro h σ; obtain ⟨a, ha, hb⟩ := h σ; exact ⟨a, ha, fun b hb' => hb b ((key σ a b).mpr hb')⟩
  · intro h σ; obtain ⟨a, ha, hb⟩ := h σ; exact ⟨a, ha, fun b hb' => hb b ((key σ a b).mp hb')⟩

/-- Definable(m, P)：U ⊨ IsDefinition(P) かつ U ⊨ P[Parameter(m)/x_0]（全称閉包）。 -/
def definable (m : α) (P : Form) : Prop :=
  isDefOrig M P ∧ ∀ σ : Nat → α, P.sat M (upd σ 0 m)

/-- 別紙 E 第 9 項：各 P について Definable な m は高々一つ。外側の ∀x_1 が P の自由な x_1 を
    捕まえる場合も含む。 -/
theorem definable_unique (P : Form) (m m' : α) (h : definable M m P) (h' : definable M m' P) : m = m' := by
  have hsem := (isDef_iff M P).mp h.1
  obtain ⟨a, _, huniq⟩ := hsem (fun _ => m)
  -- 段 1・2：b = m とすると、σ[0:=a][1:=m][0:=m] ⊨ P は Parameter(m) の条件から真なので m = a
  have e1 : m = a := huniq m (by
    have := h.2 (upd (upd (fun _ => m) 0 a) 1 m)
    exact this)
  have e2 : m' = a := huniq m' (by
    have := h'.2 (upd (upd (fun _ => m) 0 a) 1 m')
    exact this)
  rw [e1, e2]

end

#print axioms subst_lemma
#print axioms isDef_iff
#print axioms definable_unique

end G5
