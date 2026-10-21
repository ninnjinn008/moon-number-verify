/-
  書き写しの検証（改訂42）：枠組み。

  F は Moon.Fml（∈, =, ¬, ∧, ∀）に、下の層の部品の呼び出しを表す .rel 名前 c 引数 を加えたもの。
  c はその呼び出しの時点の新しい変数の番号で、部品を単独で生成した式の変数 n を
    n < 引数の個数 なら n 番目の引数、そうでなければ c + (n − 引数の個数)
  に付け替えると、生成プログラムが実際に作った部分木になる（sig）。expand はこの付け替えで .rel を展開する。

  ・ev_rename：変数の付け替えが単射なら、付け替えた式の評価は割当てを合成したものの評価と同じ。
  ・expand_ok：check が通れば、展開した式の評価は、.rel を部品の意図した条件（Rstd）で解釈した評価と同じ。
  ・Rstd：各部品の意図した条件（集合の言葉で書いたもの）。
-/
namespace Tr

/-- 部品の名前。 -/
inductive Nm where
  | empty
  | succ
  | trans
  | pair
  | is_one
  | numeral0
  | numeral1
  | numeral2
  | numeral3
  | numeral4
  | nat
  | triple
  | hyper_table
  | hyper
  | add
  | mul
  | exp
  | divides
  | prime
  | prime_table
  | nth_prime
  | seqfun
  | prod_table
  | encode
  | tuple4
  | metacode
  | numeral5
  | numeral6
  | numeral7
  | numeral8
  | numeral9
  | punct0
  | punct1
  | punct2
  | punct3
  | punct4
  | punct5
  | symvar
  | symconst
  | symfunc
  | symrel
  | symelem
  | symtheta
  | plus2
  | certificate
  | formula
  | formula_minus
  | assign
  | update
  | in_s
  | in_pair
  | in_triple
  | cons
  | term_clause
  | list_clause
  | formula_clause
  | tv_ok
  | s_ok
  | varset
  | sat
  | sat_ext
  | assign_w
  | update_w
  | is_definition
  | param_true
  | definable_in
  | ordinal
  | e_restrict
  | func_on
  | in_pair_l
  | pure
  | def_code
  | defines
  | lex_less
  | def_less
  | def_table
  | new_less
  | step
  | l_order
  | formula_code_minus
  | theta_value
  | least_good
  | theta_l
  | numeral10
  | numeral11
  | numeral12
  | dec
  | row_shape0
  | row_shape1
  | table_ok
  | cnf_cmp
  | cnf_lt
  | omega
  | func
  | bij
  | regular
  | power_of
  | strong_limit
  | inaccessible
  | o_ok
  | ord_of
  | lam_ok
  | eps0
  | lam_of
  | vstage
  | cn_ok
  | theta_ok
  | fn_ok
  | struct_rec
  | struct_full
  | func_on2
  | struct_table
  | definable_set
  | finite_sum
  | f_val
  | iterate10
  | lngn
deriving DecidableEq

inductive F where
  | mem  : Nat → Nat → F
  | eq   : Nat → Nat → F
  | neg  : F → F
  | conj : F → F → F
  | all  : Nat → F → F
  | rel  : Nm → Nat → List Nat → F
deriving DecidableEq

def upd {α : Type} (e : Nat → α) (v : Nat) (x : α) : Nat → α :=
  fun n => if n = v then x else e n

def ev {α : Type} (mem : α → α → Prop) (R : Nm → List α → Prop) : F → (Nat → α) → Prop
  | .mem a b, e   => mem (e a) (e b)
  | .eq a b, e    => e a = e b
  | .neg p, e     => ¬ ev mem R p e
  | .conj p q, e  => ev mem R p e ∧ ev mem R q e
  | .all v p, e   => ∀ x, ev mem R p (upd e v x)
  | .rel n _ as, e => R n (as.map e)

def rename (σ : Nat → Nat) : F → F
  | .mem a b    => .mem (σ a) (σ b)
  | .eq a b     => .eq (σ a) (σ b)
  | .neg p      => .neg (rename σ p)
  | .conj p q   => .conj (rename σ p) (rename σ q)
  | .all v p    => .all (σ v) (rename σ p)
  | .rel n c as => .rel n c (as.map σ)

theorem ev_rename {α : Type} (mem : α → α → Prop) (R : Nm → List α → Prop) (σ : Nat → Nat)
    (inj : ∀ x y, σ x = σ y → x = y) :
    ∀ (f : F) (e : Nat → α), ev mem R (rename σ f) e ↔ ev mem R f (fun n => e (σ n)) := by
  intro f
  induction f with
  | mem a b => intro e; exact Iff.rfl
  | eq a b => intro e; exact Iff.rfl
  | neg p ih => intro e; simp only [rename, ev]; exact not_congr (ih e)
  | conj p q ihp ihq => intro e; simp only [rename, ev]; exact and_congr (ihp e) (ihq e)
  | all v p ih =>
    intro e
    simp only [rename, ev]
    apply forall_congr'
    intro x
    rw [ih]
    have : (fun n => upd e (σ v) x (σ n)) = upd (fun n => e (σ n)) v x := by
      funext n
      simp only [upd]
      by_cases h : n = v
      · simp [h]
      · have : σ n ≠ σ v := fun h' => h (inj _ _ h')
        simp [h, this]
    rw [this]
  | rel n c as => intro e; simp only [rename, ev, List.map_map]; exact Iff.rfl

def sig (as : List Nat) (c : Nat) (n : Nat) : Nat :=
  if n < as.length then as.getD n 0 else c + (n - as.length)

def expand (tbl : Nm → Option (Nat × F)) : F → F
  | .mem a b    => .mem a b
  | .eq a b     => .eq a b
  | .neg p      => .neg (expand tbl p)
  | .conj p q   => .conj (expand tbl p) (expand tbl q)
  | .all v p    => .all v (expand tbl p)
  | .rel n c as =>
    match tbl n with
    | some (_, g) => rename (sig as c) g
    | none => .rel n c as

def okArgs (k : Nat) (as : List Nat) (c : Nat) : Bool :=
  as.length == k && as.all (fun a => decide (a < c)) &&
    (as.enum.all fun (i, a) => as.enum.all fun (j, b) => !(a == b) || i == j)

def check (tbl : Nm → Option (Nat × F)) : F → Bool
  | .mem _ _    => true
  | .eq _ _     => true
  | .neg p      => check tbl p
  | .conj p q   => check tbl p && check tbl q
  | .all _ p    => check tbl p
  | .rel n c as =>
    match tbl n with
    | some (k, _) => okArgs k as c
    | none => false

theorem getD_mem (as : List Nat) : ∀ n, n < as.length → as.getD n 0 ∈ as := by
  induction as with
  | nil => intro n h; simp at h
  | cons a as ih =>
    intro n h
    cases n with
    | zero => simp
    | succ n => simp only [List.getD_cons_succ]; exact List.mem_cons_of_mem _ (ih n (by simp at h; omega))

theorem enum_getD (as : List Nat) : ∀ n, n < as.length → (n, as.getD n 0) ∈ as.enum := by
  intro n h
  rw [List.mem_iff_getElem]
  refine ⟨n, by simp [h], ?_⟩
  simp [List.getElem_enum, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem sig_inj (k : Nat) (as : List Nat) (c : Nat) (h : okArgs k as c = true) :
    ∀ x y, sig as c x = sig as c y → x = y := by
  simp only [okArgs, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨_, hlt⟩, hnd⟩ := h
  intro x y hxy
  simp only [sig] at hxy
  by_cases hx : x < as.length <;> by_cases hy : y < as.length <;> simp only [hx, hy, ite_true, ite_false] at hxy
  · have := hnd _ (enum_getD as x hx) _ (enum_getD as y hy)
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at this
    rcases this with h1 | h1
    · exact absurd hxy h1
    · exact h1
  · have := hlt _ (getD_mem as x hx); omega
  · have := hlt _ (getD_mem as y hy); omega
  · omega

theorem map_sig (as : List Nat) (c : Nat) : (List.range as.length).map (sig as c) = as := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_range, sig]
    have : n < as.length := by simpa using h1
    simp [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]

/-- 展開の正しさ：表の各部品 g が「割当て e の下で、Rstd の名前 n の条件を (e 0, …, e (k−1)) について満たす」なら、
    展開した式の評価は、.rel を Rstd で解釈した評価と同じ。 -/
theorem expand_ok {α : Type} (mem : α → α → Prop) (R0 Rs : Nm → List α → Prop)
    (tbl : Nm → Option (Nat × F))
    (htbl : ∀ n k g, tbl n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rs n ((List.range k).map e)) :
    ∀ (f : F), check tbl f = true → ∀ e, (ev mem R0 (expand tbl f) e ↔ ev mem Rs f e) := by
  intro f
  induction f with
  | mem a b => intro _ e; exact Iff.rfl
  | eq a b => intro _ e; exact Iff.rfl
  | neg p ih => intro hc e; simp only [expand, ev]; exact not_congr (ih hc e)
  | conj p q ihp ihq =>
    intro hc e
    simp only [check, Bool.and_eq_true] at hc
    simp only [expand, ev]; exact and_congr (ihp hc.1 e) (ihq hc.2 e)
  | all v p ih =>
    intro hc e
    simp only [expand, ev]
    exact forall_congr' (fun x => ih hc _)
  | rel n c as =>
    intro hc e
    cases hg : tbl n with
    | none => simp [check, hg] at hc
    | some kg =>
      obtain ⟨k, g⟩ := kg
      simp only [check, hg] at hc
      simp only [expand, ev, hg]
      rw [ev_rename mem R0 _ (sig_inj k as c hc), htbl n k g hg]
      have hk : as.length = k := by
        simp only [okArgs, Bool.and_eq_true, beq_iff_eq] at hc; exact hc.1.1
      subst hk
      have : (List.range as.length).map (fun n => e (sig as c n)) = as.map e := by
        have h2 := congrArg (List.map e) (map_sig as c)
        rw [List.map_map] at h2
        exact h2
      rw [this]

/-! ### 意図した条件（集合の言葉で） -/
section
variable {α : Type} (mem : α → α → Prop)

def Empty (a : α) : Prop := ∀ x, ¬ mem x a
def Succ (b c : α) : Prop := ∀ u, mem u c ↔ (mem u b ∨ u = b)
def Trans (a : α) : Prop := ∀ z, mem z a → ∀ u, mem u z → mem u a
def Sing (s a : α) : Prop := mem a s ∧ ∀ t, mem t s → t = a
def Dbl (s a b : α) : Prop := mem a s ∧ mem b s ∧ ∀ t, mem t s → t = a ∨ t = b
/-- p = {{a}, {a, b}}：p の元はすべて {a} か {a, b} で、どちらも p に属する。 -/
def Pair (p a b : α) : Prop :=
  (∀ s, mem s p → Sing mem s a ∨ Dbl mem s a b) ∧ (∃ s, mem s p ∧ Sing mem s a) ∧ (∃ s, mem s p ∧ Dbl mem s a b)
def IsOne (z : α) : Prop := ∃ e, mem e z ∧ Empty mem e ∧ Succ mem e z
def Num : Nat → α → Prop
  | 0, v => Empty mem v
  | k + 1, v => ∃ w, mem w v ∧ Succ mem w v ∧ Num k w
def NatM (a : α) : Prop :=
  Trans mem a ∧ (∀ z, mem z a → ∀ u, mem u z → ∀ w, mem w u → mem w z) ∧
    ∀ z, (mem z a ∨ z = a) → Empty mem z ∨ ∃ w, mem w z ∧ Succ mem w z
/-- p = ((n, b), v)。 -/
def Triple (p n b v : α) : Prop := ∃ q, Pair mem p q v ∧ Pair mem q n b
/-- H(1, a, 0) = a、H(2, a, 0) = 0、H(n, a, 0) = 1（n ≥ 3）。 -/
def HBase (a n1 v : α) : Prop :=
  (Empty mem n1 ∧ v = a) ∨ (IsOne mem n1 ∧ Empty mem v) ∨ (¬ Empty mem n1 ∧ ¬ IsOne mem n1 ∧ IsOne mem v)
/-- 表の行 ((n, b), v) の正当化：H(0, a, b) = b+1、初期値、または再帰 H(n1+1, a, b1+1) = H(n1, a, H(n1+1, a, b1))。 -/
def HCase (t a n b v : α) : Prop :=
  (Empty mem n ∧ Succ mem b v) ∨
  (∃ n1, mem n1 n ∧ Succ mem n1 n ∧ Empty mem b ∧ HBase mem a n1 v) ∨
  (∃ n1, mem n1 n ∧ ∃ b1, mem b1 b ∧ Succ mem n1 n ∧ Succ mem b1 b ∧
    ∃ p2, mem p2 t ∧ ∃ w, Triple mem p2 n b1 w ∧ ∃ p3, mem p3 t ∧ Triple mem p3 n1 w v)
def HyperTable (t a : α) : Prop := ∀ p, mem p t → ∀ n b v, Triple mem p n b v → HCase mem t a n b v
def Hyper (n a b c : α) : Prop := ∃ t, HyperTable mem t a ∧ ∃ p, mem p t ∧ Triple mem p n b c
def Op (k : Nat) (a b c : α) : Prop := ∃ o, Num mem k o ∧ Hyper mem o a b c
def Divides (d m : α) : Prop := ∃ k, Op mem 2 d k m
def Small (z : α) : Prop := Empty mem z ∨ IsOne mem z
def PrimeM (p : α) : Prop := NatM mem p ∧ ¬ Small mem p ∧ ∀ d, mem d p → ¬ Small mem d → ¬ Divides mem d p
/-- 素数の表：各行 (i, p) は、i = 0 で p = 2、または前の行 (i−1, p2) があり、p は p2 より大きい素数で間に素数がない。 -/
def PrimeTable (t : α) : Prop :=
  ∀ q, mem q t → ∀ i p, Pair mem q i p →
    (Empty mem i ∧ Num mem 2 p) ∨
    (∃ i1, mem i1 i ∧ Succ mem i1 i ∧ ∃ q', mem q' t ∧ ∃ p2, Pair mem q' i1 p2 ∧
      mem p2 p ∧ PrimeM mem p ∧ ∀ m, mem m p → mem p2 m → ¬ PrimeM mem m)
def NthPrime (i p : α) : Prop := ∃ t, PrimeTable mem t ∧ ∃ q, mem q t ∧ ∃ p2, Pair mem q i p2 ∧ p2 = p
/-- s は定義域 h（自然数）の関数で、値は V を満たす。 -/
def SeqWith (s h : α) (V : α → Prop) : Prop :=
  NatM mem h ∧ (∀ q, mem q s → ∃ i a, Pair mem q i a ∧ mem i h ∧ V a) ∧
    (∀ i, mem i h → ∃ q, mem q s ∧ ∃ a, Pair mem q i a) ∧
    (∀ q1, mem q1 s → ∀ i1 a1, Pair mem q1 i1 a1 → ∀ q2, mem q2 s → ∀ i2 a2, Pair mem q2 i2 a2 → i1 = i2 → a1 = a2)
/-- 積の表：各行 (k, P) は、k = 0 で P = 1、または前の行 (k−1, P1) と s(k−1) = a があり、P = P1 · p_k^a。 -/
def ProdTable (t s : α) : Prop :=
  ∀ q, mem q t → ∀ k P, Pair mem q k P →
    (Empty mem k ∧ IsOne mem P) ∨
    (∃ k1, mem k1 k ∧ Succ mem k1 k ∧ ∃ q1, mem q1 t ∧ ∃ P1, Pair mem q1 k1 P1 ∧
      ∃ q2, mem q2 s ∧ ∃ a, Pair mem q2 k1 a ∧ ∃ pr, NthPrime mem k pr ∧ ∃ pw, Op mem 3 pr a pw ∧ Op mem 2 P1 pw P)
/-- c = Encode(s) = 2^h · P − 1（P は積の表の h 行目）。 -/
def EncodeM (s c : α) : Prop :=
  ∃ h, SeqWith mem s h (NatM mem) ∧ ∃ t, ProdTable mem t s ∧ ∃ q, mem q t ∧ ∃ P, Pair mem q h P ∧
    ∃ two, Num mem 2 two ∧ ∃ e, Op mem 3 two h e ∧ ∃ c1, Op mem 2 e P c1 ∧ Succ mem c c1
def Tuple4 (t : α) : Prop := ∃ four, Num mem 4 four ∧ SeqWith mem t four (NatM mem)
/-- n = MetaCode(s)：記号ごとの番号の列 c があって n = Encode(c)、c(i) = Encode(s(i))。 -/
def MetaCodeM (n s : α) : Prop :=
  ∃ h, SeqWith mem s h (Tuple4 mem) ∧ ∃ c, EncodeM mem c n ∧ SeqWith mem c h (NatM mem) ∧
    ∀ i, mem i h → ∃ q, mem q s ∧ ∃ t, Pair mem q i t ∧ ∃ q', mem q' c ∧ ∃ v, Pair mem q' i v ∧ EncodeM mem t v

/-! ### 構文の層（parse.py）の意図した条件 -/
def CompIs (t : α) (k v : Nat) : Prop := ∃ kk, Num mem k kk ∧ ∃ q, mem q t ∧ ∃ a, Pair mem q kk a ∧ Num mem v a
def Comp (t : α) (k : Nat) (P : α → Prop) : Prop := ∃ kk, Num mem k kk ∧ ∃ q, mem q t ∧ ∃ a, Pair mem q kk a ∧ P a
/-- 記号 (a0, 0, 0, 0)：⊥ → ¬ ∃ ( )。 -/
def PunctM (a0 : Nat) (t : α) : Prop := CompIs mem t 0 a0 ∧ CompIs mem t 1 0 ∧ CompIs mem t 2 0 ∧ CompIs mem t 3 0
def SymVar (t : α) : Prop := CompIs mem t 0 7 ∧ CompIs mem t 1 1 ∧ CompIs mem t 3 0
def SymConst (t : α) : Prop := CompIs mem t 0 6 ∧ CompIs mem t 1 0 ∧ CompIs mem t 3 0
def SymFunc (t : α) : Prop :=
  (CompIs mem t 0 8 ∧ CompIs mem t 1 2 ∧ CompIs mem t 2 0 ∧ CompIs mem t 3 1) ∨
  (CompIs mem t 0 8 ∧ CompIs mem t 1 3 ∧ CompIs mem t 2 0 ∧ CompIs mem t 3 1) ∨
  (CompIs mem t 0 8 ∧ CompIs mem t 1 4)
def SymRel (t : α) : Prop := CompIs mem t 0 9 ∧ CompIs mem t 1 6
def SymElem (t : α) : Prop := CompIs mem t 0 9 ∧ CompIs mem t 1 5 ∧ CompIs mem t 2 0 ∧ CompIs mem t 3 2
def SymTheta (t : α) : Prop := CompIs mem t 0 8 ∧ CompIs mem t 1 3 ∧ CompIs mem t 2 0 ∧ CompIs mem t 3 1
/-- k = n + 2。 -/
def Plus2 (n k : α) : Prop := ∃ n1, mem n1 k ∧ Succ mem n n1 ∧ Succ mem n1 k
/-- 列 s の i 番目の値 t が P を満たす。 -/
def At (s i : α) (P : α → Prop) : Prop := ∃ q, mem q s ∧ ∃ t, Pair mem q i t ∧ P t
/-- ((i, j), k) ∈ C で P(k)。 -/
def InCert (C i j : α) (P : α → Prop) : Prop := ∃ p, mem p C ∧ ∃ k, Triple mem p i j k ∧ P k
def Nxt (i : α) (B : α → Prop) : Prop := ∃ i1, Succ mem i i1 ∧ B i1
def Prv (j : α) (B : α → Prop) : Prop := ∃ j1, mem j1 j ∧ Succ mem j1 j ∧ B j1
/-- s(i) は引数 a 個の記号（ar）、s(i+1) = (、s(j−1) = )、[i+2, j−1) は項 a 個の列。 -/
def ArgsOk (s C i j : α) (ar : α → Prop) : Prop :=
  At mem s i (fun t => Comp mem t 3 (fun a => Nxt mem i (fun i1 => Nxt mem i1 (fun i2 => Prv mem j (fun j1 =>
    ar t ∧ At mem s i1 (PunctM mem 4) ∧ At mem s j1 (PunctM mem 5) ∧ InCert mem C i2 j1 (Plus2 mem a))))))
def TermOkM (s C i j : α) : Prop :=
  (Succ mem i j ∧ At mem s i (fun t => SymVar mem t ∨ SymConst mem t)) ∨ ArgsOk mem s C i j (SymFunc mem)
/-- [i, j) は項 n 個の列（k = n + 2）。 -/
def ListOkM (C K0 i j k : α) : Prop :=
  ∃ nn1, mem nn1 k ∧ ∃ n, mem n nn1 ∧ Plus2 mem n k ∧
    ((Empty mem n ∧ i = j) ∨
     ∃ n0, mem n0 n ∧ Succ mem n0 n ∧
       ((∃ m, mem m j ∧ InCert mem C i m (fun k => k = K0) ∧ InCert mem C m j (Plus2 mem n0)) ∨
        (InCert mem C i j (fun k => k = K0) ∧ InCert mem C j j (Plus2 mem n0))))
/-- ( 左 op 右 ) の形（左右は種類 kind の項目）。 -/
def Infix (s C i j : α) (op : α → Prop) (kind : α) : Prop :=
  At mem s i (PunctM mem 4) ∧ Nxt mem i (fun i1 => Prv mem j (fun j1 => At mem s j1 (PunctM mem 5) ∧
    ∃ m, mem m j ∧ InCert mem C i1 m (fun k => k = kind) ∧ At mem s m op ∧
      Nxt mem m (fun m1 => InCert mem C m1 j1 (fun k => k = kind))))
def FormOkM (s C K0 K1 i j : α) : Prop :=
  (Succ mem i j ∧ At mem s i (PunctM mem 0)) ∨
  Infix mem s C i j (SymElem mem) K0 ∨
  ArgsOk mem s C i j (SymRel mem) ∨
  Infix mem s C i j (PunctM mem 1) K1 ∨
  (At mem s i (PunctM mem 2) ∧ Nxt mem i (fun i1 => InCert mem C i1 j (fun k => k = K1))) ∨
  (At mem s i (PunctM mem 3) ∧ Nxt mem i (fun i1 => At mem s i1 (SymVar mem) ∧
    Nxt mem i1 (fun i2 => At mem s i2 (PunctM mem 4) ∧ Nxt mem i2 (fun i3 => Prv mem j (fun j1 =>
      At mem s j1 (PunctM mem 5) ∧ InCert mem C i3 j1 (fun k => k = K1))))))
/-- 証明書 C の各項目 ((i, j), k) が正当化されている（k = K0：項、k = K1：論理式、それ以外：項の列）。 -/
def CertOk (s C K0 K1 : α) : Prop :=
  ∀ p, mem p C → ∃ i j k, Triple mem p i j k ∧
    ((k = K0 ∧ TermOkM mem s C i j) ∨ (k = K1 ∧ FormOkM mem s C K0 K1 i j) ∨ ListOkM mem C K0 i j k)
/-- s は ┌L┐ の論理式：長さ h の 4 つ組の列で、((0, h), 1) を含む正当な証明書がある。 -/
def FormulaM (s : α) : Prop :=
  ∃ K0, Empty mem K0 ∧ ∃ K1, Succ mem K0 K1 ∧ ∃ h, SeqWith mem s h (Tuple4 mem) ∧
    ∃ C, InCert mem C K0 h (fun k => k = K1) ∧ CertOk mem s C K0 K1
def FormulaMinusM (s : α) : Prop :=
  ∃ K0, Empty mem K0 ∧ ∃ K1, Succ mem K0 K1 ∧ ∃ h, (SeqWith mem s h (Tuple4 mem) ∧
    ∃ C, InCert mem C K0 h (fun k => k = K1) ∧ CertOk mem s C K0 K1) ∧
    ¬ ∃ w, mem w h ∧ At mem s w (SymTheta mem)

/-! ### 充足関係の層（semantics.py）の意図した条件 -/
/-- (a, b) ∈ X。 -/
def InPair (X a b : α) : Prop := ∃ q, mem q X ∧ Pair mem q a b
/-- ((a, b), c) ∈ X。 -/
def InTriple (X a b c : α) : Prop := ∃ q, mem q X ∧ Triple mem q a b c
/-- sg は Ns から dom への関数（順序対の集合）。 -/
def AssignM (Ns dom sg : α) : Prop :=
  (∀ q, mem q sg → ∃ k a, Pair mem q k a ∧ mem k Ns ∧ mem a dom) ∧
  (∀ k, mem k Ns → ∃ q, mem q sg ∧ ∃ a, Pair mem q k a) ∧
  (∀ q1, mem q1 sg → ∀ k1 a1, Pair mem q1 k1 a1 → ∀ q2, mem q2 sg → ∀ k2 a2, Pair mem q2 k2 a2 → k1 = k2 → a1 = a2)
/-- sg2 = sg[k := a]。 -/
def UpdateM (Ns dom sg k a sg2 : α) : Prop :=
  AssignM mem Ns dom sg2 ∧ At mem sg2 k (fun b => b = a) ∧
  ∀ q, mem q sg → ∀ k1 b1, Pair mem q k1 b1 → k1 = k ∨ At mem sg2 k1 (fun b2 => b2 = b1)
/-- TV に (((i, j), k), (sg, v)) があり、kp(k) かつ vp(v)。 -/
def Tv (TV i j : α) (kp : α → Prop) (sg : α) (vp : α → Prop) : Prop :=
  ∃ e, mem e TV ∧ ∃ a b, Pair mem e a b ∧ (∃ ij k, Pair mem a ij k ∧ Pair mem ij i j ∧ kp k) ∧
    (∃ sg2 v, Pair mem b sg2 v ∧ sg2 = sg ∧ vp v)
/-- TV の元はすべて順序対 (a, b) で、a = ((i, j), k)、kp(k) なら、b = (sg2, v) で sg2 = sg なら vp(v)。 -/
def TvAll (TV i j : α) (kp : α → Prop) (sg : α) (vp : α → Prop) : Prop :=
  ∀ e, mem e TV → ∃ a b, Pair mem e a b ∧ ((∃ ij k, Pair mem a ij k ∧ Pair mem ij i j ∧ kp k) →
    ∃ sg2 v, Pair mem b sg2 v ∧ (sg2 = sg → vp v))
def InS (S i j sg : α) : Prop := ∃ e, mem e S ∧ ∃ ij sg2, Pair mem e ij sg2 ∧ Pair mem ij i j ∧ sg2 = sg
/-- 列 w = ⟨v⟩ ⌢ w2。 -/
def ConsM (v w2 w : α) : Prop :=
  (∃ z, Empty mem z ∧ InPair mem w z v) ∧
  (∀ q, mem q w → ∃ k x, Pair mem q k x ∧ ((Empty mem k ∧ x = v) ∨ ∃ k0, mem k0 k ∧ Succ mem k0 k ∧ InPair mem w2 k0 x)) ∧
  (∀ q, mem q w2 → ∃ k0 x, Pair mem q k0 x ∧ Nxt mem k0 (fun k => InPair mem w k x))
/-- 区間 [i, j) の項の、割当て sg の下での値が v であるための条件。 -/
def TermClauseM (s Cn Fn TV i j sg v : α) : Prop :=
  (Succ mem i j ∧ At mem s i (fun t => SymVar mem t ∧ Comp mem t 2 (fun k => At mem sg k (fun a => a = v)))) ∨
  (Succ mem i j ∧ At mem s i (fun t => SymConst mem t ∧ InPair mem Cn t v)) ∨
  At mem s i (fun t => SymFunc mem t ∧ Comp mem t 3 (fun ar => Nxt mem i (fun i1 => Nxt mem i1 (fun i2 =>
    Prv mem j (fun j1 => At mem s i1 (PunctM mem 4) ∧ At mem s j1 (PunctM mem 5) ∧
      Tv mem TV i2 j1 (Plus2 mem ar) sg (fun w => InTriple mem Fn t w v))))))
def ListClauseM (C K0 TV i j n sg w : α) : Prop :=
  (Empty mem n ∧ i = j ∧ Empty mem w) ∨
  ∃ n0, mem n0 n ∧ Succ mem n0 n ∧
    let via := fun mm => InCert mem C i mm (fun k => k = K0) ∧
      Tv mem TV i mm (fun k => k = K0) sg (fun v => Tv mem TV mm j (Plus2 mem n0) sg (fun w2 => ConsM mem v w2 w))
    (∃ m, mem m j ∧ via m) ∨ via j
def InfixS (s C i j : α) (op : α → Prop) (kind : α) (comb : α → α → α → α → Prop) : Prop :=
  At mem s i (PunctM mem 4) ∧ Nxt mem i (fun i1 => Prv mem j (fun j1 => At mem s j1 (PunctM mem 5) ∧
    ∃ m, mem m j ∧ InCert mem C i1 m (fun k => k = kind) ∧ At mem s m op ∧
      Nxt mem m (fun m1 => InCert mem C m1 j1 (fun k => k = kind) ∧ comb i1 m m1 j1)))
def FormClauseM (s dom E Rel Ns C K0 K1 TV S i j sg : α) : Prop :=
  (Succ mem i j ∧ (At mem s i (PunctM mem 0) ∧ ¬ i = i)) ∨
  InfixS mem s C i j (SymElem mem) K0 (fun a b c d =>
    Tv mem TV a b (fun k => k = K0) sg (fun v1 => Tv mem TV c d (fun k => k = K0) sg (fun v2 => InPair mem E v1 v2))) ∨
  At mem s i (fun t => SymRel mem t ∧ Comp mem t 3 (fun ar => Nxt mem i (fun i1 => Nxt mem i1 (fun i2 =>
    Prv mem j (fun j1 => At mem s i1 (PunctM mem 4) ∧ At mem s j1 (PunctM mem 5) ∧
      Tv mem TV i2 j1 (Plus2 mem ar) sg (fun w => InPair mem Rel t w)))))) ∨
  InfixS mem s C i j (PunctM mem 1) K1 (fun a b c d => ¬ InS mem S a b sg ∨ InS mem S c d sg) ∨
  (At mem s i (PunctM mem 2) ∧ Nxt mem i (fun i1 => InCert mem C i1 j (fun k => k = K1) ∧ ¬ InS mem S i1 j sg)) ∨
  (At mem s i (PunctM mem 3) ∧ Nxt mem i (fun i1 => At mem s i1 (fun t => SymVar mem t ∧ Comp mem t 2 (fun k =>
    Nxt mem i1 (fun i2 => At mem s i2 (PunctM mem 4) ∧ Nxt mem i2 (fun i3 => Prv mem j (fun j1 =>
      At mem s j1 (PunctM mem 5) ∧ InCert mem C i3 j1 (fun k => k = K1) ∧
        ∃ a, mem a dom ∧ ∃ sg2, UpdateM mem Ns dom sg k a sg2 ∧ InS mem S i3 j1 sg2)))))))
/-- TV の条件：C の項の区間と項の列の区間について、どの割当てでも値があり、値はすべて条件を満たす。 -/
def TvOk (s dom Cn Fn Ns C K0 TV : α) : Prop :=
  ∀ p, mem p C → ∃ i j k, Triple mem p i j k ∧
    ((k = K0 → ∀ sg, AssignM mem Ns dom sg → Tv mem TV i j (fun k2 => k2 = K0) sg (fun v => v = v) ∧
        TvAll mem TV i j (fun k2 => k2 = K0) sg (fun v => TermClauseM mem s Cn Fn TV i j sg v)) ∧
     (∀ nn1, mem nn1 k → ∀ n, mem n nn1 → Plus2 mem n k → ∀ sg, AssignM mem Ns dom sg →
        Tv mem TV i j (fun k2 => k2 = k) sg (fun w => w = w) ∧
        TvAll mem TV i j (fun k2 => k2 = k) sg (fun w => ListClauseM mem C K0 TV i j n sg w)))
/-- S の条件：C の論理式の区間について、どの割当てでも ((i, j), sg) ∈ S ⟺ 充足の条件。 -/
def SOk (s dom E Rel Ns C K0 K1 TV S : α) : Prop :=
  ∀ p, mem p C → ∃ i j k, Triple mem p i j k ∧
    (k = K1 → ∀ sg, AssignM mem Ns dom sg → (InS mem S i j sg ↔ FormClauseM mem s dom E Rel Ns C K0 K1 TV S i j sg))
/-- Ns は s に現れる変数の添字の集合。 -/
def VarSet (s h Ns : α) : Prop :=
  (∀ k, mem k Ns → ∃ p, mem p h ∧ At mem s p (fun t => SymVar mem t ∧ Comp mem t 2 (fun k2 => k2 = k))) ∧
  (∀ p, mem p h → At mem s p (fun t => SymVar mem t → Comp mem t 2 (fun k2 => mem k2 Ns)))
def SatBody (s dom E Cn Fn Rel Ns K0 K1 h sg : α) : Prop :=
  ∃ C, InCert mem C K0 h (fun k => k = K1) ∧ CertOk mem s C K0 K1 ∧
    ∃ TV, TvOk mem s dom Cn Fn Ns C K0 TV ∧ ∃ S, SOk mem s dom E Rel Ns C K0 K1 TV S ∧ InS mem S K0 h sg
/-- sat(s, 𝔄, σ)。 -/
def SatM (s dom E Cn Fn Rel sigma : α) : Prop :=
  ∃ K0, Empty mem K0 ∧ ∃ K1, Succ mem K0 K1 ∧ ∃ h, SeqWith mem s h (Tuple4 mem) ∧ ∃ Ns, VarSet mem s h Ns ∧
    (AssignM mem Ns dom sigma ∧ SatBody mem s dom E Cn Fn Rel Ns K0 K1 h sigma)
/-- sat の extended 版：sigma の Ns への制限 sr で評価する。 -/
def SatExtM (s dom E Cn Fn Rel sigma : α) : Prop :=
  ∃ K0, Empty mem K0 ∧ ∃ K1, Succ mem K0 K1 ∧ ∃ h, SeqWith mem s h (Tuple4 mem) ∧ ∃ Ns, VarSet mem s h Ns ∧
    ∃ sr, AssignM mem Ns dom sr ∧ (∀ q, mem q sr → mem q sigma) ∧ SatBody mem s dom E Cn Fn Rel Ns K0 K1 h sr

/-! ### 定義可能性の層（definable.py）の意図した条件 -/
/-- W = Ns ∪ {Z, O}。 -/
def WDef (Ns Z O W : α) : Prop :=
  (∀ q, mem q W → mem q Ns ∨ (q = Z ∨ q = O)) ∧ (∀ q, mem q Ns → mem q W) ∧ mem Z W ∧ mem O W
/-- _common：Z = 0, O = 1, W = Ns ∪ {0, 1} を導入して body を評価する。 -/
def DefCommon (s : α) (body : α → α → α → Prop) : Prop :=
  ∃ Z, Empty mem Z ∧ ∃ O, Succ mem Z O ∧ ∃ h, SeqWith mem s h (Tuple4 mem) ∧ ∃ Ns, VarSet mem s h Ns ∧
    ∃ W, WDef mem Ns Z O W ∧ body W Z O
/-- IsDefinition(P) の充足（全称閉包）。 -/
def IsDefM (s dom E Cn Fn Rel : α) : Prop :=
  DefCommon mem s (fun W Z O => ∀ sg, AssignM mem W dom sg → ∃ a, mem a dom ∧
    (∃ sa, UpdateM mem W dom sg Z a sa ∧ SatExtM mem s dom E Cn Fn Rel sa) ∧
    ∀ b, mem b dom → (∃ sb1, UpdateM mem W dom sg Z b sb1 ∧ ∃ sb, UpdateM mem W dom sb1 O b sb ∧
      SatExtM mem s dom E Cn Fn Rel sb) → b = a)
/-- P[Parameter(m)/x_0] の充足（全称閉包）。 -/
def ParamTrueM (s dom E Cn Fn Rel m : α) : Prop :=
  DefCommon mem s (fun W Z _ => ∀ sg, (AssignM mem W dom sg ∧ At mem sg Z (fun v => v = m)) →
    SatExtM mem s dom E Cn Fn Rel sg)
def DefinableInM (s dom E Cn Fn Rel m : α) : Prop :=
  mem m dom ∧ IsDefM mem s dom E Cn Fn Rel ∧ ParamTrueM mem s dom E Cn Fn Rel m

/-! ### L の段階と <_L の層（lorder.py）の意図した条件 -/
def OrdinalM (x : α) : Prop := Trans mem x ∧ ∀ z, mem z x → Trans mem z
/-- E = ∈ の D への制限（D は推移的）。 -/
def ERestrict (D E : α) : Prop :=
  (∀ q, mem q E → ∃ a b, Pair mem q a b ∧ mem a D ∧ mem b D ∧ mem a b) ∧
  (∀ b, mem b D → ∀ a, mem a b → ∃ q, mem q E ∧ Pair mem q a b)
/-- s（長さ h）の記号はどれも定数・関数・関係記号ではない。 -/
def Pure (s h : α) : Prop :=
  ∀ p, mem p h → At mem s p (fun t => ¬ SymConst mem t ∧ ¬ SymFunc mem t ∧ ¬ SymRel mem t)
/-- n は純粋な Formula₋ の式の番号。 -/
def DefCode (n : α) : Prop :=
  ∃ s, FormulaMinusM mem s ∧ MetaCodeM mem n s ∧ ∃ h, SeqWith mem s h (fun _ => True) ∧ Pure mem s h
/-- σ = τ ∪ {(0, z)}。 -/
def SigmaIs (tau z sg : α) : Prop :=
  (∀ q, mem q sg → mem q tau ∨ ∃ k a, Pair mem q k a ∧ Empty mem k ∧ a = z) ∧ (∀ q, mem q tau → mem q sg) ∧
  ∃ q, mem q sg ∧ ∃ k a, Pair mem q k a ∧ Empty mem k ∧ a = z
/-- (n, τ) は X 上で y を定義する。 -/
def DefinesM (n tau X y : α) : Prop :=
  ∃ s, FormulaMinusM mem s ∧ MetaCodeM mem n s ∧ ∃ h, SeqWith mem s h (fun _ => True) ∧ Pure mem s h ∧
    ∃ Ns, VarSet mem s h Ns ∧ ∃ K, ((∀ k, mem k K → mem k Ns ∧ ¬ Empty mem k) ∧ (∀ k, mem k Ns → Empty mem k ∨ mem k K)) ∧
      AssignM mem K X tau ∧ ∃ Z, Empty mem Z ∧ ∃ E, ERestrict mem X E ∧
        (∀ z, mem z y → mem z X) ∧
        ∀ z, mem z X → (mem z y ↔ ∃ sg, SigmaIs mem tau z sg ∧ SatExtM mem s X E Z Z Z sg)
/-- τ が τ′ より辞書式で小さい。 -/
def LexLess (tau tau2 Wg : α) : Prop :=
  ∃ q, mem q tau ∧ ∃ k u, Pair mem q k u ∧ ∃ q2, mem q2 tau2 ∧ ∃ k2 u2, Pair mem q2 k2 u2 ∧
    k2 = k ∧ InPair mem Wg u u2 ∧
    ∀ r, mem r tau → ∃ j v, Pair mem r j v ∧ (mem j k → ∃ q3, mem q3 tau2 ∧ Pair mem q3 j v)
def DefLess (n tau n2 tau2 Wg : α) : Prop := mem n n2 ∨ (n = n2 ∧ LexLess mem tau tau2 Wg)
/-- q = ((n, τ), y) のとき body n τ y。 -/
def DefEntry (q : α) (body : α → α → α → Prop) : Prop :=
  ∃ nt y, Pair mem q nt y ∧ ∃ n t, Pair mem nt n t ∧ body n t y
def DefTable (X DT : α) : Prop :=
  (∀ q, mem q DT → DefEntry mem q (fun n _ _ => DefCode mem n)) ∧
  ∀ n, DefCode mem n → ∀ t y, (DefinesM mem n t X y ↔ ∃ r, mem r DT ∧ Triple mem r n t y)
def NewLess (a b DT Wg : α) : Prop :=
  ∃ q, mem q DT ∧ DefEntry mem q (fun n t y => y = a ∧
    ∀ q2, mem q2 DT → DefEntry mem q2 (fun n2 t2 y2 => y2 = b → DefLess mem n t n2 t2 Wg))
/-- X1 = Def(X)、W1 = <_{β+1}。 -/
def StepM (X Wg X1 W1 : α) : Prop :=
  ∃ DT, DefTable mem X DT ∧
    ((∀ y, mem y X1 → ∃ q, mem q DT ∧ DefEntry mem q (fun _ _ y' => y' = y)) ∧
      (∀ q, mem q DT → DefEntry mem q (fun _ _ y' => mem y' X1))) ∧
    (∀ q, mem q W1 → ∃ a b, Pair mem q a b ∧ mem a X1 ∧ mem b X1) ∧
    ∀ a, mem a X1 → ∀ b, mem b X1 → (InPair mem W1 a b ↔
      ((mem a X ∧ mem b X ∧ InPair mem Wg a b) ∨ (mem a X ∧ ¬ mem b X) ∨ (¬ mem a X ∧ ¬ mem b X ∧ NewLess mem a b DT Wg)))
/-- T(b) = (X, W) で body X W。 -/
def AtT (T b : α) (body : α → α → Prop) : Prop := At mem T b (fun p => ∃ X W, Pair mem p X W ∧ body X W)
def IsSucc (z : α) : Prop := ∃ w, mem w z ∧ Succ mem w z
def UnionOk (T gm : α) (Y : α) (sel : α → α → α) : Prop :=
  (∀ x, mem x Y → ∃ g1, mem g1 gm ∧ AtT mem T g1 (fun X0 W0 => mem x (sel X0 W0))) ∧
  (∀ g1, mem g1 gm → AtT mem T g1 (fun X0 W0 => ∀ x, mem x (sel X0 W0) → mem x Y))
def ValueOk (T gm X W : α) : Prop :=
  (Empty mem gm → Empty mem X ∧ Empty mem W) ∧
  (∀ g1, mem g1 gm → Succ mem g1 gm → AtT mem T g1 (fun X0 W0 => StepM mem X0 W0 X W)) ∧
  ((¬ Empty mem gm ∧ ¬ IsSucc mem gm) → UnionOk mem T gm X (fun X0 _ => X0) ∧ UnionOk mem T gm W (fun _ W0 => W0))
/-- D = L_λ、WL = <_λ。 -/
def LOrderM (lam D WL : α) : Prop :=
  OrdinalM mem lam ∧ ∃ l1, Succ mem lam l1 ∧ ∃ T,
    ((∀ q, mem q T → ∃ a b, Pair mem q a b ∧ mem a l1) ∧
      (∀ q1, mem q1 T → ∀ a1 b1, Pair mem q1 a1 b1 → ∀ q2, mem q2 T → ∀ a2 b2, Pair mem q2 a2 b2 → a1 = a2 → b1 = b2)) ∧
    (∀ g, mem g l1 → AtT mem T g (fun X W => ValueOk mem T g X W)) ∧
    AtT mem T lam (fun X W => X = D ∧ W = WL)

/-! ### Θ の層（lorder.py の least_good・theta_L）の意図した条件 -/
def FormulaCodeMinus (n : α) : Prop := ∃ s, FormulaMinusM mem s ∧ MetaCodeM mem n s
/-- w = ⟨x⟩（長さ 1 の列）。 -/
def SingSeq (w x : α) : Prop :=
  ∃ one, Num mem 1 one ∧ SeqWith mem w one (fun _ => True) ∧ ∃ z0, Empty mem z0 ∧ At mem w z0 (fun u => u = x)
/-- ((Θ, ⟨m⟩), v) ∈ Fn。 -/
def ThetaValue (Fn m v : α) : Prop :=
  ∃ r, mem r Fn ∧ ∃ tw v', Pair mem r tw v' ∧ v' = v ∧ ∃ t w, Pair mem tw t w ∧ SymTheta mem t ∧ SingSeq mem w m
def DepOnlyS (Ns D Z i : α) : Prop :=
  ∀ sg, mem sg Z → ∀ sg2, (AssignM mem Ns D sg2 ∧ At mem sg i (fun u => At mem sg2 i (fun u2 => u = u2))) → mem sg2 Z
def GoodS (Ns D Z a : α) : Prop :=
  ∀ i, mem i Ns → (DepOnlyS mem Ns D Z i ∧ ∃ sg, mem sg Z) →
    ∀ sg, AssignM mem Ns D sg → ∃ sg3, UpdateM mem Ns D sg i a sg3 ∧ mem sg3 Z
/-- v は式 s について good な元のうち <_λ で最小のもの。 -/
def LeastGood (s v D E Cn Fn Rel WL : α) : Prop :=
  ∃ h, SeqWith mem s h (fun _ => True) ∧ ∃ Ns, VarSet mem s h Ns ∧ ∃ Z,
    (∀ sg, mem sg Z ↔ (AssignM mem Ns D sg ∧ SatM mem s D E Cn Fn Rel sg)) ∧ mem v D ∧ GoodS mem Ns D Z v ∧
    ∀ a, mem a D → GoodS mem Ns D Z a → a = v ∨ InPair mem WL v a
/-- Fn の Θ の部分が規則に従う。 -/
def ThetaLM (D E Cn Fn Rel WL : α) : Prop :=
  ∀ m, mem m D → ∃ v, mem v D ∧ ThetaValue mem Fn m v ∧
    ((∃ s, FormulaMinusM mem s ∧ MetaCodeM mem m s ∧ LeastGood mem s v D E Cn Fn Rel WL) ∨
      (¬ FormulaCodeMinus mem m ∧ Empty mem v))

/-! ### CNF の比較の層（cnf.py）の意図した条件 -/
/-- i > 0 のとき CNF(i) = ω^{CNF(a)} + CNF(b)。 -/
def DecM (i a b : α) : Prop :=
  ¬ Empty mem i ∧ ∃ i1, Succ mem i i1 ∧ ∃ p, PrimeM mem p ∧ Divides mem p i1 ∧
    (∀ q, mem q p → ¬ (PrimeM mem q ∧ Divides mem q i1)) ∧
    ∃ v, Succ mem a v ∧ ∃ pv, Op mem 3 p v pv ∧ ∃ j, Op mem 2 pv j i1 ∧ Succ mem b j ∧ ¬ Divides mem p j
/-- r は長さ 4 の自然数の列で、第 0 成分が k0。 -/
def RowShape (k0 : Nat) (r : α) : Prop :=
  (∃ four, Num mem 4 four ∧ SeqWith mem r four (NatM mem)) ∧ Comp mem r 0 (fun u => Num mem k0 u)
/-- 表 T の行 (0, x, u, u′) について body u u′。 -/
def RowGet0 (T x : α) (body : α → α → Prop) : Prop :=
  ∃ r, mem r T ∧ RowShape mem 0 r ∧ Comp mem r 1 (fun u => u = x) ∧ Comp mem r 2 (fun u => Comp mem r 3 (fun u' => body u u'))
/-- 表 T の行 (1, x, y, c) について body c。 -/
def RowGet1 (T x y : α) (body : α → Prop) : Prop :=
  ∃ r, mem r T ∧ RowShape mem 1 r ∧ Comp mem r 1 (fun u => u = x) ∧ Comp mem r 2 (fun u => u = y) ∧ Comp mem r 3 body
def HrOk (T i h rr : α) : Prop :=
  ∃ a, mem a i ∧ ∃ b, mem b i ∧ DecM mem i a b ∧
    ((Empty mem b ∧ h = a ∧ Empty mem rr) ∨
     (¬ Empty mem b ∧ RowGet0 mem T b (fun hb rb => RowGet1 mem T hb a (fun c =>
        (Num mem 2 c ∧ h = hb ∧ rr = rb) ∨ (¬ Num mem 2 c ∧ h = a ∧ rr = b)))))
def CmpOk (T i k c : α) : Prop :=
  (((Empty mem i ∧ Empty mem k ∧ Num mem 1 c) ∨ (Empty mem i ∧ ¬ Empty mem k ∧ Num mem 0 c)) ∨
    (¬ Empty mem i ∧ Empty mem k ∧ Num mem 2 c)) ∨
  (¬ Empty mem i ∧ ¬ Empty mem k ∧ RowGet0 mem T i (fun hi ri => RowGet0 mem T k (fun hk rk =>
    RowGet1 mem T hi hk (fun c1 => (¬ Num mem 1 c1 ∧ c = c1) ∨ (Num mem 1 c1 ∧ RowGet1 mem T ri rk (fun c2 => c2 = c))))))
/-- 計算表 T の各行が正当化されている。 -/
def TableOk (T : α) : Prop :=
  ∀ r, mem r T → Comp mem r 0 (fun kk => Comp mem r 1 (fun xv => Comp mem r 2 (fun yv => Comp mem r 3 (fun zv =>
    (Num mem 0 kk ∧ HrOk mem T xv yv zv) ∨ (Num mem 1 kk ∧ CmpOk mem T xv yv zv)))))
def CnfCmp (i k c : α) : Prop := ∃ T, TableOk mem T ∧ RowGet1 mem T i k (fun c2 => c2 = c)
def CnfLt (i k : α) : Prop := ∃ c, Num mem 0 c ∧ CnfCmp mem i k c

/-! ### 順序数・到達不能基数の層（ordinals.py・inacc_seq.py）の意図した条件 -/
def OmegaM (w : α) : Prop :=
  OrdinalM mem w ∧ ¬ Empty mem w ∧ ¬ IsSucc mem w ∧ ∀ z, mem z w → Empty mem z ∨ IsSucc mem z
def FuncM (f A B : α) : Prop :=
  (∀ q, mem q f → ∃ a b, Pair mem q a b ∧ mem a A ∧ mem b B) ∧ (∀ a, mem a A → At mem f a (fun b => mem b B)) ∧
  (∀ q1, mem q1 f → ∀ a1 b1, Pair mem q1 a1 b1 → ∀ q2, mem q2 f → ∀ a2 b2, Pair mem q2 a2 b2 → a1 = a2 → b1 = b2)
def BijM (f A B : α) : Prop :=
  FuncM mem f A B ∧ (∀ b, mem b B → ∃ a, mem a A ∧ At mem f a (fun v => v = b)) ∧
  (∀ q1, mem q1 f → ∀ a1 b1, Pair mem q1 a1 b1 → ∀ q2, mem q2 f → ∀ a2 b2, Pair mem q2 a2 b2 → b1 = b2 → a1 = a2)
def RegularM (lam : α) : Prop :=
  ∀ beta, mem beta lam → ∀ f, FuncM mem f beta lam → ∃ g, mem g lam ∧ ∀ d, mem d beta → At mem f d (fun v => mem v g)
/-- a = P(b)。 -/
def PowerOf (a b : α) : Prop := mem b a ∧ ∀ z, (mem z a ↔ ∀ u, mem u z → mem u b)
def StrongLimitM (lam : α) : Prop :=
  ∀ beta, mem beta lam → ∃ pb, PowerOf mem pb beta ∧ ∃ g, mem g lam ∧ ∃ h, BijM mem h pb g
def InaccM (lam : α) : Prop :=
  OrdinalM mem lam ∧ (∃ w, OmegaM mem w ∧ mem w lam) ∧ RegularM mem lam ∧ StrongLimitM mem lam
/-- f は W 上の関数（値は任意）。 -/
def FuncDom (f W : α) : Prop :=
  (∀ q, mem q f → ∃ a b, Pair mem q a b ∧ mem a W) ∧
  (∀ q1, mem q1 f → ∀ a1 b1, Pair mem q1 a1 b1 → ∀ q2, mem q2 f → ∀ a2 b2, Pair mem q2 a2 b2 → a1 = a2 → b1 = b2)
/-- O(i) = { O(k) : k ∈ W, CNF(k) < CNF(i) }。 -/
def OOk (Of W : α) : Prop :=
  FuncDom mem Of W ∧ ∀ i, mem i W → At mem Of i (fun x =>
    (∀ y, mem y x → ∃ k, mem k W ∧ CnfLt mem k i ∧ At mem Of k (fun ok => ok = y)) ∧
    ∀ k, mem k W → CnfLt mem k i → At mem Of k (fun ok => mem ok x))
def OrdOf (i x : α) : Prop := ∃ w, OmegaM mem w ∧ ∃ Of, OOk mem Of w ∧ At mem Of i (fun v => v = x)
/-- L(β) は β 番目の到達不能基数。 -/
def LamOk (Lf E : α) : Prop :=
  FuncDom mem Lf E ∧ ∀ beta, mem beta E → At mem Lf beta (fun lam =>
    InaccM mem lam ∧ (∀ g, mem g beta → At mem Lf g (fun lg => mem lg lam)) ∧
    ∀ mu, mem mu lam → InaccM mem mu → ∃ g, mem g beta ∧ At mem Lf g (fun lg => mem mu lg ∨ mu = lg))
def Eps0M (E : α) : Prop :=
  ∃ w, OmegaM mem w ∧ ∃ Of, OOk mem Of w ∧
    (∀ y, mem y E → ∃ i, mem i w ∧ At mem Of i (fun v => v = y)) ∧ ∀ i, mem i w → At mem Of i (fun v => mem v E)
def LamOf (beta lam : α) : Prop := ∃ E, Eps0M mem E ∧ ∃ Lf, LamOk mem Lf E ∧ At mem Lf beta (fun v => v = lam)

/-! ### 構造 U(α) の層（structure.py・lorder.py の struct_rec・struct_full）の意図した条件 -/
def VVal (R gm X : α) : Prop :=
  (Empty mem gm → Empty mem X) ∧
  (∀ b0, mem b0 gm → Succ mem b0 gm → At mem R b0 (fun Y => PowerOf mem X Y)) ∧
  ((¬ Empty mem gm ∧ ¬ IsSucc mem gm) →
    (∀ y, mem y X → ∃ b, mem b gm ∧ At mem R b (fun Y => mem y Y)) ∧ ∀ b, mem b gm → At mem R b (fun Y => ∀ y, mem y Y → mem y X))
/-- D = V_λ。 -/
def VStage (lam D : α) : Prop :=
  OrdinalM mem lam ∧ ∃ l1, Succ mem lam l1 ∧ ∃ R, FuncDom mem R l1 ∧
    (∀ g, mem g l1 → At mem R g (fun X => VVal mem R g X)) ∧ At mem R lam (fun X => X = D)
/-- Cn = { (c, ∅) : c は定数記号 }。 -/
def CnOk (Cn : α) : Prop :=
  (∀ q, mem q Cn → ∃ t v, Pair mem q t v ∧ Tuple4 mem t ∧ SymConst mem t ∧ Empty mem v) ∧
  ∀ t, (Tuple4 mem t ∧ SymConst mem t) → ∃ q, mem q Cn ∧ ∃ z, Empty mem z ∧ Pair mem q t z
def IsU (t : α) : Prop := CompIs mem t 0 8 ∧ CompIs mem t 1 2 ∧ CompIs mem t 2 0 ∧ CompIs mem t 3 1
def IsF (t : α) : Prop := CompIs mem t 0 8 ∧ CompIs mem t 1 4
/-- v = U(x)：x が順序数で x ∈ α なら SU(x)、そうでなければ ∅。 -/
def UVal (alpha SU x v : α) : Prop :=
  (OrdinalM mem x ∧ mem x alpha ∧ At mem SU x (fun s => s = v)) ∨ (¬ (OrdinalM mem x ∧ mem x alpha) ∧ Empty mem v)
def FnEntry (D alpha SU t w v : α) : Prop :=
  Tuple4 mem t ∧
    (((IsF mem t ∧ Comp mem t 3 (fun ar => SeqWith mem w ar (fun u => mem u D)) ∧ Empty mem v) ∨
      (IsU mem t ∧ ∃ x, mem x D ∧ SingSeq mem w x ∧ UVal mem alpha SU x v)) ∨
     (SymTheta mem t ∧ ∃ x, mem x D ∧ SingSeq mem w x ∧ mem v D))
/-- 関数記号の解釈 Fn。 -/
def FnOk (Fn D alpha SU : α) : Prop :=
  (∀ q, mem q Fn → ∃ tw v, Pair mem q tw v ∧ ∃ t w, Pair mem tw t w ∧ FnEntry mem D alpha SU t w v) ∧
  (∀ t, (Tuple4 mem t ∧ IsF mem t) → Comp mem t 3 (fun ar => ∀ w, SeqWith mem w ar (fun u => mem u D) →
    ∃ q, mem q Fn ∧ ∃ tw v, Pair mem q tw v ∧ Pair mem tw t w)) ∧
  (∀ t, (Tuple4 mem t ∧ IsU mem t) → ∀ x, mem x D → ∃ w, SingSeq mem w x ∧
    ∃ q, mem q Fn ∧ ∃ tw v, Pair mem q tw v ∧ Pair mem tw t w) ∧
  (∃ Th, ((∀ q, mem q Th → ∃ a b, Pair mem q a b ∧ ThetaValue mem Fn a b) ∧
      (∀ r, mem r Fn → ∃ tw v, Pair mem r tw v ∧ ∃ t w, Pair mem tw t w ∧
        (SymTheta mem t → ∃ x, mem x D ∧ SingSeq mem w x ∧ ∃ q, mem q Th ∧ Pair mem q x v))) ∧
    FuncM mem Th D D) ∧
  (∀ q1, mem q1 Fn → ∀ a1 b1, Pair mem q1 a1 b1 → ∀ q2, mem q2 Fn → ∀ a2 b2, Pair mem q2 a2 b2 → a1 = a2 → b1 = b2)
/-- x = ((D, E), (Cn, (Fn, Rel))) のとき body D E Cn Fn Rel。 -/
def StructParts (x : α) (body : α → α → α → α → α → Prop) : Prop :=
  ∃ de rest, Pair mem x de rest ∧ ∃ D E, Pair mem de D E ∧ ∃ Cn fr, Pair mem rest Cn fr ∧
    ∃ Fn Rel, Pair mem fr Fn Rel ∧ body D E Cn Fn Rel
/-- U(γ) の各成分の条件。 -/
def LevelM (SU g D E Cn Fn Rel : α) : Prop :=
  ∃ lam, LamOf mem g lam ∧ VStage mem lam D ∧ ERestrict mem D E ∧ CnOk mem Cn ∧ Empty mem Rel ∧
    FnOk mem Fn D g SU ∧ ∃ WL, LOrderM mem lam D WL ∧ ThetaLM mem D E Cn Fn Rel WL
/-- SU は α+1 上の関数で、SU(γ) は U(γ)。 -/
def StructRec (alpha SU : α) : Prop :=
  ∃ a1, Succ mem alpha a1 ∧ FuncDom mem SU a1 ∧
    ∀ g, mem g a1 → At mem SU g (fun x => StructParts mem x (fun D E Cn Fn Rel => LevelM mem SU g D E Cn Fn Rel))
/-- (D, E, Cn, Fn, Rel) は U(CNF(i))。 -/
def StructFull (i D E Cn Fn Rel : α) : Prop :=
  ∃ alpha, OrdOf mem i alpha ∧ ∃ SU, StructRec mem alpha SU ∧
    At mem SU alpha (fun x => StructParts mem x (fun D2 E2 Cn2 Fn2 Rel2 => D2 = D ∧ E2 = E ∧ Cn2 = Cn ∧ Fn2 = Fn ∧ Rel2 = Rel))

/-! ### f と LNGN_I の層（ffunc.py）の意図した条件 -/
/-- f は K 上の関数（値は任意）。 -/
def FuncOn2 (f K : α) : Prop :=
  (∀ q, mem q f → ∃ k a, Pair mem q k a ∧ mem k K) ∧ (∀ k, mem k K → At mem f k (fun _ => True)) ∧
  (∀ q1, mem q1 f → ∀ a1 b1, Pair mem q1 a1 b1 → ∀ q2, mem q2 f → ∀ a2 b2, Pair mem q2 a2 b2 → a1 = a2 → b1 = b2)
def StructTable (n ST : α) : Prop :=
  FuncOn2 mem ST n ∧ ∀ i, mem i n → At mem ST i (fun x => StructParts mem x (fun D E Cn Fn Rel => StructFull mem i D E Cn Fn Rel))
/-- S = { m ∈ ℕ : ∃ i ∈ n ∃ c ∈ n ∃ P (P ∈ Formula ∧ c = MetaCode(P) ∧ ST(i) で P が m を定義する) }。 -/
def DefinableSet (n ST S : α) : Prop :=
  ∀ m, (mem m S ↔ (NatM mem m ∧ ∃ i, mem i n ∧ At mem ST i (fun x => StructParts mem x (fun D E Cn Fn Rel =>
    ∃ c, mem c n ∧ ∃ s, FormulaM mem s ∧ MetaCodeM mem c s ∧ DefinableInM mem s D E Cn Fn Rel m))))
/-- v = Σ S。 -/
def FiniteSum (S v : α) : Prop :=
  ∃ K, NatM mem K ∧ (∀ x, mem x S → mem x K) ∧ ∃ K1, Succ mem K K1 ∧ ∃ R, FuncOn2 mem R K1 ∧
    (∃ x, Empty mem x ∧ At mem R x (fun a => Empty mem a)) ∧
    (∀ k, mem k K → ∀ k1, mem k1 K1 → Succ mem k k1 → At mem R k (fun a => At mem R k1 (fun b =>
      (mem k S → Op mem 1 a k b) ∧ (¬ mem k S → b = a)))) ∧
    At mem R K (fun a => a = v)
/-- v = f(n)。 -/
def FValM (n v : α) : Prop := ∃ ST, StructTable mem n ST ∧ ∃ S, DefinableSet mem n ST S ∧ FiniteSum mem S v
/-- x = f^10(a)。 -/
def Iterate10 (a x : α) : Prop :=
  ∃ t, Num mem 10 t ∧ ∃ t1, Succ mem t t1 ∧ ∃ G, FuncOn2 mem G t1 ∧ (∃ z, Empty mem z ∧ At mem G z (fun g0 => g0 = a)) ∧
    (∀ j, mem j t → ∀ j1, mem j1 t1 → Succ mem j j1 → At mem G j (fun gj => At mem G j1 (fun gj1 => FValM mem gj gj1))) ∧
    At mem G t (fun g => g = x)
/-- x = LNGN_I = f^10(10↑^10 10)。 -/
def LngnM (x : α) : Prop :=
  ∃ a, (∃ n12, Num mem 12 n12 ∧ ∃ n10, Num mem 10 n10 ∧ Hyper mem n12 n10 n10 a) ∧ Iterate10 mem a x

def Rstd : Nm → List α → Prop
  | .empty, [a] => Empty mem a
  | .succ, [b, c] => Succ mem b c
  | .trans, [a] => Trans mem a
  | .pair, [p, a, b] => Pair mem p a b
  | .is_one, [z] => IsOne mem z
  | .numeral0, [v] => Num mem 0 v
  | .numeral1, [v] => Num mem 1 v
  | .numeral2, [v] => Num mem 2 v
  | .numeral3, [v] => Num mem 3 v
  | .numeral4, [v] => Num mem 4 v
  | .nat, [a] => NatM mem a
  | .triple, [p, n, b, v] => Triple mem p n b v
  | .hyper_table, [t, a] => HyperTable mem t a
  | .hyper, [n, a, b, c] => Hyper mem n a b c
  | .add, [a, b, c] => Op mem 1 a b c
  | .mul, [a, b, c] => Op mem 2 a b c
  | .exp, [a, b, c] => Op mem 3 a b c
  | .divides, [d, m] => Divides mem d m
  | .prime, [p] => PrimeM mem p
  | .prime_table, [t] => PrimeTable mem t
  | .nth_prime, [i, p] => NthPrime mem i p
  | .seqfun, [s, h] => SeqWith mem s h (NatM mem)
  | .prod_table, [t, s] => ProdTable mem t s
  | .encode, [s, c] => EncodeM mem s c
  | .tuple4, [t] => Tuple4 mem t
  | .metacode, [n, s] => MetaCodeM mem n s
  | .numeral5, [v] => Num mem 5 v
  | .numeral6, [v] => Num mem 6 v
  | .numeral7, [v] => Num mem 7 v
  | .numeral8, [v] => Num mem 8 v
  | .numeral9, [v] => Num mem 9 v
  | .punct0, [t] => PunctM mem 0 t
  | .punct1, [t] => PunctM mem 1 t
  | .punct2, [t] => PunctM mem 2 t
  | .punct3, [t] => PunctM mem 3 t
  | .punct4, [t] => PunctM mem 4 t
  | .punct5, [t] => PunctM mem 5 t
  | .symvar, [t] => SymVar mem t
  | .symconst, [t] => SymConst mem t
  | .symfunc, [t] => SymFunc mem t
  | .symrel, [t] => SymRel mem t
  | .symelem, [t] => SymElem mem t
  | .symtheta, [t] => SymTheta mem t
  | .plus2, [n, k] => Plus2 mem n k
  | .certificate, [s, C, K0, K1] => CertOk mem s C K0 K1
  | .formula, [s] => FormulaM mem s
  | .formula_minus, [s] => FormulaMinusM mem s
  | .assign, [Ns, dom, sg] => AssignM mem Ns dom sg
  | .update, [Ns, dom, sg, k, a, sg2] => UpdateM mem Ns dom sg k a sg2
  | .in_s, [S, i, j, sg] => InS mem S i j sg
  | .in_pair, [X, a, b] => InPair mem X a b
  | .in_triple, [X, a, b, c] => InTriple mem X a b c
  | .cons, [v, w2, w] => ConsM mem v w2 w
  | .term_clause, [s, Cn, Fn, TV, i, j, sg, v] => TermClauseM mem s Cn Fn TV i j sg v
  | .list_clause, [C, K0, TV, i, j, n, sg, w] => ListClauseM mem C K0 TV i j n sg w
  | .formula_clause, [s, dom, E, Rel, Ns, C, K0, K1, TV, S, i, j, sg] => FormClauseM mem s dom E Rel Ns C K0 K1 TV S i j sg
  | .tv_ok, [s, dom, Cn, Fn, Ns, C, K0, TV] => TvOk mem s dom Cn Fn Ns C K0 TV
  | .s_ok, [s, dom, E, Rel, Ns, C, K0, K1, TV, S] => SOk mem s dom E Rel Ns C K0 K1 TV S
  | .varset, [s, h, Ns] => VarSet mem s h Ns
  | .sat, [s, dom, E, Cn, Fn, Rel, sg] => SatM mem s dom E Cn Fn Rel sg
  | .sat_ext, [s, dom, E, Cn, Fn, Rel, sg] => SatExtM mem s dom E Cn Fn Rel sg
  | .assign_w, [W, dom, sg] => AssignM mem W dom sg
  | .update_w, [W, dom, sg, k, a, sg2] => UpdateM mem W dom sg k a sg2
  | .is_definition, [s, dom, E, Cn, Fn, Rel] => IsDefM mem s dom E Cn Fn Rel
  | .param_true, [s, dom, E, Cn, Fn, Rel, m] => ParamTrueM mem s dom E Cn Fn Rel m
  | .definable_in, [s, dom, E, Cn, Fn, Rel, m] => DefinableInM mem s dom E Cn Fn Rel m
  | .ordinal, [x] => OrdinalM mem x
  | .e_restrict, [D, E] => ERestrict mem D E
  | .func_on, [f, K, X] => AssignM mem K X f
  | .in_pair_l, [X, a, b] => InPair mem X a b
  | .pure, [s, h] => Pure mem s h
  | .def_code, [n] => DefCode mem n
  | .defines, [n, tau, X, y] => DefinesM mem n tau X y
  | .lex_less, [tau, tau2, Wg] => LexLess mem tau tau2 Wg
  | .def_less, [n, tau, n2, tau2, Wg] => DefLess mem n tau n2 tau2 Wg
  | .def_table, [X, DT] => DefTable mem X DT
  | .new_less, [a, b, DT, Wg] => NewLess mem a b DT Wg
  | .step, [X, Wg, X1, W1] => StepM mem X Wg X1 W1
  | .l_order, [lam, D, WL] => LOrderM mem lam D WL
  | .formula_code_minus, [n] => FormulaCodeMinus mem n
  | .theta_value, [Fn, m, v] => ThetaValue mem Fn m v
  | .least_good, [s, v, D, E, Cn, Fn, Rel, WL] => LeastGood mem s v D E Cn Fn Rel WL
  | .theta_l, [D, E, Cn, Fn, Rel, WL] => ThetaLM mem D E Cn Fn Rel WL
  | .numeral10, [v] => Num mem 10 v
  | .numeral11, [v] => Num mem 11 v
  | .numeral12, [v] => Num mem 12 v
  | .dec, [i, a, b] => DecM mem i a b
  | .row_shape0, [r] => RowShape mem 0 r
  | .row_shape1, [r] => RowShape mem 1 r
  | .table_ok, [T] => TableOk mem T
  | .cnf_cmp, [i, k, c] => CnfCmp mem i k c
  | .cnf_lt, [i, k] => CnfLt mem i k
  | .omega, [w] => OmegaM mem w
  | .func, [f, A, B] => FuncM mem f A B
  | .bij, [f, A, B] => BijM mem f A B
  | .regular, [l] => RegularM mem l
  | .power_of, [a, b] => PowerOf mem a b
  | .strong_limit, [l] => StrongLimitM mem l
  | .inaccessible, [l] => InaccM mem l
  | .o_ok, [Of, W] => OOk mem Of W
  | .ord_of, [i, x] => OrdOf mem i x
  | .lam_ok, [Lf, E] => LamOk mem Lf E
  | .eps0, [E] => Eps0M mem E
  | .lam_of, [b, l] => LamOf mem b l
  | .vstage, [l, D] => VStage mem l D
  | .cn_ok, [Cn] => CnOk mem Cn
  | .theta_ok, [Th, D] => FuncM mem Th D D
  | .fn_ok, [Fn, D, a, SU] => FnOk mem Fn D a SU
  | .struct_rec, [a, SU] => StructRec mem a SU
  | .struct_full, [i, D, E, Cn, Fn, Rel] => StructFull mem i D E Cn Fn Rel
  | .func_on2, [f, K] => FuncOn2 mem f K
  | .struct_table, [n, ST] => StructTable mem n ST
  | .definable_set, [n, ST, S] => DefinableSet mem n ST S
  | .finite_sum, [S, v] => FiniteSum mem S v
  | .f_val, [n, v] => FValM mem n v
  | .iterate10, [a, x] => Iterate10 mem a x
  | .lngn, [x] => LngnM mem x
  | _, _ => False

/-! ### 有界量化の書き換えに使う、順序対の基本事実 -/

theorem pair_dbl {p a b : α} (h : Pair mem p a b) : ∃ s, mem s p ∧ mem a s ∧ mem b s := by
  obtain ⟨_, _, s, hs, ha, hb, _⟩ := h
  exact ⟨s, hs, ha, hb⟩

theorem triple_path {p n b v : α} (h : Triple mem p n b v) :
    ∃ s1, mem s1 p ∧ ∃ q, mem q s1 ∧ mem v s1 ∧ ∃ s2, mem s2 q ∧ mem n s2 ∧ mem b s2 := by
  obtain ⟨q, h1, h2⟩ := h
  obtain ⟨s1, hs1, hq, hv⟩ := pair_dbl mem h1
  obtain ⟨s2, hs2, hn, hb⟩ := pair_dbl mem h2
  exact ⟨s1, hs1, q, hq, hv, s2, hs2, hn, hb⟩

end

theorem orImp {a b : Prop} : (a ∨ b) ↔ (¬ a → b) := by
  by_cases h : a <;> simp [h]

end Tr
