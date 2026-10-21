/-
  展開の正しさ（改訂44 で一般化）：下の層の部品を呼び出す引数に同じ変数が重なる場合（例：in_cert(C, j, j, …)）も扱う。
  付け替え sig が単射でなくても、部品の束縛変数（すべて引数の個数 k 以上）の行き先が他の変数の行き先と衝突しなければ、
  付け替えた式の評価は割当てを合成したものの評価と同じ（ev_rename2）。
-/
import TrPartsJ
import TrKer
namespace Tr

/-- 束縛変数の一覧。 -/
def bv : F → List Nat
  | .mem _ _ => []
  | .eq _ _ => []
  | .neg p => bv p
  | .conj p q => bv p ++ bv q
  | .all v p => v :: bv p
  | .rel _ _ _ => []

theorem ev_rename2 {α : Type} (mem : α → α → Prop) (R : Nm → List α → Prop) (σ : Nat → Nat) :
    ∀ (f : F), (∀ v, v ∈ bv f → ∀ x, σ x = σ v → x = v) →
      ∀ (e : Nat → α), ev mem R (rename σ f) e ↔ ev mem R f (fun n => e (σ n)) := by
  intro f
  induction f with
  | mem a b => intro _ e; exact Iff.rfl
  | eq a b => intro _ e; exact Iff.rfl
  | neg p ih => intro hb e; simp only [rename, ev]; exact not_congr (ih hb e)
  | conj p q ihp ihq =>
    intro hb e; simp only [rename, ev]
    exact and_congr (ihp (fun v hv => hb v (by simp [bv, hv])) e) (ihq (fun v hv => hb v (by simp [bv, hv])) e)
  | all v p ih =>
    intro hb e
    simp only [rename, ev]
    apply forall_congr'
    intro x
    rw [ih (fun w hw => hb w (by simp [bv, hw]))]
    have : (fun n => upd e (σ v) x (σ n)) = upd (fun n => e (σ n)) v x := by
      funext n
      simp only [upd]
      by_cases h : n = v
      · simp [h]
      · have : σ n ≠ σ v := fun h' => h (hb v (by simp [bv]) n h')
        simp [h, this]
    rw [this]
  | rel n c as => intro _ e; simp only [rename, ev, List.map_map]; exact Iff.rfl

def okArgs2 (k : Nat) (as : List Nat) (c : Nat) (g : F) : Bool :=
  as.length == k && as.all (fun a => decide (a < c)) && (bv g).all (fun v => decide (k ≤ v))

def check2 (tbl : Nm → Option (Nat × F)) : F → Bool
  | .mem _ _    => true
  | .eq _ _     => true
  | .neg p      => check2 tbl p
  | .conj p q   => check2 tbl p && check2 tbl q
  | .all _ p    => check2 tbl p
  | .rel n c as =>
    match tbl n with
    | some (k, g) => okArgs2 k as c g
    | none => false

theorem sig_ok (k : Nat) (as : List Nat) (c : Nat) (g : F) (h : okArgs2 k as c g = true) :
    ∀ v, v ∈ bv g → ∀ x, sig as c x = sig as c v → x = v := by
  simp only [okArgs2, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hk, hlt⟩, hbv⟩ := h
  intro v hv x hx
  have hvk := hbv v hv
  simp only [sig] at hx
  have hv' : ¬ v < as.length := by omega
  simp only [hv', ite_false] at hx
  by_cases hxk : x < as.length
  · simp only [hxk, ite_true] at hx
    have := hlt _ (getD_mem as x hxk); omega
  · simp only [hxk, ite_false] at hx; omega

theorem expand_ok2 {α : Type} (mem : α → α → Prop) (R0 Rs : Nm → List α → Prop)
    (tbl : Nm → Option (Nat × F))
    (htbl : ∀ n k g, tbl n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rs n ((List.range k).map e)) :
    ∀ (f : F), check2 tbl f = true → ∀ e, (ev mem R0 (expand tbl f) e ↔ ev mem Rs f e) := by
  intro f
  induction f with
  | mem a b => intro _ e; exact Iff.rfl
  | eq a b => intro _ e; exact Iff.rfl
  | neg p ih => intro hc e; simp only [expand, ev]; exact not_congr (ih hc e)
  | conj p q ihp ihq =>
    intro hc e
    simp only [check2, Bool.and_eq_true] at hc
    simp only [expand, ev]; exact and_congr (ihp hc.1 e) (ihq hc.2 e)
  | all v p ih =>
    intro hc e
    simp only [expand, ev]
    exact forall_congr' (fun x => ih hc _)
  | rel n c as =>
    intro hc e
    cases hg : tbl n with
    | none => simp [check2, hg] at hc
    | some kg =>
      obtain ⟨k, g⟩ := kg
      simp only [check2, hg] at hc
      simp only [expand, ev, hg]
      rw [ev_rename2 mem R0 _ g (sig_ok k as c g hc), htbl n k g hg]
      have hk : as.length = k := by
        simp only [okArgs2, Bool.and_eq_true, beq_iff_eq] at hc; exact hc.1.1
      subst hk
      have : (List.range as.length).map (fun n => e (sig as c n)) = as.map e := by
        have h2 := congrArg (List.map e) (map_sig as c)
        rw [List.map_map] at h2
        exact h2
      rw [this]


/-! ### 改訂48：束縛変数の条件を部品ごとの補題に分ける

  check2 は、下の層の部品の展開した式 g の束縛変数をすべて調べるので、層が深くなるとカーネルでの計算が
  重くなる（step・l_order ではメモリ 6 GB を超えた）。そこで、
  ・check3：引数の個数と、引数が c 未満であることだけを調べる（g は見ない）。
  ・g の束縛変数がすべて k 以上であること（bvOk）は、部品ごとの補題として、下の層から順に証明する。
    そのために relGe K f（f の束縛変数と下の層の呼び出しの番号 c がすべて K 以上）を小さな r_X の上で計算する。 -/

def okArgs3 (k : Nat) (as : List Nat) (c : Nat) : Bool :=
  as.length == k && as.all (fun a => decide (a < c))

def check3 (tbl : Nm → Option (Nat × F)) : F → Bool
  | .mem _ _    => true
  | .eq _ _     => true
  | .neg p      => check3 tbl p
  | .conj p q   => check3 tbl p && check3 tbl q
  | .all _ p    => check3 tbl p
  | .rel n c as =>
    match tbl n with
    | some (k, _) => okArgs3 k as c
    | none => false

def relGe (K : Nat) : F → Bool
  | .mem _ _    => true
  | .eq _ _     => true
  | .neg p      => relGe K p
  | .conj p q   => relGe K p && relGe K q
  | .all v p    => decide (K ≤ v) && relGe K p
  | .rel _ c _  => decide (K ≤ c)

/-- 表の各部品の展開した式は、束縛変数がすべて引数の個数以上。 -/
def BvOk (tbl : Nm → Option (Nat × F)) : Prop := ∀ n k g, tbl n = some (k, g) → ∀ v, v ∈ bv g → k ≤ v

theorem okArgs3_to2 (k : Nat) (as : List Nat) (c : Nat) (g : F) (h : okArgs3 k as c = true)
    (hb : ∀ v, v ∈ bv g → k ≤ v) : okArgs2 k as c g = true := by
  simp only [okArgs3, okArgs2, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h, hb⟩

theorem check3_to2 (tbl : Nm → Option (Nat × F)) (hb : BvOk tbl) :
    ∀ f, check3 tbl f = true → check2 tbl f = true := by
  intro f
  induction f with
  | mem a b => intro _; rfl
  | eq a b => intro _; rfl
  | neg p ih => intro h; exact ih h
  | conj p q ihp ihq =>
    intro h; simp only [check3, check2, Bool.and_eq_true] at h ⊢; exact ⟨ihp h.1, ihq h.2⟩
  | all v p ih => intro h; exact ih h
  | rel n c as =>
    intro h
    cases hg : tbl n with
    | none => simp [check3, hg] at h
    | some kg =>
      obtain ⟨k, g⟩ := kg
      simp only [check3, hg] at h
      simp only [check2, hg]
      exact okArgs3_to2 k as c g h (hb n k g hg)

theorem expand_ok3 {α : Type} (mem : α → α → Prop) (R0 Rs : Nm → List α → Prop)
    (tbl : Nm → Option (Nat × F))
    (htbl : ∀ n k g, tbl n = some (k, g) → ∀ e, ev mem R0 g e ↔ Rs n ((List.range k).map e))
    (hb : BvOk tbl) (f : F) (hc : check3 tbl f = true) (e : Nat → α) :
    ev mem R0 (expand tbl f) e ↔ ev mem Rs f e :=
  expand_ok2 mem R0 Rs tbl htbl f (check3_to2 tbl hb f hc) e

theorem bv_rename (σ : Nat → Nat) : ∀ f, bv (rename σ f) = (bv f).map σ := by
  intro f
  induction f with
  | mem a b => rfl
  | eq a b => rfl
  | neg p ih => exact ih
  | conj p q ihp ihq => simp [bv, rename, ihp, ihq]
  | all v p ih => simp [bv, rename, ih]
  | rel n c as => rfl

/-- 展開した式の束縛変数の下限。 -/
theorem bv_expand_ge (tbl : Nm → Option (Nat × F)) (hb : BvOk tbl) (K : Nat) :
    ∀ f, check3 tbl f = true → relGe K f = true → ∀ v, v ∈ bv (expand tbl f) → K ≤ v := by
  intro f
  induction f with
  | mem a b => intro _ _ v hv; simp [expand, bv] at hv
  | eq a b => intro _ _ v hv; simp [expand, bv] at hv
  | neg p ih => intro hc hr v hv; exact ih hc hr v hv
  | conj p q ihp ihq =>
    intro hc hr v hv
    simp only [check3, relGe, Bool.and_eq_true] at hc hr
    simp only [expand, bv, List.mem_append] at hv
    rcases hv with hv | hv
    · exact ihp hc.1 hr.1 v hv
    · exact ihq hc.2 hr.2 v hv
  | all w p ih =>
    intro hc hr v hv
    simp only [relGe, Bool.and_eq_true, decide_eq_true_eq] at hr
    simp only [expand, bv, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hr.1
    · exact ih hc hr.2 v hv
  | rel n c as =>
    intro hc hr v hv
    simp only [relGe, decide_eq_true_eq] at hr
    cases hg : tbl n with
    | none => simp [expand, hg, bv] at hv
    | some kg =>
      obtain ⟨k, g⟩ := kg
      simp only [check3, hg, okArgs3, Bool.and_eq_true, beq_iff_eq] at hc
      simp only [expand, hg, bv_rename, List.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have hkw := hb n k g hg w hw
      simp only [sig]
      have : ¬ w < as.length := by omega
      simp only [this, ite_false]
      omega

end Tr
