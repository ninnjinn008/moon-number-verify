/-
  書き写しの検証（改訂52）：構造 U(α) の各成分（e_restrict・cn_ok・Rel = ∅・fn_ok）から、
  充足関係の層が要求する「集合が G5 の構造を表す」条件 Rep5 が成り立つこと。

  ・sModel：Fn から作る G5 の構造（∈ は本物の ∈、定数は ∅、関数記号 f の値は Fn の中の値、関係は空）。
  ・rep5_struct：e_restrict・cn_ok・Rel = ∅・fn_ok と、∅ ∈ D、U の値が D に入ることから Rep5。
  ・theta_model：Fn の Θ の値（((Θ, ⟨m⟩), v) ∈ Fn）は、sModel の Θ の解釈の値と一致する。
  ・struct_henkin：さらに theta_L と <_λ の整列性があれば、sModel の Θ は Henkin 公理（読み 1）を満たす。
-/
import TrTh
namespace Tr
open G5 (Form Occ Tok)

theorem get?_lt {β : Type} {l : List β} {i : Nat} {a : β} (h : l.get? i = some a) : i < l.length := by
  rw [List.get?_eq_getElem?] at h
  by_cases hc : i < l.length
  · exact hc
  · rw [List.getElem?_eq_none (by omega)] at h; cases h
theorem get?_ex {β : Type} {l : List β} {i : Nat} (h : i < l.length) : ∃ a, l.get? i = some a :=
  ⟨l[i], by rw [List.get?_eq_getElem?, List.getElem?_eq_getElem h]⟩
theorem get?_map_range {β : Type} (f : Nat → β) (n i : Nat) :
    ((List.range n).map f).get? i = if i < n then some (f i) else none := by
  by_cases h : i < n
  · simp [h, List.get?_eq_getElem?, List.getElem?_range]
  · simp [h, List.get?_eq_getElem?, List.getElem?_range]; omega

/-- 関数記号の記号の 4 つ組。 -/
theorem tok_fn_cases {g : Nat → Nat} {f a : Nat} (h : tok g = some (.fn f a)) :
    (f = 0 ∧ a = 1 ∧ g 0 = 8 ∧ g 1 = 2 ∧ g 2 = 0 ∧ g 3 = 1) ∨ (f = 1 ∧ a = 1 ∧ g 0 = 8 ∧ g 1 = 3 ∧ g 2 = 0 ∧ g 3 = 1) ∨
    (g 0 = 8 ∧ g 1 = 4 ∧ f = g 2 + 2 ∧ a = g 3) := by
  unfold tok at h; rw [dec_fn] at h
  rcases h with ⟨h0, h1, h2, h3, rfl, rfl⟩ | ⟨h0, h1, h2, h3, rfl, rfl⟩ | ⟨h0, h1, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, h0, h1, h2, h3⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, h0, h1, h2, h3⟩)
  · exact Or.inr (Or.inr ⟨h0, h1, rfl, rfl⟩)

theorem tok_fn_agree {g g' : Nat → Nat} {f a : Nat} (h : tok g = some (.fn f a)) (h' : tok g' = some (.fn f a)) :
    ∀ j, j < 4 → g j = g' j := by
  intro j hj
  rcases tok_fn_cases h with ⟨e1, e2, a0, a1, a2, a3⟩ | ⟨e1, e2, a0, a1, a2, a3⟩ | ⟨a0, a1, e1, e2⟩ <;>
  rcases tok_fn_cases h' with ⟨e1', e2', b0, b1, b2, b3⟩ | ⟨e1', e2', b0, b1, b2, b3⟩ | ⟨b0, b1, e1', e2'⟩ <;>
  (match j, hj with
   | 0, _ => omega
   | 1, _ => omega
   | 2, _ => omega
   | 3, _ => omega)

namespace Model
variable {α : Type} (M : Model α)

/-! ### 列を表す集合 -/

theorem repL_set_unique {w w' : α} {l : List α} (h : M.RepL w l) (h' : M.RepL w' l) : w = w' := by
  apply M.ext; intro x; constructor
  · intro hx
    obtain ⟨i, a, hg, hp⟩ := h.1 x hx
    obtain ⟨x', hx', hp'⟩ := h'.2 i a hg
    rw [M.pair_ext hp hp']; exact hx'
  · intro hx
    obtain ⟨i, a, hg, hp⟩ := h'.1 x hx
    obtain ⟨x', hx', hp'⟩ := h.2 i a hg
    rw [M.pair_ext hp hp']; exact hx'

theorem seqWith_of_repL {w : α} {l : List α} (V : α → Prop) (h : M.RepL w l) (hV : ∀ a, a ∈ l → V a) :
    SeqWith M.mem w (M.num l.length) V := by
  refine ⟨M.natM_num _, fun q hq => ?_, fun i hi => ?_, fun q1 hq1 i1 a1 hp1 q2 hq2 i2 a2 hp2 e => ?_⟩
  · obtain ⟨i, a, hg, hp⟩ := h.1 q hq
    exact ⟨M.num i, a, hp, M.num_lt (get?_lt hg), hV a (List.get?_mem hg)⟩
  · obtain ⟨j, hj, rfl⟩ := (M.num_mem _ i).mp hi
    obtain ⟨a, hg⟩ := get?_ex hj
    obtain ⟨x, hx, hp⟩ := h.2 j a hg
    exact ⟨x, hx, a, hp⟩
  · obtain ⟨k1, b1, hg1, hp1'⟩ := h.1 q1 hq1
    obtain ⟨k2, b2, hg2, hp2'⟩ := h.1 q2 hq2
    obtain ⟨rfl, rfl⟩ := M.pair_unique hp1 hp1'
    obtain ⟨rfl, rfl⟩ := M.pair_unique hp2 hp2'
    rw [M.num_inj e, hg2] at hg1
    exact (Option.some.inj hg1).symm

theorem repL_of_seqWith {w : α} {n : Nat} {V : α → Prop} (hs : SeqWith M.mem w (M.num n) V) :
    ∃ l : List α, M.RepL w l ∧ l.length = n ∧ ∀ a, a ∈ l → V a := by
  obtain ⟨_, helem, htot, hfun⟩ := hs
  have hex : ∀ i, ∃ a : Option α, (i < n → ∃ b, a = some b ∧ (∃ q, M.mem q w ∧ Pair M.mem q (M.num i) b) ∧ V b) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨q, hq, b, hp⟩ := htot (M.num i) (M.num_lt hi)
      obtain ⟨i', b', hp', _, hv⟩ := helem q hq
      obtain ⟨_, rfl⟩ := M.pair_unique hp hp'
      exact ⟨some b, fun _ => ⟨b, rfl, ⟨q, hq, hp⟩, hv⟩⟩
    · exact ⟨none, fun h => absurd h hi⟩
  have hf : ∀ i, i < n → ∃ b, Classical.choose (hex i) = some b ∧ (∃ q, M.mem q w ∧ Pair M.mem q (M.num i) b) ∧ V b :=
    fun i hi => Classical.choose_spec (hex i) hi
  let f : Nat → α := fun i => (Classical.choose (hex i)).getD (M.num 0)
  have hfv : ∀ i, i < n → (∃ q, M.mem q w ∧ Pair M.mem q (M.num i) (f i)) ∧ V (f i) := by
    intro i hi
    obtain ⟨b, e, hq, hv⟩ := hf i hi
    simp only [f, e, Option.getD_some]; exact ⟨hq, hv⟩
  refine ⟨(List.range n).map f, ⟨fun x hx => ?_, fun i a hg => ?_⟩, by simp, fun a ha => ?_⟩
  · obtain ⟨i, a, hp, hi, _⟩ := helem x hx
    obtain ⟨j, hj, rfl⟩ := (M.num_mem n i).mp hi
    obtain ⟨⟨q, hq, hpq⟩, _⟩ := hfv j hj
    have e := hfun x hx _ _ hp q hq _ _ hpq rfl
    refine ⟨j, a, ?_, hp⟩
    rw [get?_map_range]; simp only [hj, ite_true, e]
  · rw [get?_map_range] at hg
    by_cases hi : i < n
    · simp only [hi, ite_true, Option.some.injEq] at hg
      subst hg
      exact (hfv i hi).1
    · simp only [hi, ite_false] at hg; cases hg
  · simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact (hfv i hi).2

theorem singSeq_iff (w x : α) : SingSeq M.mem w x ↔ M.RepL w [x] := by
  constructor
  · rintro ⟨one, h1, hsw, z0, hz0, q, hq, b, hp, rfl⟩
    rw [M.num_iff] at h1; subst h1
    rw [M.empty_iff] at hz0; subst hz0
    obtain ⟨l, hl, hlen, _⟩ := M.repL_of_seqWith hsw
    match l, hlen with
    | [a], _ =>
      obtain ⟨i, a', hg, hp'⟩ := hl.1 q hq
      obtain ⟨e, rfl⟩ := M.pair_unique hp hp'
      have := M.num_inj e; subst this
      simp at hg; subst hg; exact hl
  · intro h
    refine ⟨M.num 1, (M.num_iff 1 _).mpr rfl, M.seqWith_of_repL _ h (fun _ _ => trivial), M.num 0,
      (M.empty_iff _).mpr rfl, ?_⟩
    obtain ⟨q, hq, hp⟩ := h.2 0 x rfl
    exact ⟨q, hq, x, hp, rfl⟩

/-! ### Fn から作る G5 の構造 -/

open Classical in
/-- 構造 U(α) の G5 の構造：∈ は本物の ∈、定数は ∅、関数記号の値は Fn の中の値、関係は空。 -/
noncomputable def sModel (D Fn : α) (d0 : {x // M.mem x D}) : G5.Model {x // M.mem x D} where
  E a b := M.mem a.1 b.1
  Cn _ := d0
  Fn f a ws := if h : ∃ v : {x // M.mem x D}, ∃ t w g, M.SeqRep t 4 g ∧ tok g = some (.fn f a) ∧
      M.RepL w (ws.map Subtype.val) ∧ InTriple M.mem Fn t w v.1 then Classical.choose h else d0
  Rel _ _ _ := False

section Struct
variable (Zx : M.Zax) (hM : ∀ x y, M.mem x y → M.H x)
  {D E Cn Fn Rel alpha SU : α} (hE : ERestrict M.mem D E) (hCn : CnOk M.mem Cn) (hRel : Empty M.mem Rel)
  (hFn : FnOk M.mem Fn D alpha SU) (hz : M.mem (M.num 0) D)
  (hU : ∀ x s, M.mem x D → OrdinalM M.mem x → M.mem x alpha → At M.mem SU x (fun s' => s' = s) → M.mem s D)

include hFn hz hU in
theorem fn_dom {t w v : α} (h : InTriple M.mem Fn t w v) : M.mem v D := by
  obtain ⟨q, hq, p, hpv, _⟩ := h
  obtain ⟨tw, v', hp, t', w', _, hent⟩ := hFn.1 q hq
  obtain ⟨rfl, rfl⟩ := M.pair_unique hpv hp
  rcases hent with ⟨_, (⟨_, _, he⟩ | ⟨_, x, hx, _, hu⟩) | ⟨_, _, _, _, hv⟩⟩
  · rw [(M.empty_iff _).mp he]; exact hz
  · rcases hu with ⟨ho, ha, hat⟩ | ⟨_, he⟩
    · exact hU x _ hx ho ha hat
    · rw [(M.empty_iff _).mp he]; exact hz
  · exact hv

include hFn in
theorem fn_uniq {t w v v' : α} (h : InTriple M.mem Fn t w v) (h' : InTriple M.mem Fn t w v') : v = v' := by
  obtain ⟨q, hq, p, hpv, hp⟩ := h
  obtain ⟨q', hq', p', hpv', hp'⟩ := h'
  exact hFn.2.2.2.2 q hq _ _ hpv q' hq' _ _ hpv' (M.pair_ext hp hp')

/-- Fn の行の記号 t は 4 つ組。 -/
theorem fn_tuple {t w v : α} (hFn : FnOk M.mem Fn D alpha SU) (h : InTriple M.mem Fn t w v) :
    ∃ g, M.SeqRep t 4 g := by
  obtain ⟨q, hq, p, hpv, hp⟩ := h
  obtain ⟨tw, v', hp1, t', w', hp2, hent⟩ := hFn.1 q hq
  obtain ⟨rfl, rfl⟩ := M.pair_unique hpv hp1
  obtain ⟨rfl, rfl⟩ := M.pair_unique hp hp2
  exact (M.tuple4_iff t).mp hent.1

include hFn in
/-- 全域性：関数記号の記号 t と、引数の個数が正しい列 w について、Fn に値がある。 -/
theorem fn_total {t w : α} {g : Nat → Nat} {f a : Nat} (ht : M.SeqRep t 4 g) (htok : tok g = some (.fn f a))
    (ws : List {x // M.mem x D}) (hlen : ws.length = a) (hws : M.RepL w (ws.map Subtype.val)) :
    ∃ v, InTriple M.mem Fn t w v := by
  have ht4 : Tuple4 M.mem t := (M.tuple4_iff t).mpr ⟨g, ht⟩
  have ci := fun k (hk : k < 4) v => M.compIs_iff ht hk v
  rcases tok_fn_cases htok with ⟨rfl, rfl, h0, h1, h2, h3⟩ | ⟨rfl, rfl, h0, h1, h2, h3⟩ | ⟨h0, h1, rfl, rfl⟩
  · -- U
    match ws, hlen with
    | [x], _ =>
      have hU' : IsU M.mem t := ⟨(ci 0 (by decide) 8).mpr h0, (ci 1 (by decide) 2).mpr h1,
        (ci 2 (by decide) 0).mpr h2, (ci 3 (by decide) 1).mpr h3⟩
      obtain ⟨w', hsw', q, hq, tw, v, hp, hp2⟩ := hFn.2.2.1 t ⟨ht4, hU'⟩ x.1 x.2
      have := M.repL_set_unique ((M.singSeq_iff w' x.1).mp hsw') hws
      subst this
      exact ⟨v, q, hq, tw, hp, hp2⟩
  · -- Θ
    match ws, hlen with
    | [x], _ =>
      obtain ⟨Th, ⟨hth1, _⟩, hfun⟩ := hFn.2.2.2.1
      obtain ⟨q, hq, y, hp, _⟩ := hfun.2.1 x.1 x.2
      obtain ⟨a', b', hp', r, hr, tw, v', hp1, _, t', w', hp2, hst, hss⟩ := hth1 q hq
      obtain ⟨rfl, rfl⟩ := M.pair_unique hp hp'
      obtain ⟨g', ht'⟩ := M.fn_tuple hFn ⟨r, hr, tw, hp1, hp2⟩
      have et : t' = t := by
        apply M.seqRep_ext' ht' ht
        obtain ⟨e0, e1, e2, e3⟩ := hst
        rw [M.compIs_iff ht' (by decide)] at e0 e1 e2 e3
        intro j hj
        match j, hj with
        | 0, _ => omega
        | 1, _ => omega
        | 2, _ => omega
        | 3, _ => omega
      subst et
      have := M.repL_set_unique ((M.singSeq_iff w' x.1).mp hss) hws
      subst this
      exact ⟨v', r, hr, tw, hp1, hp2⟩
  · -- 一般の関数記号
    have hF' : IsF M.mem t := ⟨(ci 0 (by decide) 8).mpr h0, (ci 1 (by decide) 4).mpr h1⟩
    have hft := hFn.2.1 t ⟨ht4, hF'⟩
    rw [M.comp_iff ht (by decide)] at hft
    have hsw := M.seqWith_of_repL (fun u => M.mem u D) hws (by
      intro u hu; simp only [List.mem_map] at hu; obtain ⟨b, _, rfl⟩ := hu; exact b.2)
    rw [List.length_map, hlen] at hsw
    obtain ⟨q, hq, tw, v, hp, hp2⟩ := hft w hsw
    exact ⟨v, q, hq, tw, hp, hp2⟩

include hE hCn hRel hFn hz hU hM in
/-- 構造 U(α) の成分から Rep5。 -/
theorem rep5_struct : M.Rep5 D E Cn Fn Rel (M.sModel D Fn ⟨M.num 0, hz⟩) := by
  refine ⟨fun x hx => hM x D hx, ?_, ?_, ?_, fun t w v h => M.fn_dom hFn hz hU h, ?_⟩
  · intro a b
    show InPair M.mem E a.1 b.1 ↔ M.mem a.1 b.1
    constructor
    · rintro ⟨q, hq, hpq⟩
      obtain ⟨a', b', hp', _, _, hab⟩ := hE.1 q hq
      obtain ⟨rfl, rfl⟩ := M.pair_unique hpq hp'
      exact hab
    · intro hab; exact hE.2 b.1 b.2 a.1 hab
  · intro t g k ht hk v
    show InPair M.mem Cn t v ↔ v = M.num 0
    constructor
    · rintro ⟨q, hq, hp⟩
      obtain ⟨t', v', hp', _, _, he⟩ := hCn.1 q hq
      obtain ⟨rfl, rfl⟩ := M.pair_unique hp hp'
      exact (M.empty_iff _).mp he
    · rintro rfl
      obtain ⟨q, hq, z, hz', hp⟩ := hCn.2 t ⟨(M.tuple4_iff t).mpr ⟨g, ht⟩, (M.const_iff ht).mpr ⟨k, hk⟩⟩
      rw [(M.empty_iff _).mp hz'] at hp
      exact ⟨q, hq, hp⟩
  · intro t g f a ht htok w ws hlen hws v
    obtain ⟨v0, hv0⟩ := M.fn_total hFn ht htok ws hlen hws
    have hex : ∃ v : {x // M.mem x D}, ∃ t w g, M.SeqRep t 4 g ∧ tok g = some (.fn f a) ∧
        M.RepL w (ws.map Subtype.val) ∧ InTriple M.mem Fn t w v.1 :=
      ⟨⟨v0, M.fn_dom hFn hz hU hv0⟩, t, w, g, ht, htok, hws, hv0⟩
    have hval : InTriple M.mem Fn t w ((M.sModel D Fn ⟨M.num 0, hz⟩).Fn f a ws).1 := by
      simp only [sModel, dif_pos hex]
      obtain ⟨t', w', g', ht', htok', hws', hin⟩ := Classical.choose_spec hex
      have et : t' = t := M.seqRep_ext' ht' ht (tok_fn_agree htok' htok)
      have ew : w' = w := M.repL_set_unique hws' hws
      rw [et, ew] at hin
      exact hin
    constructor
    · intro h; exact M.fn_uniq hFn h hval
    · rintro rfl; exact hval
  · intro t g r a _ _ w ws _ _
    show InPair M.mem Rel t w ↔ False
    exact ⟨fun ⟨q, hq, _⟩ => hRel q hq, False.elim⟩

include hE hCn hRel hFn hz hU hM in
/-- Fn の Θ の値は、sModel の Θ の解釈の値。 -/
theorem theta_model {m v : α} (hm : M.mem m D) (hv : ThetaValue M.mem Fn m v) :
    ((M.sModel D Fn ⟨M.num 0, hz⟩).Fn 1 1 [⟨m, hm⟩]).1 = v := by
  have R := M.rep5_struct hM hE hCn hRel hFn hz hU
  obtain ⟨r, hr, tw, v', hp1, rfl, t, w, hp2, hst, hss⟩ := hv
  obtain ⟨g, ht⟩ := M.fn_tuple hFn ⟨r, hr, tw, hp1, hp2⟩
  have htok : tok g = some (.fn 1 1) := by
    obtain ⟨e0, e1, e2, e3⟩ := hst
    rw [M.compIs_iff ht (by decide)] at e0 e1 e2 e3
    simp [tok, decode, e0, e1, e2, e3]
  have := (R.hFn t g 1 1 ht htok w [⟨m, hm⟩] rfl ((M.singSeq_iff w m).mp hss) v').mp ⟨r, hr, tw, hp1, hp2⟩
  exact this.symm

include hE hCn hRel hFn hz hU hM Zx in
/-- 構造 U(α) の Θ（sModel の Θ の解釈）は、theta_L と <_λ の整列性の下で Henkin 公理（読み 1）を満たす：
    Formula₋ の式 φ の自由変数が高々 x_i なら、φ を満たす x_i があるとき x_i := Θ(⌜φ⌝) でも φ は真。 -/
theorem struct_henkin {WL : α} (hdom : M.H D) (hwo : M.WO D WL) (hth : ThetaLM M.mem D E Cn Fn Rel WL)
    {s : α} {h : Nat} {S : Nat → Nat → Nat} (hs : M.SeqRep4 s h S)
    (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
    (hθ : ∀ n, n < h → str S h n ≠ some (.fn 1 1)) (hm : M.mem (M.num (Enc.metacode h S)) D) :
    ∀ i, (∀ k, φ.fv k → k = i) → (i ∈ NsL S h ∨ ¬ φ.fv i) → ∀ σ,
      (∃ x, φ.sat (M.sModel D Fn ⟨M.num 0, hz⟩) (G5.upd σ i x)) →
      φ.sat (M.sModel D Fn ⟨M.num 0, hz⟩)
        (G5.upd σ i ((M.sModel D Fn ⟨M.num 0, hz⟩).Fn 1 1 [⟨M.num (Enc.metacode h S), hm⟩])) := by
  have R := M.rep5_struct hM hE hCn hRel hFn hz hU
  obtain ⟨v, hval, _, hv, hhen⟩ := M.thetaL_henkin R Zx hdom hs φ hw ho hl hθ hwo hth hm
  have e : (M.sModel D Fn ⟨M.num 0, hz⟩).Fn 1 1 [⟨M.num (Enc.metacode h S), hm⟩] = ⟨v, hv⟩ :=
    Subtype.ext (M.theta_model hM hE hCn hRel hFn hz hU hm hval)
  rw [e]
  exact hhen

end Struct

end Model

#print axioms Model.rep5_struct
#print axioms Model.theta_model
#print axioms Model.struct_henkin
end Tr
