/-
  書き写しの検証（改訂51）：Θ の層（lorder.py の least_good・theta_L）を G14 の Θ の規則と Henkin 公理につなぐ。

  ・goodS_iff：集合の言葉の good（GoodS）は、G14 の good（Tarski の意味論での dep_only と更新）と同値。
  ・leastGood_iff：least_good(s, v, …) ⟺ v は G14 の意味で good な元のうち <_λ で最小のもの。
  ・leastGood_unique・leastGood_exists：<_λ が整列順序なら、least_good を満たす v はちょうど一つ。
  ・thetaL_henkin：theta_L が成り立てば、各 Formula₋ の式 P の番号 m について、Fn の Θ の値 v は P について最小の good な元で、
    読み 1 の Henkin 公理（P の自由変数が高々 x_i なら、P を満たす x_i があるとき x_i := v でも P は真）が成り立つ。
-/
import TrLO3
import G14
namespace Tr
open G5 (Form Occ)

namespace Model
variable {α : Type} (M : Model α)

section Good
variable {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}} {s : α} {h : Nat} {S : Nat → Nat → Nat}
  (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Zx : M.Zax) (hdom : M.H dom) (hs : M.SeqRep4 s h S)
  (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length) (d : {x // M.mem x dom})
  {Ns Z : α} (hNs : ∀ x, M.mem x Ns ↔ ∃ k, k ∈ NsL S h ∧ x = M.num k)
  (hZ : ∀ sg, M.mem sg Z ↔ (AssignM M.mem Ns dom sg ∧ SatM M.mem s dom E Cn Fn Rel sg))
include R Zx hdom hs hw ho hl hNs hZ

/-- Z の元は、割当て τ の制限 sgT τ で、τ の下で φ が真なもの。 -/
theorem memZ (τ : Nat → {x // M.mem x dom}) : M.mem (M.sgT S h τ) Z ↔ φ.sat M5 τ := by
  have hτ : ∀ k, M.H (τ k).1 := fun k => R.domH _ (τ k).2
  rw [hZ, ← M.sat_iff R Zx hdom hs φ hw ho hl τ]
  exact ⟨fun h => h.2, fun h' => ⟨M.assign_sgOf _ _ hτ Ns dom hNs (fun k => (τ k).2), h'⟩⟩

theorem depOnly_iff (k : Nat) (hk : k ∈ NsL S h) (d : {x // M.mem x dom}) :
    DepOnlyS M.mem Ns dom Z (M.num k) ↔ G5.depOnly M5 φ k := by
  have hH := R.domH
  have hτ : ∀ τ : Nat → {x // M.mem x dom}, ∀ k, M.H (τ k).1 := fun τ k => hH _ (τ k).2
  constructor
  · intro hd σ σ' e
    have side : ∀ σ σ' : Nat → {x // M.mem x dom}, σ k = σ' k → φ.sat M5 σ → φ.sat M5 σ' := by
      intro σ σ' e hσ
      have h1 := (M.memZ R Zx hdom hs φ hw ho hl hNs hZ σ).mpr hσ
      refine (M.memZ R Zx hdom hs φ hw ho hl hNs hZ σ').mp (hd _ h1 _ ⟨M.assign_sgOf _ _ (hτ σ') Ns dom hNs
        (fun k => (σ' k).2), ?_⟩)
      rw [M.at_sgT S h σ (hτ σ) k hk]
      rw [M.at_sgT S h σ' (hτ σ') k hk]
      rw [e]
    exact ⟨side σ σ' e, side σ' σ e.symm⟩
  · intro hd sg hsg sg2 ⟨hA2, hat⟩
    let σ0 : Nat → {x // M.mem x dom} := fun _ => d
    have hA := ((hZ sg).mp hsg).1
    have e1 := M.sgT_τc S h σ0 hH hNs hA
    have e2 := M.sgT_τc S h σ0 hH hNs hA2
    rw [← e1, M.at_sgT S h _ (hτ _) k hk] at hat
    rw [← e2, M.at_sgT S h _ (hτ _) k hk] at hat
    rw [← e2]
    rw [← e1] at hsg
    apply (M.memZ R Zx hdom hs φ hw ho hl hNs hZ _).mpr
    exact (hd _ _ (Subtype.ext hat)).mp ((M.memZ R Zx hdom hs φ hw ho hl hNs hZ _).mp hsg)

/-- 集合の言葉の good は、G14 の good と同値。 -/
theorem goodS_iff (a : α) (ha : M.mem a dom) :
    GoodS M.mem Ns dom Z a ↔ G5.good M5 φ (fun i => i ∈ NsL S h) ⟨a, ha⟩ := by
  have hH := R.domH
  have hτ : ∀ τ : Nat → {x // M.mem x dom}, ∀ k, M.H (τ k).1 := fun τ k => hH _ (τ k).2
  have exZ : (∃ sg, M.mem sg Z) ↔ ∃ σ, G5.Zs M5 φ σ := by
    constructor
    · rintro ⟨sg, hsg⟩
      have e := M.sgT_τc S h (fun _ => ⟨a, ha⟩) hH hNs ((hZ sg).mp hsg).1
      rw [← e] at hsg
      exact ⟨_, (M.memZ R Zx hdom hs φ hw ho hl hNs hZ _).mp hsg⟩
    · rintro ⟨σ, hσ⟩; exact ⟨_, (M.memZ R Zx hdom hs φ hw ho hl hNs hZ σ).mpr hσ⟩
  constructor
  · intro hg i hi hdep hex σ
    have hiN : M.mem (M.num i) Ns := (hNs _).mpr ⟨i, hi, rfl⟩
    obtain ⟨sg3, hu, h3⟩ := hg _ hiN ⟨(M.depOnly_iff R Zx hdom hs φ hw ho hl hNs hZ i hi ⟨a, ha⟩).mpr hdep,
      exZ.mpr hex⟩ (M.sgT S h σ) (M.assign_sgOf _ _ (hτ σ) Ns dom hNs (fun k => (σ k).2))
    rw [sgT, M.update_sgOfT hH (NsL S h) hNs σ i hi ⟨a, ha⟩ sg3] at hu
    subst hu
    exact (M.memZ R Zx hdom hs φ hw ho hl hNs hZ _).mp h3
  · intro hg i hi ⟨hdep, hex⟩ sg hA
    obtain ⟨k, hk, rfl⟩ := (hNs i).mp hi
    let σ := M.τc S h (fun _ => ⟨a, ha⟩) sg
    have e := M.sgT_τc S h (fun _ => ⟨a, ha⟩) hH hNs hA
    refine ⟨M.sgT S h (G5.upd σ k ⟨a, ha⟩), ?_, ?_⟩
    · rw [← e]
      exact (M.update_sgOfT hH (NsL S h) hNs σ k hk ⟨a, ha⟩ _).mpr rfl
    · exact (M.memZ R Zx hdom hs φ hw ho hl hNs hZ _).mpr
        (hg k hk ((M.depOnly_iff R Zx hdom hs φ hw ho hl hNs hZ k hk ⟨a, ha⟩).mp hdep) (exZ.mp hex) σ)

end Good

section Least
variable {dom E Cn Fn Rel : α} {M5 : G5.Model {x // M.mem x dom}} {s : α} {h : Nat} {S : Nat → Nat → Nat}
  (R : M.Rep5T dom E Cn Fn Rel M5 S h) (Zx : M.Zax) (hdom : M.H dom) (hs : M.SeqRep4 s h S)
  (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
include R Zx hdom hs hw ho hl

/-- least_good の意味：v は（G14 の意味で）good な元のうち <_λ で最小のもの。 -/
theorem leastGood_iff (v WL : α) :
    LeastGood M.mem s v dom E Cn Fn Rel WL ↔
      ∃ hv : M.mem v dom, G5.good M5 φ (fun i => i ∈ NsL S h) ⟨v, hv⟩ ∧
        ∀ b (hb : M.mem b dom), G5.good M5 φ (fun i => i ∈ NsL S h) ⟨b, hb⟩ → b = v ∨ InPair M.mem WL v b := by
  constructor
  · rintro ⟨h', hsw, Ns, hvs, Z, hZ, hv, hg, hleast⟩
    have eh := M.seqWith_dom (SeqRep4.dom M hs) hsw; subst eh
    have hNs := (M.varset_iff hs Ns).mp hvs
    refine ⟨hv, (M.goodS_iff R Zx hdom hs φ hw ho hl hNs hZ v hv).mp hg, fun b hb hgb => ?_⟩
    exact hleast b hb ((M.goodS_iff R Zx hdom hs φ hw ho hl hNs hZ b hb).mpr hgb)
  · rintro ⟨hv, hg, hleast⟩
    obtain ⟨_, hNs⟩ := M.Ns0_spec S h
    -- Z = { sg : 割当てで、s が真 } を作る
    obtain ⟨A, hA, hAm⟩ := M.asg_ex R Zx hdom S h
    obtain ⟨Z, _, hZm⟩ := Zx.sep A (fun sg => SatM M.mem s dom E Cn Fn Rel sg) hA
    have hZ : ∀ sg, M.mem sg Z ↔ (AssignM M.mem (M.Ns0 S h) dom sg ∧ SatM M.mem s dom E Cn Fn Rel sg) := by
      intro sg; rw [hZm, hAm]
    refine ⟨M.num h, ⟨(M.seqWith4 hs).1, fun q hq => by
        obtain ⟨i, a, hpq, hi, _⟩ := (M.seqWith4 hs).2.1 q hq; exact ⟨i, a, hpq, hi, trivial⟩,
      (M.seqWith4 hs).2.2.1, (M.seqWith4 hs).2.2.2⟩,
      M.Ns0 S h, (M.varset_iff hs _).mpr hNs, Z, hZ, hv,
      (M.goodS_iff R Zx hdom hs φ hw ho hl hNs hZ v hv).mpr hg, fun b hb hgb => ?_⟩
    exact hleast b hb ((M.goodS_iff R Zx hdom hs φ hw ho hl hNs hZ b hb).mp hgb)

/-- <_λ が狭義の整列順序なら、least_good を満たす v はちょうど一つあり、Henkin 公理を満たす。 -/
theorem leastGood_exists_unique {WL : α} (hwo : M.WO dom WL) (d : {x // M.mem x dom}) :
    ∃ v, LeastGood M.mem s v dom E Cn Fn Rel WL ∧ (∀ v', LeastGood M.mem s v' dom E Cn Fn Rel WL → v' = v) ∧
      ∃ hv : M.mem v dom, ∀ i, (∀ k, φ.fv k → k = i) → (i ∈ NsL S h ∨ ¬ φ.fv i) →
        ∀ σ, (∃ x, φ.sat M5 (G5.upd σ i x)) → φ.sat M5 (G5.upd σ i ⟨v, hv⟩) := by
  obtain ⟨_, hwf, hirr, htr, htot⟩ := hwo
  let W : {x // M.mem x dom} → {x // M.mem x dom} → Prop := fun a b => InPair M.mem WL a.1 b.1
  have wfW : WellFounded W := InvImage.wf (fun a : {x // M.mem x dom} => a.1) hwf
  obtain ⟨a0, ha0⟩ := G5.good_exists M5 φ (fun i => i ∈ NsL S h) d
  obtain ⟨θ, hθ, hmin⟩ := G5.exists_min W wfW _ a0 ha0
  have hleast : ∀ b (hb : M.mem b dom), G5.good M5 φ (fun i => i ∈ NsL S h) ⟨b, hb⟩ → b = θ.1 ∨ InPair M.mem WL θ.1 b := by
    intro b hb hgb
    by_cases e : b = θ.1
    · exact Or.inl e
    · rcases htot b θ.1 hb θ.2 e with h1 | h1
      · exact absurd hgb (hmin ⟨b, hb⟩ h1)
      · exact Or.inr h1
  have hL := (M.leastGood_iff R Zx hdom hs φ hw ho hl θ.1 WL).mpr ⟨θ.2, hθ, hleast⟩
  refine ⟨θ.1, hL, fun v' hv' => ?_, θ.2, fun i hfv hNs σ hex => G5.henkin M5 φ _ hfv θ hθ hNs σ hex⟩
  obtain ⟨hv'd, hg', hl'⟩ := (M.leastGood_iff R Zx hdom hs φ hw ho hl v' WL).mp hv'
  rcases hleast v' hv'd hg' with e | h1
  · exact e
  · rcases hl' θ.1 θ.2 hθ with e | h2
    · exact e.symm
    · exact absurd (htr _ _ _ h1 h2) (hirr θ.1)

end Least

/-! ### theta_L：Fn の Θ の部分 -/

/-- theta_L が成り立ち、<_λ が D 上の狭義の整列順序なら、Formula₋ の式 φ の番号 m ∈ D について、
    Fn の Θ の値 v（((Θ, ⟨m⟩), v) ∈ Fn）は φ について最小の good な元で、Henkin 公理を満たす。
    そのような v はただ一つ。 -/
theorem thetaL_henkin {dom E Cn Fn Rel WL : α} {M5 : G5.Model {x // M.mem x dom}} {s : α} {h : Nat}
    {S : Nat → Nat → Nat} (R : M.Rep5 dom E Cn Fn Rel M5) (Zx : M.Zax) (hdom : M.H dom) (hs : M.SeqRep4 s h S)
    (φ : Form) (hw : φ.wf) (ho : Occ (str S h) 0 φ.toks) (hl : h = φ.toks.length)
    (hθ : ∀ n, n < h → str S h n ≠ some (.fn 1 1))
    (hwo : M.WO dom WL) (hth : ThetaLM M.mem dom E Cn Fn Rel WL)
    (hm : M.mem (M.num (Enc.metacode h S)) dom) :
    ∃ v, ThetaValue M.mem Fn (M.num (Enc.metacode h S)) v ∧ LeastGood M.mem s v dom E Cn Fn Rel WL ∧
      ∃ hv : M.mem v dom, ∀ i, (∀ k, φ.fv k → k = i) → (i ∈ NsL S h ∨ ¬ φ.fv i) →
        ∀ σ, (∃ x, φ.sat M5 (G5.upd σ i x)) → φ.sat M5 (G5.upd σ i ⟨v, hv⟩) := by
  have RT := Model.Rep5.toT M R S h
  have hfm : FormulaMinusM M.mem s := (M.formula_minus_iff hs).mpr ⟨⟨φ, hw, ho, hl⟩, hθ⟩
  have hmc : MetaCodeM M.mem (M.num (Enc.metacode h S)) s := (M.metacode_iff hs _).mpr rfl
  obtain ⟨v, hv, hval, hcase⟩ := hth _ hm
  rcases hcase with ⟨s', _, hmc', hlg⟩ | ⟨hno, _⟩
  · obtain ⟨es, _⟩ := M.metacode_unique hmc' hmc
    subst es
    obtain ⟨v0, hlg0, huniq, hv0, hhen⟩ := M.leastGood_exists_unique RT Zx hdom hs φ hw ho hl hwo ⟨v, hv⟩
    have := huniq v hlg; subst this
    exact ⟨v, hval, hlg, hv0, hhen⟩
  · exact absurd ⟨s, hfm, hmc⟩ hno

/-- 番号が Formula₋ の式の番号でない m では、Θ の値は ∅。 -/
theorem thetaL_other {dom E Cn Fn Rel WL : α} (hth : ThetaLM M.mem dom E Cn Fn Rel WL) {m : α}
    (hm : M.mem m dom) (hno : ¬ FormulaCodeMinus M.mem m) :
    ∃ v, ThetaValue M.mem Fn m v ∧ Empty M.mem v := by
  obtain ⟨v, _, hval, hcase⟩ := hth m hm
  rcases hcase with ⟨s, hfm, hmc, _⟩ | ⟨_, he⟩
  · exact absurd ⟨s, hfm, hmc⟩ hno
  · exact ⟨v, hval, he⟩

end Model

#print axioms Model.goodS_iff
#print axioms Model.leastGood_iff
#print axioms Model.leastGood_exists_unique
#print axioms Model.thetaL_henkin
end Tr
