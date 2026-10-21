/-
  一意性（改訂53、その 2）：構造 U(α) の表 SU と struct_full。

  ・fn_agree：Θ 以外の記号の Fn の行は、γ より下の SU が一致すれば一致する。
  ・theta_agree：Θ の行の値は least_good で決まる。Formula₋ の式は Θ を含まないので、
    その充足は Θ 以外の行だけで決まり（Rep5T：式に現れる記号に限った表現）、二つの Fn で同じ最小元になる。
  ・structRec_unique・structFull_unique：struct_full を満たす (D, E, Cn, Fn, Rel) は高々一つ。
  仮定 SUClosed（各段の D は 0 を含み、下の段の SU の値を含む）は階数の評価で、紙の証明の補題で示す。
-/
import TrUq1
namespace Tr

namespace Model
variable {α : Type} (M : Model α)

theorem compIs_unique {t : α} {k a b : Nat} (ht : Tuple4 M.mem t) (hk : k < 4)
    (h : CompIs M.mem t k a) (h' : CompIs M.mem t k b) : a = b := by
  obtain ⟨g, hg⟩ := (M.tuple4_iff t).mp ht
  rw [M.compIs_iff hg hk] at h h'
  omega

theorem theta_sym_eq {t t' : α} (ht : Tuple4 M.mem t) (ht' : Tuple4 M.mem t')
    (h : SymTheta M.mem t) (h' : SymTheta M.mem t') : t = t' := by
  obtain ⟨g, hg⟩ := (M.tuple4_iff t).mp ht
  obtain ⟨g', hg'⟩ := (M.tuple4_iff t').mp ht'
  obtain ⟨a0, a1, a2, a3⟩ := h
  obtain ⟨b0, b1, b2, b3⟩ := h'
  rw [M.compIs_iff hg (by decide)] at a0 a1 a2 a3
  rw [M.compIs_iff hg' (by decide)] at b0 b1 b2 b3
  apply M.seqRep_ext' hg hg'
  intro j hj
  match j, hj with
  | 0, _ => omega
  | 1, _ => omega
  | 2, _ => omega
  | 3, _ => omega

theorem fn_entry {Fn D g SU t w v : α} (hFn : FnOk M.mem Fn D g SU) (h : InTriple M.mem Fn t w v) :
    FnEntry M.mem D g SU t w v := by
  obtain ⟨q, hq, p, hpv, hp⟩ := h
  obtain ⟨tw, v', hp1, t', w', hp2, hent⟩ := hFn.1 q hq
  obtain ⟨rfl, rfl⟩ := M.pair_unique hpv hp1
  obtain ⟨rfl, rfl⟩ := M.pair_unique hp hp2
  exact hent

theorem thetaValue_unique {Fn D g SU m v v' : α} (hFn : FnOk M.mem Fn D g SU)
    (h : ThetaValue M.mem Fn m v) (h' : ThetaValue M.mem Fn m v') : v = v' := by
  obtain ⟨r, hr, tw, v1, hp1, rfl, t, w, hp2, hst, hss⟩ := h
  obtain ⟨r', hr', tw', v1', hp1', rfl, t', w', hp2', hst', hss'⟩ := h'
  obtain ⟨g1, hg1⟩ := M.fn_tuple hFn ⟨r, hr, tw, hp1, hp2⟩
  obtain ⟨g2, hg2⟩ := M.fn_tuple hFn ⟨r', hr', tw', hp1', hp2'⟩
  have et : t = t' := M.theta_sym_eq ((M.tuple4_iff t).mpr ⟨g1, hg1⟩) ((M.tuple4_iff t').mpr ⟨g2, hg2⟩) hst hst'
  have ew : w = w' := M.repL_set_unique ((M.singSeq_iff w m).mp hss) ((M.singSeq_iff w' m).mp hss')
  subst et; subst ew
  exact hFn.2.2.2.2 r hr _ _ hp1 r' hr' _ _ hp1' (M.pair_ext hp2 hp2')

theorem uval_agree {g SU SU' x v v' : α} (ih : ∀ x, M.mem x g → ∀ s s', M.Look SU x s → M.Look SU' x s' → s = s')
    (h : UVal M.mem g SU x v) (h' : UVal M.mem g SU' x v') : v = v' := by
  rcases h with ⟨ho, hx, hat⟩ | ⟨hn, he⟩ <;> rcases h' with ⟨ho', hx', hat'⟩ | ⟨hn', he'⟩
  · obtain ⟨s, hl, rfl⟩ := (M.at_look _ _ _).mp hat
    obtain ⟨s', hl', rfl⟩ := (M.at_look _ _ _).mp hat'
    exact ih x hx _ _ hl hl'
  · exact absurd ⟨ho, hx⟩ hn'
  · exact absurd ⟨ho', hx'⟩ hn
  · exact M.empty_eq he he'

/-- Θ 以外の記号の行は、下の段の SU が一致すれば、もう一方の Fn にもある。 -/
theorem fn_agree {Fn Fn' D g SU SU' t w v : α} (hFn : FnOk M.mem Fn D g SU) (hFn' : FnOk M.mem Fn' D g SU')
    (ih : ∀ x, M.mem x g → ∀ s s', M.Look SU x s → M.Look SU' x s' → s = s')
    (hnt : ¬ SymTheta M.mem t) (h : InTriple M.mem Fn t w v) : InTriple M.mem Fn' t w v := by
  obtain ⟨ht4, hcase⟩ := M.fn_entry hFn h
  rcases hcase with (⟨hF, har, hv⟩ | ⟨hU, x, hx, hsx, huv⟩) | ⟨hT, _⟩
  · have hall := hFn'.2.1 t ⟨ht4, hF⟩
    obtain ⟨g4, hg4⟩ := (M.tuple4_iff t).mp ht4
    rw [M.comp_iff hg4 (by decide)] at hall har
    obtain ⟨q, hq, tw, v', hp, hp2⟩ := hall w har
    obtain ⟨_, hc'⟩ := M.fn_entry hFn' ⟨q, hq, tw, hp, hp2⟩
    rcases hc' with (⟨_, _, hv'⟩ | ⟨hU', _⟩) | ⟨hT', _⟩
    · rw [M.empty_eq hv hv']; exact ⟨q, hq, tw, hp, hp2⟩
    · exact absurd (M.compIs_unique ht4 (by decide) hF.2 hU'.2.1) (by decide)
    · exact absurd (M.compIs_unique ht4 (by decide) hF.2 hT'.2.1) (by decide)
  · obtain ⟨w', hsw', q, hq, tw, v', hp, hp2⟩ := hFn'.2.2.1 t ⟨ht4, hU⟩ x hx
    have ew : w' = w := M.repL_set_unique ((M.singSeq_iff w' x).mp hsw') ((M.singSeq_iff w x).mp hsx)
    rw [ew] at hp2
    obtain ⟨_, hc'⟩ := M.fn_entry hFn' ⟨q, hq, tw, hp, hp2⟩
    rcases hc' with (⟨hF', _⟩ | ⟨_, x', _, hsx', huv'⟩) | ⟨hT', _⟩
    · exact absurd (M.compIs_unique ht4 (by decide) hU.2.1 hF'.2) (by decide)
    · have ex : [x'] = [x] := M.repL_unique ((M.singSeq_iff w x').mp hsx') ((M.singSeq_iff w x).mp hsx)
      have ex' : x' = x := (List.cons.inj ex).1
      rw [ex'] at huv'
      rw [M.uval_agree ih huv huv']; exact ⟨q, hq, tw, hp, hp2⟩
    · exact absurd (M.compIs_unique ht4 (by decide) hU.2.1 hT'.2.1) (by decide)
  · exact absurd hT hnt

/-- 式の記号に Θ がなければ、式に現れる記号は Θ でない。 -/
theorem not_theta_tok {len : Nat} {S : Nat → Nat → Nat} (hθ : ∀ n, n < len → str S len n ≠ some (.fn 1 1))
    {t : α} {g : Nat → Nat} (hi : ∃ i, i < len ∧ g = S i) (ht : M.SeqRep t 4 g) : ¬ SymTheta M.mem t := by
  intro hst
  obtain ⟨i, hi, rfl⟩ := hi
  obtain ⟨e0, e1, e2, e3⟩ := hst
  rw [M.compIs_iff ht (by decide)] at e0 e1 e2 e3
  apply hθ i hi
  simp [str, hi, tok, decode, e0, e1, e2, e3]

theorem H_left {p a b : α} (hM : ∀ x y, M.mem x y → M.H x) (h : Pair M.mem p a b) : M.H a := by
  obtain ⟨s, _, ha, _⟩ := Tr.pair_dbl M.mem h
  exact hM a s ha

theorem cnOk_unique {Cn Cn' : α} (h : CnOk M.mem Cn) (h' : CnOk M.mem Cn') : Cn = Cn' := by
  have side : ∀ C C', CnOk M.mem C → CnOk M.mem C' → ∀ q, M.mem q C → M.mem q C' := by
    intro C C' hC hC' q hq
    obtain ⟨t, v, hp, ht4, hsc, hv⟩ := hC.1 q hq
    obtain ⟨q', hq', z, hz, hp'⟩ := hC'.2 t ⟨ht4, hsc⟩
    rw [M.empty_eq hz hv] at hp'
    rw [← M.pair_ext hp' hp]; exact hq'
  exact M.ext _ _ (fun q => ⟨side Cn Cn' h h' q, side Cn' Cn h' h q⟩)

theorem structParts_and {x : α} {P Q : α → α → α → α → α → Prop} (h : StructParts M.mem x P)
    (h' : StructParts M.mem x Q) : StructParts M.mem x (fun D E Cn Fn Rel => P D E Cn Fn Rel ∧ Q D E Cn Fn Rel) := by
  obtain ⟨de, rest, hp, D, E, hde, Cn, fr, hrest, Fn, Rel, hfr, hP⟩ := h
  obtain ⟨de', rest', hp', D', E', hde', Cn', fr', hrest', Fn', Rel', hfr', hQ⟩ := h'
  obtain ⟨e1, e2⟩ := M.pair_unique hp' hp
  subst e1; subst e2
  obtain ⟨e3, e4⟩ := M.pair_unique hde' hde
  subst e3; subst e4
  obtain ⟨e5, e6⟩ := M.pair_unique hrest' hrest
  subst e5; subst e6
  obtain ⟨e7, e8⟩ := M.pair_unique hfr' hfr
  subst e7; subst e8
  exact ⟨_, _, hp, _, _, hde, _, _, hrest, _, _, hfr, hP, hQ⟩

theorem structParts_eq (hM : ∀ x y, M.mem x y → M.H x) {x x' : α} {P P' : α → α → α → α → α → Prop}
    (h : StructParts M.mem x P) (h' : StructParts M.mem x' P')
    (hc : ∀ D E Cn Fn Rel D' E' Cn' Fn' Rel', M.H D → P D E Cn Fn Rel → P' D' E' Cn' Fn' Rel' →
      D = D' ∧ E = E' ∧ Cn = Cn' ∧ Fn = Fn' ∧ Rel = Rel') : x = x' := by
  obtain ⟨de, rest, hp, D, E, hde, Cn, fr, hrest, Fn, Rel, hfr, hP⟩ := h
  obtain ⟨de', rest', hp', D', E', hde', Cn', fr', hrest', Fn', Rel', hfr', hP'⟩ := h'
  obtain ⟨e1, e2, e3, e4, e5⟩ := hc _ _ _ _ _ _ _ _ _ _ (M.H_left hM hde) hP hP'
  subst e1; subst e2; subst e3; subst e4; subst e5
  have := M.pair_ext hfr hfr'; subst this
  have := M.pair_ext hrest hrest'; subst this
  have := M.pair_ext hde hde'; subst this
  exact M.pair_ext hp hp'

/-- 各段の閉包条件：D は 0 を含み、x ∈ D が順序数で x ∈ γ なら SU(x) ∈ D（紙の証明：階数の評価）。 -/
def SUClosed (SU : α) : Prop :=
  ∀ g x, M.Look SU g x → StructParts M.mem x (fun D _ _ _ _ =>
    M.mem (M.num 0) D ∧ ∀ y s, M.mem y D → OrdinalM M.mem y → M.mem y g → At M.mem SU y (fun s' => s' = s) → M.mem s D)

section Main
variable (Zx : M.Zax) (hM : ∀ x y, M.mem x y → M.H x)
include Zx hM

theorem theta_agree {D E Cn Rel g SU SU' Fn Fn' WL : α} (hdom : M.H D)
    (hE : ERestrict M.mem D E) (hCn : CnOk M.mem Cn) (hRel : Empty M.mem Rel)
    (hFn : FnOk M.mem Fn D g SU) (hFn' : FnOk M.mem Fn' D g SU') (hz : M.mem (M.num 0) D)
    (hU : ∀ x s, M.mem x D → OrdinalM M.mem x → M.mem x g → At M.mem SU x (fun s' => s' = s) → M.mem s D)
    (hU' : ∀ x s, M.mem x D → OrdinalM M.mem x → M.mem x g → At M.mem SU' x (fun s' => s' = s) → M.mem s D)
    (ih : ∀ x, M.mem x g → ∀ s s', M.Look SU x s → M.Look SU' x s' → s = s')
    (hwo : M.WO D WL) (hth : ThetaLM M.mem D E Cn Fn Rel WL) (hth' : ThetaLM M.mem D E Cn Fn' Rel WL)
    {m v v' : α} (hm : M.mem m D) (hv : ThetaValue M.mem Fn m v) (hv' : ThetaValue M.mem Fn' m v') : v = v' := by
  obtain ⟨v1, _, hv1, hc⟩ := hth m hm
  obtain ⟨v2, _, hv2, hc'⟩ := hth' m hm
  rw [M.thetaValue_unique hFn hv hv1, M.thetaValue_unique hFn' hv' hv2]
  rcases hc with ⟨s, hfm, hmc, hlg⟩ | ⟨hno, he⟩ <;> rcases hc' with ⟨s', hfm', hmc', hlg'⟩ | ⟨hno', he'⟩
  · obtain ⟨es, len, S, hs, _⟩ := M.metacode_unique hmc hmc'
    subst es
    obtain ⟨⟨φ, hw, ho, hl⟩, hθ⟩ := (M.formula_minus_iff hs).mp hfm
    have R := M.rep5_struct hM hE hCn hRel hFn hz hU
    have RT := Model.Rep5.toT M R S len
    have RT' : M.Rep5T D E Cn Fn' Rel (M.sModel D Fn ⟨M.num 0, hz⟩) S len :=
      ⟨R.domH, R.hE, fun t g k _ => R.hCn t g k,
       fun t g f a hi ht htok w ws hlen hws v => by
         have hnt := M.not_theta_tok hθ hi ht
         rw [← R.hFn t g f a ht htok w ws hlen hws v]
         exact ⟨M.fn_agree hFn' hFn (fun x hx s s' h1 h2 => (ih x hx s' s h2 h1).symm) hnt,
                M.fn_agree hFn hFn' ih hnt⟩,
       fun t w v h => M.fn_dom hFn' hz hU' h,
       fun t g r a _ => R.hRel t g r a⟩
    have hlg2 := (M.leastGood_iff RT Zx hdom hs φ hw ho hl v2 WL).mpr
      ((M.leastGood_iff RT' Zx hdom hs φ hw ho hl v2 WL).mp hlg')
    obtain ⟨v0, _, huniq, _⟩ := M.leastGood_exists_unique RT Zx hdom hs φ hw ho hl hwo ⟨M.num 0, hz⟩
    rw [huniq v1 hlg, huniq v2 hlg2]
  · exact absurd ⟨s, hfm, hmc⟩ hno'
  · exact absurd ⟨s', hfm', hmc'⟩ hno
  · exact M.empty_eq he he'

theorem fn_sub {D E Cn Rel g SU SU' Fn Fn' WL : α} (hdom : M.H D)
    (hE : ERestrict M.mem D E) (hCn : CnOk M.mem Cn) (hRel : Empty M.mem Rel)
    (hFn : FnOk M.mem Fn D g SU) (hFn' : FnOk M.mem Fn' D g SU') (hz : M.mem (M.num 0) D)
    (hU : ∀ x s, M.mem x D → OrdinalM M.mem x → M.mem x g → At M.mem SU x (fun s' => s' = s) → M.mem s D)
    (hU' : ∀ x s, M.mem x D → OrdinalM M.mem x → M.mem x g → At M.mem SU' x (fun s' => s' = s) → M.mem s D)
    (ih : ∀ x, M.mem x g → ∀ s s', M.Look SU x s → M.Look SU' x s' → s = s')
    (hwo : M.WO D WL) (hth : ThetaLM M.mem D E Cn Fn Rel WL) (hth' : ThetaLM M.mem D E Cn Fn' Rel WL) :
    ∀ q, M.mem q Fn → M.mem q Fn' := by
  intro q hq
  obtain ⟨tw, v, hp1, t, w, hp2, hent⟩ := hFn.1 q hq
  have hin : InTriple M.mem Fn t w v := ⟨q, hq, tw, hp1, hp2⟩
  by_cases hT : SymTheta M.mem t
  · obtain ⟨ht4, hcase⟩ := hent
    have hx : ∃ x, M.mem x D ∧ SingSeq M.mem w x := by
      rcases hcase with (⟨hF, _⟩ | ⟨hU0, _⟩) | ⟨_, x, hx, hsx, _⟩
      · exact absurd (M.compIs_unique ht4 (by decide) hF.2 hT.2.1) (by decide)
      · exact absurd (M.compIs_unique ht4 (by decide) hU0.2.1 hT.2.1) (by decide)
      · exact ⟨x, hx, hsx⟩
    obtain ⟨x, hx, hsx⟩ := hx
    have hval : ThetaValue M.mem Fn x v := ⟨q, hq, tw, v, hp1, rfl, t, w, hp2, hT, hsx⟩
    obtain ⟨v', _, hval', _⟩ := hth' x hx
    have e := M.theta_agree Zx hM hdom hE hCn hRel hFn hFn' hz hU hU' ih hwo hth hth' hx hval hval'
    rw [← e] at hval'
    obtain ⟨r, hr, tw', v2, hp1', e2, t', w', hp2', hT', hsx'⟩ := hval'
    rw [e2] at hp1'
    obtain ⟨g1, hg1⟩ := M.fn_tuple hFn' ⟨r, hr, tw', hp1', hp2'⟩
    have et : t' = t := M.theta_sym_eq ((M.tuple4_iff t').mpr ⟨g1, hg1⟩) ht4 hT' hT
    have ew : w' = w := M.repL_set_unique ((M.singSeq_iff w' x).mp hsx') ((M.singSeq_iff w x).mp hsx)
    rw [et, ew] at hp2'
    have etw := M.pair_ext hp2' hp2
    rw [etw] at hp1'
    rw [M.pair_ext hp1' hp1] at hr; exact hr
  · obtain ⟨r, hr, p, hpv, hp⟩ := M.fn_agree hFn hFn' ih hT hin
    rw [M.pair_ext hp hp2] at hpv
    rw [M.pair_ext hpv hp1] at hr; exact hr

theorem level_unique {g SU SU' D E Cn Fn Rel D' E' Cn' Fn' Rel' : α} (hdom : M.H D)
    (h : LevelM M.mem SU g D E Cn Fn Rel) (h' : LevelM M.mem SU' g D' E' Cn' Fn' Rel')
    (hz : M.mem (M.num 0) D)
    (hU : ∀ x s, M.mem x D → OrdinalM M.mem x → M.mem x g → At M.mem SU x (fun s' => s' = s) → M.mem s D)
    (hz' : M.mem (M.num 0) D')
    (hU' : ∀ x s, M.mem x D' → OrdinalM M.mem x → M.mem x g → At M.mem SU' x (fun s' => s' = s) → M.mem s D')
    (ih : ∀ x, M.mem x g → ∀ s s', M.Look SU x s → M.Look SU' x s' → s = s') :
    D = D' ∧ E = E' ∧ Cn = Cn' ∧ Fn = Fn' ∧ Rel = Rel' := by
  obtain ⟨lam, hlam, hV, hE, hCn, hRel, hFn, WL, hLO, hth⟩ := h
  obtain ⟨lam', hlam', hV', hE', hCn', hRel', hFn', WL', hLO', hth'⟩ := h'
  have e1 := M.lamOf_unique hlam hlam'; subst e1
  have e2 := M.vstage_unique hV hV'; subst e2
  have e3 := M.erestrict_unique hE hE'; subst e3
  have e4 := M.cnOk_unique hCn hCn'; subst e4
  have e5 := M.empty_eq hRel hRel'; subst e5
  obtain ⟨_, e7⟩ := M.lorder_unique hLO hLO'; subst e7
  have hwo := (M.lorder_wo Zx hM hLO).2
  refine ⟨rfl, rfl, rfl, M.ext _ _ (fun q => ⟨?_, ?_⟩), rfl⟩
  · exact M.fn_sub Zx hM hdom hE hCn hRel hFn hFn' hz hU hU' ih hwo hth hth' q
  · exact M.fn_sub Zx hM hdom hE hCn hRel hFn' hFn hz hU' hU
      (fun x hx s s' h1 h2 => (ih x hx s' s h2 h1).symm) hwo hth' hth q

/-- struct_rec を満たす二つの表は α で同じ値をとる。 -/
theorem structRec_unique {alpha SU SU' : α} (h : StructRec M.mem alpha SU) (h' : StructRec M.mem alpha SU')
    (hc : M.SUClosed SU) (hc' : M.SUClosed SU') :
    ∀ x x', M.Look SU alpha x → M.Look SU' alpha x' → x = x' := by
  obtain ⟨a1, hs1, hf, hall⟩ := h
  obtain ⟨a1', hs1', hf', hall'⟩ := h'
  have ea : a1' = a1 := M.ext _ _ (fun u => by rw [hs1 u, hs1' u])
  rw [ea] at hf' hall'
  have key : ∀ g, M.mem g a1 → ∀ x x', M.Look SU g x → M.Look SU' g x' → x = x' := by
    intro g
    induction g using M.wf.induction with
    | _ g ih =>
    intro hg x x' hl hl'
    have ih' : ∀ y, M.mem y g → ∀ s s', M.Look SU y s → M.Look SU' y s' → s = s' :=
      fun y hy s s' h1 h2 => ih y hy (M.look_dom hf h1) s s' h1 h2
    have hq := M.structParts_and (M.at_val hf (hall g hg) hl) (hc g x hl)
    have hq' := M.structParts_and (M.at_val hf' (hall' g hg) hl') (hc' g x' hl')
    exact M.structParts_eq hM hq hq' (fun D E Cn Fn Rel D' E' Cn' Fn' Rel' hD hP hP' =>
      M.level_unique Zx hM hD hP.1 hP'.1 hP.2.1 hP.2.2 hP'.2.1 hP'.2.2 ih')
  exact key alpha ((hs1 alpha).mpr (Or.inr rfl))

/-- struct_full を満たす (D, E, Cn, Fn, Rel) は高々一つ（閉包条件は紙の証明の補題）。 -/
theorem structFull_unique (hC : ∀ alpha SU, StructRec M.mem alpha SU → M.SUClosed SU)
    {i D E Cn Fn Rel D' E' Cn' Fn' Rel' : α}
    (h : StructFull M.mem i D E Cn Fn Rel) (h' : StructFull M.mem i D' E' Cn' Fn' Rel') :
    D = D' ∧ E = E' ∧ Cn = Cn' ∧ Fn = Fn' ∧ Rel = Rel' := by
  obtain ⟨alpha, ho, SU, hr, hat⟩ := h
  obtain ⟨alpha', ho', SU', hr', hat'⟩ := h'
  have ea := M.ordOf_unique ho' ho
  rw [ea] at hr' hat'
  obtain ⟨x, hl, hx⟩ := (M.at_look _ _ _).mp hat
  obtain ⟨x', hl', hx'⟩ := (M.at_look _ _ _).mp hat'
  have ex := M.structRec_unique Zx hM hr hr' (hC _ _ hr) (hC _ _ hr') x x' hl hl'
  rw [← ex] at hx'
  have hq := M.structParts_and hx hx'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ⟨e1, e2, e3, e4, e5⟩, ⟨f1, f2, f3, f4, f5⟩⟩ := hq
  rw [← e1, ← e2, ← e3, ← e4, ← e5, f1, f2, f3, f4, f5]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Main
end Model

#print axioms Model.fn_agree
#print axioms Model.theta_agree
#print axioms Model.structRec_unique
#print axioms Model.structFull_unique
end Tr
