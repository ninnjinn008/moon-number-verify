/-
  一意性（改訂53、その 1）：ω、CNF の比較、O・ε0・L（到達不能基数の列）、V_λ。

  ・omega_iff：omega(w) なら w の元はちょうど自然数。
  ・cnfLt_lt：集合の言葉の cnf_lt(k, i) なら、G7 の意味で CNF(k) < CNF(i)（計算表の健全性 G7.cnf_cmp_correct による）。
  ・ordOf_unique・eps0_unique・lamOf_unique・vstage_unique：ord_of・eps0・lam_of・vstage を満たす値はただ一つ。
  （存在は集合論の側：紙の証明。）
-/
import TrU
namespace Tr

namespace Model
variable {α : Type} (M : Model α)

/-! ### 関数の値 -/

/-- (i, v) ∈ F。 -/
def Look (F i v : α) : Prop := ∃ q, M.mem q F ∧ Pair M.mem q i v

theorem at_look (F i : α) (P : α → Prop) : At M.mem F i P ↔ ∃ v, M.Look F i v ∧ P v :=
  ⟨fun ⟨q, hq, t, hp, ht⟩ => ⟨t, ⟨q, hq, hp⟩, ht⟩, fun ⟨t, ⟨q, hq, hp⟩, ht⟩ => ⟨q, hq, t, hp, ht⟩⟩

theorem look_func {F W i v v' : α} (hf : FuncDom M.mem F W) (h : M.Look F i v) (h' : M.Look F i v') : v = v' := by
  obtain ⟨q, hq, hp⟩ := h
  obtain ⟨q', hq', hp'⟩ := h'
  exact hf.2 q hq _ _ hp q' hq' _ _ hp' rfl

theorem look_dom {F W i v : α} (hf : FuncDom M.mem F W) (h : M.Look F i v) : M.mem i W := by
  obtain ⟨q, hq, hp⟩ := h
  obtain ⟨a, b, hp', ha⟩ := hf.1 q hq
  obtain ⟨rfl, rfl⟩ := M.pair_unique hp hp'
  exact ha

/-- At で述べた性質を、関数の値そのものに移す。 -/
theorem at_val {F W i v : α} {P : α → Prop} (hf : FuncDom M.mem F W) (ha : At M.mem F i P) (hl : M.Look F i v) : P v := by
  obtain ⟨v0, hl0, hp⟩ := (M.at_look F i P).mp ha
  rw [M.look_func hf hl0 hl] at hp; exact hp

theorem mem_irrefl (a : α) : ¬ M.mem a a := by
  induction a using M.wf.induction with
  | _ a ih => intro h; exact ih a h h

theorem mem_asymm {a b : α} (h : M.mem a b) : ¬ M.mem b a := by
  intro h'
  induction a using M.wf.induction generalizing b with
  | _ a ih => exact ih b h' h' h

/-! ### ω -/

theorem ordinal_num (n : Nat) : OrdinalM M.mem (M.num n) := by
  have h := M.natM_num n
  exact ⟨h.1, fun z hz u hu w hw => h.2.1 z hz u hu w hw⟩

theorem omega_iff {w : α} (hw : OmegaM M.mem w) (x : α) : M.mem x w ↔ ∃ n, x = M.num n := by
  obtain ⟨hord, hne, hns, hel⟩ := hw
  constructor
  · intro hx
    induction x using M.wf.induction with
    | _ x ih =>
    rcases hel x hx with he | ⟨y, hy, hs⟩
    · exact ⟨0, (M.empty_iff x).mp he⟩
    · obtain ⟨n, rfl⟩ := ih y hy (hord.1 x hx y hy)
      exact ⟨n + 1, (M.succ_num_iff n x).mp hs⟩
  · rintro ⟨n, rfl⟩
    induction n with
    | zero =>
      have hex : ∃ z, M.mem z w := Classical.byContradiction (fun h => hne (fun z hz => h ⟨z, hz⟩))
      obtain ⟨z, hz⟩ := hex
      obtain ⟨m, hm, hmin⟩ := G5.exists_min M.mem M.wf (fun z => M.mem z w) z hz
      have he : Empty M.mem m := fun b hb => hmin b hb (hord.1 m hm b hb)
      rw [(M.empty_iff m).mp he] at hm; exact hm
    | succ n ih =>
      rcases M.ord_trich (M.num (n + 1)) w (M.ordinal_num _) hord with h | h | h
      · exact h
      · exact absurd ⟨M.num n, by rw [← h]; exact M.num_lt (by omega), by rw [← h]; exact (M.succ_num_iff n _).mpr rfl⟩ hns
      · obtain ⟨j, hj, e⟩ := (M.num_mem _ w).mp h
        rw [e] at ih
        exact absurd (M.num_mem_iff.mp ih) (by omega)

/-! ### CNF の計算表 -/

theorem rowShape_iff (k0 : Nat) (r : α) : RowShape M.mem k0 r ↔ ∃ f, M.SeqRep r 4 f ∧ f 0 = k0 := by
  constructor
  · rintro ⟨⟨four, h4, hsw⟩, hc⟩
    rw [M.num_iff] at h4; subst h4
    obtain ⟨f, hf⟩ := M.seq_extract hsw
    rw [M.comp_iff hf (by decide), M.num_iff] at hc
    exact ⟨f, hf, M.num_inj hc⟩
  · rintro ⟨f, hf, h0⟩
    refine ⟨⟨M.num 4, (M.num_iff 4 _).mpr rfl, (M.seqWith_iff hf _).mpr rfl⟩, ?_⟩
    rw [M.comp_iff hf (by decide), M.num_iff, h0]

/-- 計算表 T の行 (0, i, h, r)。 -/
def HRn (T : α) (i h r : Nat) : Prop := ∃ q, M.mem q T ∧ ∃ f, M.SeqRep q 4 f ∧ f 0 = 0 ∧ f 1 = i ∧ f 2 = h ∧ f 3 = r
/-- 計算表 T の行 (1, i, k, c)。 -/
def CMn (T : α) (i k c : Nat) : Prop := ∃ q, M.mem q T ∧ ∃ f, M.SeqRep q 4 f ∧ f 0 = 1 ∧ f 1 = i ∧ f 2 = k ∧ f 3 = c

theorem rowGet0_num (T : α) (i : Nat) (body : α → α → Prop) :
    RowGet0 M.mem T (M.num i) body ↔ ∃ h r, M.HRn T i h r ∧ body (M.num h) (M.num r) := by
  constructor
  · rintro ⟨q, hq, hs, h1, h2⟩
    obtain ⟨f, hf, h0⟩ := (M.rowShape_iff 0 q).mp hs
    rw [M.comp_iff hf (by decide)] at h1 h2
    rw [M.comp_iff hf (by decide)] at h2
    exact ⟨f 2, f 3, ⟨q, hq, f, hf, h0, M.num_inj h1, rfl, rfl⟩, h2⟩
  · rintro ⟨h, r, ⟨q, hq, f, hf, h0, h1, h2, h3⟩, hb⟩
    refine ⟨q, hq, (M.rowShape_iff 0 q).mpr ⟨f, hf, h0⟩, ?_, ?_⟩
    · rw [M.comp_iff hf (by decide), h1]
    · rw [M.comp_iff hf (by decide), M.comp_iff hf (by decide), h2, h3]; exact hb

theorem rowGet1_num (T : α) (i k : Nat) (body : α → Prop) :
    RowGet1 M.mem T (M.num i) (M.num k) body ↔ ∃ c, M.CMn T i k c ∧ body (M.num c) := by
  constructor
  · rintro ⟨q, hq, hs, h1, h2, h3⟩
    obtain ⟨f, hf, h0⟩ := (M.rowShape_iff 1 q).mp hs
    rw [M.comp_iff hf (by decide)] at h1 h2 h3
    exact ⟨f 3, ⟨q, hq, f, hf, h0, M.num_inj h1, M.num_inj h2, rfl⟩, h3⟩
  · rintro ⟨c, ⟨q, hq, f, hf, h0, h1, h2, h3⟩, hb⟩
    refine ⟨q, hq, (M.rowShape_iff 1 q).mpr ⟨f, hf, h0⟩, ?_, ?_, ?_⟩
    · rw [M.comp_iff hf (by decide), h1]
    · rw [M.comp_iff hf (by decide), h2]
    · rw [M.comp_iff hf (by decide), h3]; exact hb

theorem empty_num (n : Nat) : Empty M.mem (M.num n) ↔ n = 0 := by
  rw [M.empty_iff]; exact ⟨M.num_inj, fun h => by rw [h]⟩

theorem num_k_iff (k n : Nat) : Num M.mem k (M.num n) ↔ n = k := by
  rw [M.num_iff]; exact ⟨M.num_inj, fun h => by rw [h]⟩

theorem decM_py {i : Nat} {a b : α} (h : DecM M.mem (M.num i) a b) (ha : M.mem a (M.num i)) (hb : M.mem b (M.num i)) :
    ∃ a' b', a = M.num a' ∧ b = M.num b' ∧ Dec.pyDec i a' b' := by
  obtain ⟨a', _, rfl⟩ := (M.num_mem i a).mp ha
  obtain ⟨b', _, rfl⟩ := (M.num_mem i b).mp hb
  refine ⟨a', b', rfl, rfl, ?_⟩
  obtain ⟨hne, i1, hi1, p, hp, hdv, hleast, v, hv, pv, hpv, j, hj, hbj, hndv⟩ := h
  rw [M.succ_num_iff] at hi1; subst hi1
  rw [M.succ_num_iff] at hv; subst hv
  rw [M.succ_num_iff] at hbj; subst hbj
  obtain ⟨p', rfl⟩ := M.prime_num hp
  rw [M.exp_iff] at hpv; subst hpv
  rw [M.mul_iff] at hj
  refine ⟨fun e => hne ((M.empty_num i).mpr e), p', (M.prime_iff p').mp hp, (M.divides_iff _ _).mp hdv,
    fun q hq ⟨hq1, hq2⟩ => hleast (M.num q) (M.num_lt hq) ⟨(M.prime_iff q).mpr hq1, (M.divides_iff _ _).mpr hq2⟩,
    b' + 1, M.num_inj hj, rfl, fun hd => hndv ((M.divides_iff _ _).mpr hd)⟩

/-- 集合の計算表は、G7 の表の条件を満たす。 -/
theorem tableOk_G7 {T : α} (hT : TableOk M.mem T) : G7.tableOk Dec.pyDecSpec (M.HRn T) (M.CMn T) := by
  have rowOk : ∀ q f, M.mem q T → M.SeqRep q 4 f →
      (M.num (f 0) = M.num 0 ∧ HrOk M.mem T (M.num (f 1)) (M.num (f 2)) (M.num (f 3))) ∨
      (M.num (f 0) = M.num 1 ∧ CmpOk M.mem T (M.num (f 1)) (M.num (f 2)) (M.num (f 3))) := by
    intro q f hq hf
    have := hT q hq
    rw [M.comp_iff hf (by decide), M.comp_iff hf (by decide), M.comp_iff hf (by decide),
      M.comp_iff hf (by decide), M.num_iff, M.num_iff] at this
    exact this
  refine ⟨fun i h r ⟨q, hq, f, hf, h0, h1, h2, h3⟩ => ?_, fun i k c ⟨q, hq, f, hf, h0, h1, h2, h3⟩ => ?_⟩
  · rcases rowOk q f hq hf with ⟨_, hok⟩ | ⟨e, _⟩
    · rw [h1, h2, h3] at hok
      obtain ⟨a, ha, b, hb, hd, hcase⟩ := hok
      obtain ⟨a', b', rfl, rfl, hpy⟩ := M.decM_py hd ha hb
      refine ⟨a', b', M.num_mem_iff.mp ha, M.num_mem_iff.mp hb, hpy, ?_⟩
      rcases hcase with ⟨he, eh, er⟩ | ⟨hne, hrow⟩
      · exact Or.inl ⟨(M.empty_num _).mp he, M.num_inj eh, (M.empty_num _).mp er⟩
      · right
        refine ⟨fun e => hne ((M.empty_num _).mpr e), ?_⟩
        obtain ⟨hb', rb', hhr, hrow1⟩ := (M.rowGet0_num T b' _).mp hrow
        obtain ⟨c', hcm, hc⟩ := (M.rowGet1_num T hb' a' _).mp hrow1
        refine ⟨hb', rb', hhr, c', hcm, ?_⟩
        rcases hc with ⟨hc2, eh, er⟩ | ⟨hc2, eh, er⟩
        · exact Or.inl ⟨(M.num_k_iff 2 c').mp hc2, M.num_inj eh, M.num_inj er⟩
        · exact Or.inr ⟨fun e => hc2 ((M.num_k_iff 2 c').mpr e), M.num_inj eh, M.num_inj er⟩
    · rw [h0] at e; exact absurd (M.num_inj e) (by decide)
  · rcases rowOk q f hq hf with ⟨e, _⟩ | ⟨_, hok⟩
    · rw [h0] at e; exact absurd (M.num_inj e) (by decide)
    · rw [h1, h2, h3] at hok
      simp only [CmpOk, M.empty_num, M.num_k_iff] at hok
      rcases hok with ((⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩) | ⟨e1, e2, e3⟩) | ⟨e1, e2, hrow⟩
      · exact Or.inl ⟨e1, e2, e3⟩
      · exact Or.inr (Or.inl ⟨e1, e2, e3⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨e1, e2, e3⟩))
      · right; right; right
        refine ⟨e1, e2, ?_⟩
        obtain ⟨hi, ri, hhi, hrow2⟩ := (M.rowGet0_num T i _).mp hrow
        obtain ⟨hk, rk, hhk, hrow3⟩ := (M.rowGet0_num T k _).mp hrow2
        obtain ⟨c1, hc1, hcase⟩ := (M.rowGet1_num T hi hk _).mp hrow3
        refine ⟨hi, ri, hhi, hk, rk, hhk, c1, hc1, ?_⟩
        rcases hcase with ⟨hn1, ec⟩ | ⟨h1', hrow4⟩
        · exact Or.inl ⟨fun e => hn1 ((M.num_k_iff 1 c1).mpr e), M.num_inj ec⟩
        · obtain ⟨c2, hc2, ec⟩ := (M.rowGet1_num T ri rk _).mp hrow4
          exact Or.inr ⟨(M.num_k_iff 1 c1).mp h1', c2, hc2, M.num_inj ec⟩

/-- cnf_lt(k, i) なら、CNF(k) < CNF(i)。 -/
theorem cnfLt_lt {k i : Nat} (h : CnfLt M.mem (M.num k) (M.num i)) :
    G7.ON.cmp (G7.norm Dec.pyDecSpec k) (G7.norm Dec.pyDecSpec i) = .lt := by
  obtain ⟨c, hc0, T, hT, hrow⟩ := h
  rw [M.num_iff] at hc0; subst hc0
  obtain ⟨c', hcm, ec⟩ := (M.rowGet1_num T k i _).mp hrow
  have e0 := M.num_inj ec
  subst e0
  have := (Dec.cnf_cmp_correct_py k i 0).mp ⟨_, _, M.tableOk_G7 hT, hcm⟩
  revert this
  cases G7.ON.cmp (G7.norm Dec.pyDecSpec k) (G7.norm Dec.pyDecSpec i) <;> simp [G7.code]

/-! ### O と ε0 -/

theorem oOk_unique {Of Of' W W' : α} (hO : OOk M.mem Of W) (hO' : OOk M.mem Of' W')
    (hW : ∀ x, M.mem x W ↔ ∃ n, x = M.num n) (hW' : ∀ x, M.mem x W' ↔ ∃ n, x = M.num n) :
    ∀ n x x', M.Look Of (M.num n) x → M.Look Of' (M.num n) x' → x = x' := by
  intro n
  induction n using Dec.name_lt_wf_py.induction with
  | _ n ih =>
  intro x x' hl hl'
  have hv := M.at_val hO.1 (hO.2 _ ((hW _).mpr ⟨n, rfl⟩)) hl
  have hv' := M.at_val hO'.1 (hO'.2 _ ((hW' _).mpr ⟨n, rfl⟩)) hl'
  have side : ∀ (F F' W W' x x' : α), OOk M.mem F W → OOk M.mem F' W' →
      (∀ x, M.mem x W ↔ ∃ n, x = M.num n) → (∀ x, M.mem x W' ↔ ∃ n, x = M.num n) →
      (∀ k, G7.ON.cmp (G7.norm Dec.pyDecSpec k) (G7.norm Dec.pyDecSpec n) = .lt →
        ∀ y y', M.Look F (M.num k) y → M.Look F' (M.num k) y' → y = y') →
      ((∀ y, M.mem y x → ∃ k, M.mem k W ∧ CnfLt M.mem k (M.num n) ∧ At M.mem F k (fun ok => ok = y)) ∧
        ∀ k, M.mem k W → CnfLt M.mem k (M.num n) → At M.mem F k (fun ok => M.mem ok x)) →
      ((∀ y, M.mem y x' → ∃ k, M.mem k W' ∧ CnfLt M.mem k (M.num n) ∧ At M.mem F' k (fun ok => ok = y)) ∧
        ∀ k, M.mem k W' → CnfLt M.mem k (M.num n) → At M.mem F' k (fun ok => M.mem ok x')) →
      ∀ y, M.mem y x → M.mem y x' := by
    intro F F' W W' x x' hF hF' hW hW' ih hv hv' y hy
    obtain ⟨k, hk, hlt, hat⟩ := hv.1 y hy
    obtain ⟨k', rfl⟩ := (hW k).mp hk
    obtain ⟨y0, hl0, rfl⟩ := (M.at_look _ _ _).mp hat
    have hk' : M.mem (M.num k') W' := (hW' _).mpr ⟨k', rfl⟩
    obtain ⟨y1, hl1, hy1⟩ := (M.at_look _ _ _).mp (hv'.2 _ hk' hlt)
    rw [ih k' (M.cnfLt_lt hlt) _ _ hl0 hl1]; exact hy1
  apply M.ext; intro y
  exact ⟨side Of Of' W W' x x' hO hO' hW hW' ih hv hv' y,
    side Of' Of W' W x' x hO' hO hW' hW (fun k hk y y' h h' => (ih k hk y' y h' h).symm) hv' hv y⟩

theorem ordOf_unique {i x x' : α} (h : OrdOf M.mem i x) (h' : OrdOf M.mem i x') : x = x' := by
  obtain ⟨w, hw, Of, hO, hat⟩ := h
  obtain ⟨w', hw', Of', hO', hat'⟩ := h'
  obtain ⟨v, hl, rfl⟩ := (M.at_look _ _ _).mp hat
  obtain ⟨v', hl', rfl⟩ := (M.at_look _ _ _).mp hat'
  obtain ⟨n, rfl⟩ := (M.omega_iff hw i).mp (M.look_dom hO.1 hl)
  exact M.oOk_unique hO hO' (M.omega_iff hw) (M.omega_iff hw') n _ _ hl hl'

theorem eps0_unique {E E' : α} (h : Eps0M M.mem E) (h' : Eps0M M.mem E') : E = E' := by
  have side : ∀ E E', Eps0M M.mem E → Eps0M M.mem E' → ∀ y, M.mem y E → M.mem y E' := by
    rintro E E' ⟨w, hw, Of, hO, hr1, _⟩ ⟨w', hw', Of', hO', _, hr2'⟩ y hy
    obtain ⟨i, hi, hat⟩ := hr1 y hy
    obtain ⟨v, hl, rfl⟩ := (M.at_look _ _ _).mp hat
    obtain ⟨n, rfl⟩ := (M.omega_iff hw i).mp hi
    obtain ⟨v', hl', hv'⟩ := (M.at_look _ _ _).mp (hr2' _ ((M.omega_iff hw' _).mpr ⟨n, rfl⟩))
    rw [M.oOk_unique hO hO' (M.omega_iff hw) (M.omega_iff hw') n _ _ hl hl']; exact hv'
  exact M.ext _ _ (fun y => ⟨side E E' h h' y, side E' E h' h y⟩)

theorem eps0_trans {E : α} (h : Eps0M M.mem E) : Trans M.mem E := by
  obtain ⟨w, hw, Of, hO, hr1, hr2⟩ := h
  intro y hy z hz
  obtain ⟨i, hi, hat⟩ := hr1 y hy
  obtain ⟨v, hl, rfl⟩ := (M.at_look _ _ _).mp hat
  obtain ⟨k, hk, _, hatk⟩ := (M.at_val hO.1 (hO.2 i hi) hl).1 z hz
  obtain ⟨vk, hlk, rfl⟩ := (M.at_look _ _ _).mp hatk
  exact M.at_val (P := fun v => M.mem v E) hO.1 (hr2 k hk) hlk

/-! ### 到達不能基数の列 L -/

theorem lamOk_unique {Lf Lf' E : α} (hL : LamOk M.mem Lf E) (hL' : LamOk M.mem Lf' E) (hEt : Trans M.mem E) :
    ∀ b, M.mem b E → ∀ l l', M.Look Lf b l → M.Look Lf' b l' → l = l' := by
  intro b
  induction b using M.wf.induction with
  | _ b ih =>
  intro hb l l' hl hl'
  obtain ⟨hi, hab, hle⟩ := M.at_val hL.1 (hL.2 b hb) hl
  obtain ⟨hi', hab', hle'⟩ := M.at_val hL'.1 (hL'.2 b hb) hl'
  -- l ∈ l' はありえない（対称）
  have no : ∀ (F F' : α) (l l' : α), LamOk M.mem F E → LamOk M.mem F' E →
      (∀ g, M.mem g b → ∀ v v', M.Look F g v → M.Look F' g v' → v = v') →
      InaccM M.mem l → (∀ g, M.mem g b → At M.mem F g (fun lg => M.mem lg l)) →
      (∀ mu, M.mem mu l' → InaccM M.mem mu → ∃ g, M.mem g b ∧ At M.mem F' g (fun lg => M.mem mu lg ∨ mu = lg)) →
      ¬ M.mem l l' := by
    intro F F' l l' hF hF' ihg hil habv hlev hll
    obtain ⟨g, hg, hat⟩ := hlev l hll hil
    obtain ⟨v', hlv', hv'⟩ := (M.at_look _ _ _).mp hat
    obtain ⟨v, hlv, hv⟩ := (M.at_look _ _ _).mp (habv g hg)
    rw [← ihg g hg v v' hlv hlv'] at hv'
    rcases hv' with h1 | rfl
    · exact M.mem_asymm h1 hv
    · exact M.mem_irrefl _ hv
  have ihg : ∀ g, M.mem g b → ∀ v v', M.Look Lf g v → M.Look Lf' g v' → v = v' :=
    fun g hg => ih g hg (hEt b hb g hg)
  rcases M.ord_trich l l' hi.1 hi'.1 with h | h | h
  · exact absurd h (no Lf Lf' l l' hL hL' ihg hi hab hle')
  · exact h
  · exact absurd h (no Lf' Lf l' l hL' hL (fun g hg v v' h1 h2 => (ihg g hg v' v h2 h1).symm) hi' hab' hle)

theorem lamOf_unique {b l l' : α} (h : LamOf M.mem b l) (h' : LamOf M.mem b l') : l = l' := by
  obtain ⟨E, hE, Lf, hL, hat⟩ := h
  obtain ⟨E', hE', Lf', hL', hat'⟩ := h'
  have e := M.eps0_unique hE hE'; subst e
  obtain ⟨v, hl, rfl⟩ := (M.at_look _ _ _).mp hat
  obtain ⟨v', hl', rfl⟩ := (M.at_look _ _ _).mp hat'
  exact M.lamOk_unique hL hL' (M.eps0_trans hE) b (M.look_dom hL.1 hl) _ _ hl hl'

/-! ### V_λ -/

theorem powerOf_unique {X X' Y : α} (h : PowerOf M.mem X Y) (h' : PowerOf M.mem X' Y) : X = X' :=
  M.ext _ _ (fun z => by rw [h.2 z, h'.2 z])

theorem vstage_unique {lam D D' : α} (h : VStage M.mem lam D) (h' : VStage M.mem lam D') : D = D' := by
  obtain ⟨⟨htr, _⟩, l1, hl1, R, hf, hall, hlam⟩ := h
  obtain ⟨_, l1', hl1', R', hf', hall', hlam'⟩ := h'
  have el : l1 = l1' := M.ext _ _ (fun u => by rw [hl1 u, hl1' u])
  subst el
  have l1tr : ∀ g, M.mem g l1 → ∀ w, M.mem w g → M.mem w l1 := by
    intro g hg w hw
    rcases (hl1 g).mp hg with hg | rfl
    · exact (hl1 w).mpr (Or.inl (htr g hg w hw))
    · exact (hl1 w).mpr (Or.inl hw)
  have key : ∀ g, M.mem g l1 → ∀ X X', M.Look R g X → M.Look R' g X' → X = X' := by
    intro g
    induction g using M.wf.induction with
    | _ g ih =>
    intro hg X X' hl hl'
    have hv := M.at_val hf (hall g hg) hl
    have hv' := M.at_val hf' (hall' g hg) hl'
    by_cases he : Empty M.mem g
    · exact M.empty_eq (hv.1 he) (hv'.1 he)
    by_cases hsu : IsSucc M.mem g
    · obtain ⟨w, hw, hsw⟩ := hsu
      obtain ⟨Y, hlY, hpY⟩ := (M.at_look _ _ _).mp (hv.2.1 w hw hsw)
      obtain ⟨Y', hlY', hpY'⟩ := (M.at_look _ _ _).mp (hv'.2.1 w hw hsw)
      have := ih w hw (l1tr g hg w hw) Y Y' hlY hlY'
      subst this
      exact M.powerOf_unique hpY hpY'
    · obtain ⟨u1, u2⟩ := hv.2.2 ⟨he, hsu⟩
      obtain ⟨u1', u2'⟩ := hv'.2.2 ⟨he, hsu⟩
      apply M.ext; intro y; constructor
      · intro hy
        obtain ⟨b, hb, hat⟩ := u1 y hy
        obtain ⟨Y, hlY, hyY⟩ := (M.at_look _ _ _).mp hat
        obtain ⟨Y', hlY', hsub⟩ := (M.at_look _ _ _).mp (u2' b hb)
        rw [ih b hb (l1tr g hg b hb) Y Y' hlY hlY'] at hyY
        exact hsub y hyY
      · intro hy
        obtain ⟨b, hb, hat⟩ := u1' y hy
        obtain ⟨Y', hlY', hyY⟩ := (M.at_look _ _ _).mp hat
        obtain ⟨Y, hlY, hsub⟩ := (M.at_look _ _ _).mp (u2 b hb)
        rw [← ih b hb (l1tr g hg b hb) Y Y' hlY hlY'] at hyY
        exact hsub y hyY
  obtain ⟨X, hl, rfl⟩ := (M.at_look _ _ _).mp hlam
  obtain ⟨X', hl', rfl⟩ := (M.at_look _ _ _).mp hlam'
  exact key lam ((hl1 lam).mpr (Or.inr rfl)) X X' hl hl'

end Model

#print axioms Model.omega_iff
#print axioms Model.cnfLt_lt
#print axioms Model.ordOf_unique
#print axioms Model.lamOf_unique
#print axioms Model.vstage_unique
end Tr
