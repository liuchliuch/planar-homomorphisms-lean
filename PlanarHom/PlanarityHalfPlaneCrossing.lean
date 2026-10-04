import PlanarHom.PlanarityContinuousAngleLift
import PlanarHom.PlanarEmbedding
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# NEW alternating-endpoint crossing in a closed half-plane

Two arbitrary continuous curves in a closed half-plane connecting four strictly
alternating boundary points must intersect. The proof uses the nonzero difference
map on a square and proves its boundary angle increments inconsistent. No simple
curve, Jordan separation, or embedding certificate is assumed.
-/
noncomputable section
open Set Topology unitInterval Complex
open scoped ComplexConjugate
namespace PlanarHom.PlanarityHalfPlaneCrossing
open PlanarityContinuousAngleLift

/-- Principal argument is continuous along every nonzero closed-upper-half-plane
path, including negative real boundary points. -/
def upperArg (f : C(I, ℂ)) (hup : ∀ t, 0 ≤ (f t).im) (hne : ∀ t, f t ≠ 0) : C(I, ℝ) where
  toFun t := Complex.arg (f t)
  continuous_toFun := by
    have h := Real.continuous_arccos.comp
      ((Complex.continuous_re.comp f.continuous).div f.continuous.norm
        (fun t => norm_ne_zero_iff.mpr (hne t)))
    exact h.congr (fun t => (Complex.arg_of_im_nonneg_of_ne_zero (hup t) (hne t)).symm)

/-- The continuous argument branch on the lower half-plane has value `-π`,
rather than `π`, on the negative real boundary. -/
def lowerArg (f : C(I, ℂ)) (hdown : ∀ t, (f t).im ≤ 0) (hne : ∀ t, f t ≠ 0) : C(I, ℝ) :=
  -(upperArg ⟨fun t => conj (f t), continuous_conj.comp f.continuous⟩
    (fun t => by simpa using neg_nonneg.mpr (hdown t))
    (fun t h => hne t (by simpa using congrArg conj h)))

@[simp] theorem coe_lowerArg (f : C(I, ℂ)) (hdown) (hne) (t : I) :
    (lowerArg f hdown hne t : Real.Angle) = Complex.arg (f t) := by
  change ((-Complex.arg (conj (f t)) : ℝ) : Real.Angle) = _
  rw [Real.Angle.coe_neg, Complex.arg_conj_coe_angle, neg_neg]

/-- The elementary half-plane crossing theorem for arbitrary continuous paths. -/
theorem alternating_paths_intersect (α β : C(I, ℂ)) {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : α 0 = a) (hc : α 1 = c) (hb : β 0 = b) (hd : β 1 = d)
    (hα : ∀ t, 0 ≤ (α t).im) (hβ : ∀ t, 0 ≤ (β t).im) :
    ∃ s t, α s = β t := by
  by_contra h
  have hne : ∀ s t, α s - β t ≠ 0 := by
    intro s t he
    exact h ⟨s,t,sub_eq_zero.mp he⟩
  let f : C(I × I, Real.Angle) :=
    ⟨fun st => Complex.arg (α st.1 - β st.2), by
      rw [continuous_iff_continuousAt]
      intro st
      have hdiff : ContinuousAt (fun st : I × I => α st.1 - β st.2) st :=
        ((α.continuous.comp continuous_fst).sub (β.continuous.comp continuous_snd)).continuousAt
      exact (Complex.continuousAt_arg_coe_angle (hne st.1 st.2)).comp (f := fun st : I × I => α st.1 - β st.2) hdiff⟩
  let bottomPath : C(I, ℂ) := ⟨fun s => α s - β 0, α.continuous.sub continuous_const⟩
  let topPath : C(I, ℂ) := ⟨fun s => α s - β 1, α.continuous.sub continuous_const⟩
  let leftPath : C(I, ℂ) := ⟨fun t => α 0 - β t, continuous_const.sub β.continuous⟩
  let rightPath : C(I, ℂ) := ⟨fun t => α 1 - β t, continuous_const.sub β.continuous⟩
  have hu0 : ∀ t, 0 ≤ (bottomPath t).im := by simpa [bottomPath,hb] using hα
  have hu1 : ∀ t, 0 ≤ (topPath t).im := by simpa [topPath,hd] using hα
  have hd0 : ∀ t, (leftPath t).im ≤ 0 := by simpa [leftPath,ha] using fun t => neg_nonpos.mpr (hβ t)
  have hd1 : ∀ t, (rightPath t).im ≤ 0 := by simpa [rightPath,hc] using fun t => neg_nonpos.mpr (hβ t)
  let bot := upperArg bottomPath hu0 (fun t => hne t 0)
  let top := upperArg topPath hu1 (fun t => hne t 1)
  let lft := lowerArg leftPath hd0 (fun t => hne 0 t)
  let rgt := lowerArg rightPath hd1 (fun t => hne 1 t)
  haveI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have he := square_boundary_increment (2*Real.pi) f bot top lft rgt
    (fun _ => rfl) (fun _ => rfl) (fun t => coe_lowerArg ..) (fun t => coe_lowerArg ..)
  have hbot0 : bot 0 = Real.pi := by
    change Complex.arg (α 0-β 0) = _
    rw [ha,hb,← Complex.ofReal_sub, Complex.arg_ofReal_of_neg (sub_neg.mpr hab)]
  have hbot1 : bot 1 = 0 := by
    change Complex.arg (α 1-β 0) = _
    rw [hc,hb,← Complex.ofReal_sub, Complex.arg_ofReal_of_nonneg (sub_nonneg.mpr hbc.le)]
  have htop0 : top 0 = Real.pi := by
    change Complex.arg (α 0-β 1) = _
    rw [ha,hd,← Complex.ofReal_sub, Complex.arg_ofReal_of_neg (sub_neg.mpr (hab.trans (hbc.trans hcd)))]
  have htop1 : top 1 = Real.pi := by
    change Complex.arg (α 1-β 1) = _
    rw [hc,hd,← Complex.ofReal_sub, Complex.arg_ofReal_of_neg (sub_neg.mpr hcd)]
  have hlft0 : lft 0 = -Real.pi := by
    change -Complex.arg (conj (α 0-β 0)) = _
    simp only [ha,hb,← Complex.ofReal_sub, Complex.conj_ofReal,
      Complex.arg_ofReal_of_neg (sub_neg.mpr hab)]
  have hlft1 : lft 1 = -Real.pi := by
    change -Complex.arg (conj (α 0-β 1)) = _
    simp only [ha,hd,← Complex.ofReal_sub, Complex.conj_ofReal,
      Complex.arg_ofReal_of_neg (sub_neg.mpr (hab.trans (hbc.trans hcd)))]
  have hrgt0 : rgt 0 = 0 := by
    change -Complex.arg (conj (α 1-β 0)) = _
    simp only [hc,hb,← Complex.ofReal_sub, Complex.conj_ofReal,
      Complex.arg_ofReal_of_nonneg (sub_nonneg.mpr hbc.le), neg_zero]
  have hrgt1 : rgt 1 = -Real.pi := by
    change -Complex.arg (conj (α 1-β 1)) = _
    simp only [hc,hd,← Complex.ofReal_sub, Complex.conj_ofReal,
      Complex.arg_ofReal_of_neg (sub_neg.mpr hcd)]
  rw [hbot0,hbot1,htop0,htop1,hlft0,hlft1,hrgt0,hrgt1] at he
  linarith [Real.pi_pos]

/-- Coordinate form directly usable for the project's actual plane curves. -/
theorem alternating_plane_paths_intersect (α β : C(I, MultiGraph.Plane)) {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : α 0 = (a,0)) (hc : α 1 = (c,0))
    (hb : β 0 = (b,0)) (hd : β 1 = (d,0))
    (hα : ∀ t, 0 ≤ (α t).2) (hβ : ∀ t, 0 ≤ (β t).2) :
    ∃ s t, α s = β t := by
  let A : C(I,ℂ) := ⟨fun t => Complex.equivRealProdCLM.symm (α t),
    Complex.equivRealProdCLM.symm.continuous.comp α.continuous⟩
  let B : C(I,ℂ) := ⟨fun t => Complex.equivRealProdCLM.symm (β t),
    Complex.equivRealProdCLM.symm.continuous.comp β.continuous⟩
  obtain ⟨s,t,h⟩ := alternating_paths_intersect A B hab hbc hcd
    (by change Complex.equivRealProdCLM.symm (α 0) = _; rw [ha]; rfl)
    (by change Complex.equivRealProdCLM.symm (α 1) = _; rw [hc]; rfl)
    (by change Complex.equivRealProdCLM.symm (β 0) = _; rw [hb]; rfl)
    (by change Complex.equivRealProdCLM.symm (β 1) = _; rw [hd]; rfl) hα hβ
  exact ⟨s,t,Complex.equivRealProdCLM.symm.injective h⟩

/-- Noninterleaving follows from actual disjoint continuous arcs, rather than an
input ordering certificate. Endpoints may touch, so interval inequalities are weak. -/
theorem noninterleaving_of_disjoint (α β : C(I, MultiGraph.Plane)) {a b c d : ℝ}
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (ha : α 0 = (a,0)) (hb : α 1 = (b,0))
    (hc : β 0 = (c,0)) (hd : β 1 = (d,0))
    (hα : ∀ t, 0 ≤ (α t).2) (hβ : ∀ t, 0 ≤ (β t).2)
    (hdis : Disjoint (Set.range α) (Set.range β)) :
    b ≤ c ∨ d ≤ a ∨ (a ≤ c ∧ d ≤ b) ∨ (c ≤ a ∧ b ≤ d) := by
  by_contra h
  push_neg at h
  have hcross (a b c d : ℝ) (α β : C(I,MultiGraph.Plane))
      (hab : a < b) (hbc : b < c) (hcd : c < d)
      (ha : α 0 = (a,0)) (hc : α 1 = (c,0))
      (hb : β 0 = (b,0)) (hd : β 1 = (d,0))
      (hα : ∀ t, 0 ≤ (α t).2) (hβ : ∀ t, 0 ≤ (β t).2)
      (hdis : Disjoint (Set.range α) (Set.range β)) : False := by
    obtain ⟨s,t,he⟩ := alternating_plane_paths_intersect α β hab hbc hcd ha hc hb hd hα hβ
    exact Set.disjoint_left.mp hdis ⟨s,rfl⟩ ⟨t,he.symm⟩
  by_cases hac : a ≤ c
  · have hbd : b < d := h.2.2.1 hac
    have hac' : a < c := by
      by_contra hn
      have hca : c ≤ a := le_of_not_gt hn
      have := h.2.2.2 hca
      linarith
    exact hcross a c b d α β hac' h.1 hbd ha hb hc hd hα hβ hdis
  · have hca : c < a := lt_of_not_ge hac
    have hdb : d < b := h.2.2.2 hca.le
    exact hcross c a d b β α hca h.2.1 hdb hc hd ha hb hβ hα hdis.symm

end PlanarHom.PlanarityHalfPlaneCrossing
