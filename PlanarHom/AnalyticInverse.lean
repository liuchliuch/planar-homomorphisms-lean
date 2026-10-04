import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Analytic inverses patched by injectivity

A locally invertible analytic map with global injectivity has a single analytic
inverse throughout its image. Domain and codomain may differ, as needed for the
matrix support space and its continuous dual in Lemma 4.5.
-/

open scoped Topology
open Filter
noncomputable section

namespace PlanarHom.AnalyticInverse

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The global choice inverse agrees locally with the analytic inverse supplied
by the inverse function theorem, because the original map is injective. -/
theorem analyticAt_invFun_of_equiv {f : E → F} (hinj : Function.Injective f)
    (x : E) (hf : AnalyticAt ℝ f x) (e : E ≃L[ℝ] F)
    (he : fderiv ℝ f x = (e : E →L[ℝ] F)) :
    AnalyticAt ℝ (Function.invFun f) (f x) := by
  have hd : HasStrictFDerivAt f (e : E →L[ℝ] F) x := by
    simpa only [he] using hf.hasStrictFDerivAt
  let g := hd.toOpenPartialHomeomorph f
  have hx : x ∈ g.source := hd.mem_toOpenPartialHomeomorph_source
  have hy : f x ∈ g.target := hd.image_mem_toOpenPartialHomeomorph_target
  have hg : AnalyticAt ℝ g.symm (f x) := by
    exact g.analyticAt_symm' hx hf he
  apply hg.congr
  filter_upwards [g.open_target.mem_nhds hy] with y hy'
  have hgy : f (g.symm y) = y := g.right_inv hy'
  calc
    g.symm y = Function.invFun f (f (g.symm y)) := (Function.leftInverse_invFun (f := f) hinj (g.symm y)).symm
    _ = Function.invFun f y := by rw [hgy]

/-- A bijective linear derivative gives the required continuous linear
equivalence in finite dimension. -/
theorem analyticAt_invFun {f : E → F} [FiniteDimensional ℝ E]
    (hinj : Function.Injective f) (x : E) (hf : AnalyticAt ℝ f x)
    (hderiv : Function.Bijective (fderiv ℝ f x)) :
    AnalyticAt ℝ (Function.invFun f) (f x) := by
  let e : E ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap hderiv).toContinuousLinearEquiv
  apply analyticAt_invFun_of_equiv hinj x hf e
  rfl

/-- Global injectivity patches all local analytic inverses on the image. -/
theorem analyticOnNhd_invFun [FiniteDimensional ℝ E] {f : E → F}
    (hinj : Function.Injective f) (hf : ∀ x, AnalyticAt ℝ f x)
    (hderiv : ∀ x, Function.Bijective (fderiv ℝ f x)) :
    AnalyticOnNhd ℝ (Function.invFun f) (Set.range f) := by
  rintro y ⟨x, rfl⟩
  exact analyticAt_invFun hinj x (hf x) (hderiv x)

/-- Applying the inverse along an analytic curve in the range preserves
analyticity; this is the continuation-curve interface. -/
theorem analyticAt_invFun_comp [FiniteDimensional ℝ E] {f : E → F}
    (hinj : Function.Injective f) (hf : ∀ x, AnalyticAt ℝ f x)
    (hderiv : ∀ x, Function.Bijective (fderiv ℝ f x))
    {a : ℝ → F} {t : ℝ} (ha : AnalyticAt ℝ a t) (hmem : a t ∈ Set.range f) :
    AnalyticAt ℝ (fun s => Function.invFun f (a s)) t :=
  (analyticOnNhd_invFun hinj hf hderiv _ hmem).comp ha

end PlanarHom.AnalyticInverse
