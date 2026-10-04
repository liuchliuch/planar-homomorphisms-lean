import PlanarHom.DenseTranscendenceEvaluation
import PlanarHom.FixedRealExtensionPresentation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Basis.Bilinear

/-! A fixed finite RF-basis presentation is finitely generated as a field over
Q. The explicit generators are the formal variables and the finite basis; no
finite-type-as-a-Q-algebra claim is made for a rational-function field. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealPresentationFiniteness
open DensePolynomial
variable {d e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction d) K] [Algebra ℚ K]

def polynomialMap (d:ℕ) (K:Type) [Field K] [Algebra (RationalFunction d) K] :
    MvPolynomial (Fin d) ℚ→+*K :=
  (algebraMap (RationalFunction d) K).comp
    ((algebraMap (Poly d) (RationalFunction d)).comp (mvEquiv d).toRingHom)

theorem polynomialMap_C (q:ℚ) : polynomialMap d K (MvPolynomial.C q)=algebraMap ℚ K q :=
  congrArg (fun f:ℚ→+*K=>f q) (RingHom.ext_rat ((polynomialMap d K).comp MvPolynomial.C) (algebraMap ℚ K))

def generators (basis:Module.Basis (Fin e) (RationalFunction d) K) : Fin d⊕Fin e→K :=
  Sum.elim (fun i=>polynomialMap d K (MvPolynomial.X i)) basis

theorem generated_top (basis:Module.Basis (Fin e) (RationalFunction d) K) :
    IntermediateField.adjoin ℚ (Set.range (generators basis))=⊤ := by
  let S:=IntermediateField.adjoin ℚ (Set.range (generators basis))
  have hb:∀i:Fin e,basis i∈S := fun i=>IntermediateField.subset_adjoin ℚ _ ⟨Sum.inr i,rfl⟩
  have hX:∀i:Fin d,polynomialMap d K (MvPolynomial.X i)∈S :=
    fun i=>IntermediateField.subset_adjoin ℚ _ ⟨Sum.inl i,rfl⟩
  have hp:∀p:MvPolynomial (Fin d) ℚ,polynomialMap d K p∈S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C q=>rw [polynomialMap_C]; exact S.algebraMap_mem q
    | add p q hp hq=>rw [map_add]; exact S.add_mem hp hq
    | mul_X p i hp=>rw [map_mul]; exact S.mul_mem hp (hX i)
  have hpoly:∀p:Poly d,algebraMap (RationalFunction d) K (algebraMap (Poly d) (RationalFunction d) p)∈S := by
    intro p
    have hh:=hp ((mvEquiv d).symm p)
    simpa only [polynomialMap,RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] using hh
  have hr:∀r:RationalFunction d,algebraMap (RationalFunction d) K r∈S := by
    intro r
    obtain ⟨p,q,hq,he⟩:=IsFractionRing.div_surjective (A:=Poly d) r
    rw [←he,map_div₀]
    exact S.div_mem (hpoly p) (hpoly q)
  apply top_unique
  intro x hx
  change x∈S
  rw [←basis.sum_equivFun x]
  apply S.sum_mem
  intro i hi
  rw [Algebra.smul_def]
  exact S.mul_mem (hr _) (hb i)

theorem top_fg (basis:Module.Basis (Fin e) (RationalFunction d) K) :
    (⊤:IntermediateField ℚ K).FG :=
  IntermediateField.fg_def.mpr ⟨Set.range (generators basis),Set.finite_range _,generated_top basis⟩

end PlanarHom.FixedRealPresentationFiniteness
