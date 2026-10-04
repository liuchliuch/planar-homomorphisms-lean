import PlanarHom.FixedRealLemmaA11Ordinary
import PlanarHom.FixedRealOrdinaryToPrescribed
import Mathlib.Algebra.Order.Ring.InjSurj

/-! Full A.11 including the prescribed-bipartition problem and the ordinary
symmetric double. Two independent side constants are retained at every endpoint.
The orientation conversions are actual represented oracle programs. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealLemmaA11
open DensePolynomial Complexity FixedRealExtension RepresentedBit Boolean
variable {n e d:ℕ} {F:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]

def side : Cube d⊕Cube d→Bool := Sum.elim (fun _=>false) (fun _=>true)
def prescribedProblem (basis:Module.Basis (Fin e) (RationalFunction n) F)
    (c:F) (ρ:Fin d→F) (μ ν:Cube d→F) : Problem :=
  FixedRealOrientation.problem basis (FixedRealBipartiteLeftHard.double (c • FixedRealTensorCoreEasy.tensor ρ))
    (Sum.elim μ ν) side

theorem double_crosses (c:F) (ρ:Fin d→F) :
    ∀i j,FixedRealBipartiteLeftHard.double (c • FixedRealTensorCoreEasy.tensor ρ) i j≠0→
      side i≠side j := by
  intro i j h
  cases i <;> cases j <;> simp_all [side,FixedRealBipartiteLeftHard.double]

def toPrescribed (basis:Module.Basis (Fin e) (RationalFunction n) F)
    (c:F) (ρ:Fin d→F) (μ ν:Cube d→F) :
    Reduction (problem basis c ρ μ ν) (prescribedProblem basis c ρ μ ν) :=
  FixedRealOrdinaryToPrescribed.forward basis _ _ side (double_crosses c ρ)

def fromPrescribed (basis:Module.Basis (Fin e) (RationalFunction n) F)
    (c:F) (ρ:Fin d→F) (μ ν:Cube d→F)
    (hμ:∀i,0<algebraMap F ℝ (μ i)) (hν:∀i,0<algebraMap F ℝ (ν i)) :
    Reduction (prescribedProblem basis c ρ μ ν) (problem basis c ρ μ ν) := by
  let φ:=algebraMap F ℝ
  letI : LinearOrder F:=LinearOrder.lift' φ φ.injective
  letI : IsStrictOrderedRing F:=Function.Injective.isStrictOrderedRing φ φ.map_zero φ.map_one
    φ.map_add φ.map_mul (fun {_ _}=>Iff.rfl) (fun {_ _}=>Iff.rfl)
  have hw:∀i:Cube d⊕Cube d,0<Sum.elim μ ν i := by
    intro i
    change φ 0<φ (Sum.elim μ ν i)
    rw [map_zero]
    cases i with | inl i=>exact hμ i | inr i=>exact hν i
  exact FixedRealOrientation.reduction basis _ _ hw side (double_crosses c ρ)

/-- Complete A.11: ordinary and prescribed inputs, two independent side
constants, and a real-field hard endpoint whenever either vector varies. -/
theorem lemmaA11 (basis:Module.Basis (Fin e) (RationalFunction n) F)
    (c:F) (hc:0<algebraMap F ℝ c) (ρ:Fin d→F)
    (hρ:∀j,0<algebraMap F ℝ (ρ j)) (hne:∀j,algebraMap F ℝ (ρ j)≠1)
    (μ ν:Cube d→F) (hμ:∀i,0<algebraMap F ℝ (μ i)) (hν:∀i,0<algebraMap F ℝ (ν i)) :
    (((∀i j,μ i=μ j) ∧ (∀i j,ν i=ν j))→
      (problem basis c ρ μ ν).InFP ∧ (prescribedProblem basis c ρ μ ν).InFP) ∧
    (((∃i j,μ i≠μ j) ∨ (∃i j,ν i≠ν j))→
      SharpPHard (problem basis c ρ μ ν) ∧ SharpPHard (prescribedProblem basis c ρ μ ν)) := by
  constructor
  · intro h
    have ho:=constant_inFP basis c ρ μ ν h.1 h.2
    exact ⟨ho,(fromPrescribed basis c ρ μ ν hμ hν).inFP ho⟩
  · intro h
    have ho:=nonconstant_hard basis c hc ρ hρ hne μ ν hμ hν h
    exact ⟨ho,ho.trans (toPrescribed basis c ρ μ ν)⟩

end PlanarHom.FixedRealLemmaA11
