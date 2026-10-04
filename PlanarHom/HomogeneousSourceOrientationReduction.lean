import PlanarHom.HomogeneousSourceOrientationComponents
import PlanarHom.HomogeneousSourceOrientationCrossing
import PlanarHom.RootedRealAvailability

/-! Complete homogeneous typed-source orientation. A literal computed component
batch is reserialized into the exact intrinsic-domain format, then the genuine
connected root-attachment reduction calls the original homogeneous oracle.
The empty input has an empty query batch and returns the field unit. -/
noncomputable section
namespace PlanarHom.HomogeneousSourceOrientation
open Complexity Complexity.MixedCode PrescribedDomains GraphComponentCode
open FixedRealRootRestrictions PairProjectionMachines ArithmeticCircuitPrimitives
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K] {dimension : ℕ}

def prepareComponents (g : MixedCode) : Bits × List MixedCode :=
  ([], (components g).map canonicalDomains)

theorem fp_prepareComponents :
    FP MixedCode.encoding (BitEncoding.bits.prod MixedCode.encoding.list) prepareComponents :=
  (fp_const MixedCode.encoding BitEncoding.bits []).pair
    (GraphComponentMachines.fp_components.comp
      (ListMapMachines.fp_map MixedCode.encoding MixedCode.encoding canonicalDomains fp_canonicalDomains))

/-- The ordinary raw typed promise is exactly the decode-based graph promise
used by the charged pipeline compiler, with no canonical-word restriction. -/
theorem domainProblem_eq_restricted (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K) (side : C → Bool) :
    domainEvaluationProblem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w
      (Bipartite.domains side) sidePolicies emptyPolicies =
    restrictedEvaluationProblem basis (fun _ : Fin 1 => M)
      (extendedUnaries (fun l : Fin 0 => l.elim0) (Bipartite.domains side)) w
      (EncodedGraph sidePolicies emptyPolicies) := by
  have he : EncodedInput sidePolicies emptyPolicies =
      (fun raw => ∃ g, MixedCode.encoding.decode raw = some g ∧ EncodedGraph sidePolicies emptyPolicies g) :=
    funext (fun raw => propext (encodedInput_iff_graph sidePolicies emptyPolicies raw))
  unfold domainEvaluationProblem restrictedEvaluationProblem
  rw [he]

/-- Actual polynomial computed-component reduction, preserving the exact typed
metadata promise and handling disconnected, singleton, and empty inputs. -/
def componentReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K) (side : C → Bool) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w
        (Bipartite.domains side) sidePolicies emptyPolicies)
      (connectedTypedProblem basis M w side) := by
  rw [domainProblem_eq_restricted basis M w side]
  apply reductionOfPipeline basis BitEncoding.bits
    (fun _ : Fin 1 => M) (extendedUnaries (fun l : Fin 0 => l.elim0) (Bipartite.domains side)) w
    (fun _ : Fin 1 => M) (extendedUnaries (fun l : Fin 0 => l.elim0) (Bipartite.domains side)) w
    (EncodedGraph sidePolicies emptyPolicies) connectedTypedGraph
    (fun _ h => h.planarValid.1) (fun _ h => h.1.planarValid.1)
    prepareComponents (fun p : Bits × List K => p.2.prod) fp_prepareComponents
  · exact (fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
      (MaterializedFieldListMachines.fp_product basis)
  · intro g hg query hquery
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hquery
    exact canonical_components_promises g hg c hc
  · intro g hg
    simp only [prepareComponents, List.map_map, Function.comp_apply]
    exact canonical_components_evaluate g hg _ _ _

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Genuine homogeneous source-orientation reduction, with positive original
weights and the literal crossing property as the only numerical hypotheses. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K) (hw : ∀ i, 0 < w i)
    (side : C → Bool) (hcross : ∀ i j, M i j ≠ 0 → side i ≠ side j) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w
        (Bipartite.domains side) sidePolicies emptyPolicies)
      (evaluationProblem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w) :=
  (componentReduction basis M w side).trans (connectedReductionOfCrosses basis M w hw side hcross)

end PlanarHom.HomogeneousSourceOrientation

namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PrescribedDomains TypedBipartiteContext
open FixedRealRootRestrictions
variable {x y : ℕ}

/-- Exact original-field/source-oracle endpoint for the literal ambient X/Y
prescribed domains, including arbitrary valid raw encodings and all components. -/
def homogeneousSourceOrientation (L : RealLanguage (x+y) 1 0)
    (hw : ∀ i, 0 < L.weights i)
    (hcross : Bipartite.Crosses L.matrices (TypedSideSourceAccess.ambientSide x y)) :
    PromisePolyTimeTuringReduction
      (L.typedProblem (domains x y) (fun _ : Fin 1 => crossPolicy) (fun l : Fin 0 => l.elim0))
      L.problem := by
  letI : IsStrictOrderedRing L.field := Subfield.toIsStrictOrderedRing L.field.toSubfield
  have hwK : ∀ i, 0 < L.weightsK i := hw
  have hcrossK : ∀ i j, L.matricesK 0 i j ≠ 0 →
      TypedSideSourceAccess.ambientSide x y i ≠ TypedSideSourceAccess.ambientSide x y j := by
    intro i j hn
    apply hcross 0 i j
    intro hz
    apply hn
    exact Subtype.ext hz
  have h := HomogeneousSourceOrientation.reduction L.basis (L.matricesK 0) L.weightsK hwK
    (TypedSideSourceAccess.ambientSide x y) hcrossK
  have hM : (fun _ : Fin 1 => L.matricesK 0) = L.matricesK := by
    funext l
    congr 1
    exact (Fin.eq_zero l).symm
  have hU : (fun l : Fin 0 => Fin.elim0 l) = L.unariesK := by
    funext l
    exact l.elim0
  rw [hM,hU] at h
  simpa only [typedProblem, problem, TypedSideSourceAccess.domains_eq_bipartite,
    HomogeneousSourceOrientation.sidePolicies, HomogeneousSourceOrientation.emptyPolicies] using h

/-- Unit-background specialization used by the homogeneous source entrance. -/
def homogeneousUnitSourceOrientation (L : RealLanguage (x+y) 1 0)
    (hw : ∀ i, L.weights i = 1)
    (hcross : Bipartite.Crosses L.matrices (TypedSideSourceAccess.ambientSide x y)) :
    PromisePolyTimeTuringReduction
      (L.typedProblem (domains x y) (fun _ : Fin 1 => crossPolicy) (fun l : Fin 0 => l.elim0))
      L.problem :=
  L.homogeneousSourceOrientation (fun i => by rw [hw i]; exact zero_lt_one) hcross

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
