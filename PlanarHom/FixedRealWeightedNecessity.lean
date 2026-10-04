import PlanarHom.FixedRealWeightedSupportAssembly
import PlanarHom.FixedRealRectangularWeightedNecessity

/-! NEW full A.12 necessity in the original prescribed field. The actual
numerical row quotient is formed first, retaining summed weights and its zero
class. Genuine support, positive and rectangular source proofs close every
component, including the empty-domain boundary. -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical
namespace PlanarHom.FixedRealWeightedNecessity
open DensePolynomial Complexity RepresentedBit Structures FixedRealActualTwins
variable {n e q : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]

 theorem positiveVertexWeightClass_of_not_hard (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin q) (Fin q) K) (hs : ∀ i j,M i j=M j i)
    (hnn : ∀ i j,0≤φ (M i j)) (w : Fin q → K) (hw : ∀ i,0<φ (w i))
    (hn : ¬SharpPHard (FixedRealComponents.problem basis (fun _ : Fin 1 => M)
      (fun l : Fin 0 => l.elim0) w)) :
    PositiveVertexWeightClass (fun i j => φ (M i j)) (fun i => φ (w i))
      (fun i j => congrArg φ (hs i j)) := by
  letI : Algebra K ℝ := φ.toAlgebra
  let Q := Twins.quotientMatrix M hs
  let v := Twins.quotientWeight M w
  let f : Fin (Fintype.card (Quotient (Twins.rowSetoid M))) ≃ Quotient (Twins.rowSetoid M) :=
    (Fintype.equivFin _).symm
  let A := fun i j => Q (f i) (f j)
  let u := fun i => v (f i)
  have hqs : ∀ i j,Q i j=Q j i := Twins.quotientMatrix_symmetric M hs
  have hqn : ∀ i j,0≤φ (Q i j) := by
    intro i j
    induction i using Quotient.inductionOn with
    | h i => induction j using Quotient.inductionOn with
      | h j => exact hnn i j
  have hqw : ∀ i,0<φ (v i) := quotientWeight_map_pos φ M w hw
  have hai : Function.Injective A := by
    intro i j hij
    apply f.injective
    apply Twins.quotientMatrix_rows_injective M hs
    funext k
    simpa only [A,f.apply_symm_apply] using congrFun hij (f.symm k)
  have red := (reindexReduction basis Q v f).trans (quotientReduction basis M hs w)
  have hA := FixedRealWeightedSupportAssembly.weightedClass_of_rectangular basis
    (fun V μ ν hp hi hμ hν hn => FixedRealRectangularWeightedNecessity.allowed_of_not_hard basis V μ ν hp hi hμ hν hn)
    A (fun i j => hqs _ _) (fun i j => hqn _ _) hai u (fun i => hqw _)
    (fun h => hn (h.trans red))
  let a := f.trans (rowEquiv φ M)
  have hm : (fun i j => φ (A i j)) =
      (fun i j => Twins.quotientMatrix (fun i j => φ (M i j)) (fun i j => congrArg φ (hs i j)) (a i) (a j)) := by
    funext i j
    exact quotientMatrix_map φ M hs (f i) (f j)
  have hv : (fun i => φ (u i)) =
      (fun i => Twins.quotientWeight (fun i j => φ (M i j)) (fun i => φ (w i)) (a i)) := by
    funext i
    exact quotientWeight_map φ M w (f i)
  change WeightedClass (fun i j => φ (A i j)) (fun i => φ (u i)) at hA
  rw [hm,hv] at hA
  exact WeightedClass.of_equiv a hA

end PlanarHom.FixedRealWeightedNecessity
