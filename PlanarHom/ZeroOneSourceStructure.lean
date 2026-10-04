import PlanarHom.ZeroOneGramMatching
import PlanarHom.ZeroOneReducedMatchingLift
import PlanarHom.ZeroOneDifunctionalComponents
import PlanarHom.ActualTwinRealAvailability

/-! NEW complete internal Section 7 necessity argument. The ordinary weighted
source is reduced to its actual nonzero row quotient by the real Corollary 3.8
program. Source Gram blocks, integer tensor obstruction and exact row lifting
then construct every original basic zero-one component. Only the independently
identified all-size positive-Potts hardness foundation remains explicit. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode ActualTwins RootedRestriction
open ZeroOneBasicStructure ZeroOneGramBlockClassification ZeroOneGramMatching
variable {q : ℕ}

theorem zeroOne_basic_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hw : ∀i,0<L.weights i) (h01 : ∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1)
    (hnot : ¬PromisedSharpPHard L.problem) :
    ∀c : (colorSupport (L.matrices 0) hs).ConnectedComponent,
      BasicZeroOneComponent (fun i j : c.supp=>L.matrices 0 i.val j.val) := by
  let A := L.matricesK 0
  let hsK := L.actualTwin_symmetryK hs
  let R := unitLanguage (fun _ : Fin 1=>L.actualTwinMatrix hs)
    (fun _ i j=>(IsAlgebraic.of_finite ℚ (L.actualTwinMatrixK hs i j)).algHom L.field.val)
  have hRunit : ∀i,R.weights i=1 := fun _=>rfl
  have hRhs : ∀i j,R.matrices 0 i j=R.matrices 0 j i :=
    fun i j=>congrArg L.field.val (reducedMatrix_symmetric A hsK i j)
  have hR01 : ∀i j,R.matrices 0 i j=0 ∨ R.matrices 0 i j=1 := by
    intro i j
    change L.actualTwinMatrix hs i j=0 ∨ L.actualTwinMatrix hs i j=1
    rw [L.actualTwinMatrix_eq_representatives hs]
    exact h01 _ _
  have hRnz : ∀i,R.matrices 0 i≠0 := reducedRealMatrix_rows_ne_zero A hsK
  have hRinj : Function.Injective (R.matrices 0) := reducedRealMatrix_rows_injective A hsK
  have first := R.presentationDescentReduction L.field L.basis
    (fun _ : Fin 1=>L.actualTwinMatrixK hs) (fun u : Fin 0=>u.elim0) (fun _=>1)
    (fun _ _ _=>rfl) (fun u=>u.elim0) (fun _=>rfl)
  have red : PromisePolyTimeTuringReduction R.problem L.problem :=
    first.trans (L.corollary38_zeroOne hs hw h01)
  have hnR : ¬PromisedSharpPHard R.problem := fun hh=>hnot (hh.trans red)
  have hb := source_blocks hPotts R hRunit hRhs hR01 hRnz hRinj hnR
  have hm : ∀i j k,R.matrices 0 i j≠0 → R.matrices 0 i k≠0 → j=k :=
    neighbors_unique (R.matrices 0) hRhs hR01 hb
  have hmK : ∀i j k,reducedMatrix A hsK i j≠0 → reducedMatrix A hsK i k≠0 → j=k := by
    intro i j k hij hik
    exact hm i j k (fun hz=>hij (Subtype.ext hz)) (fun hz=>hik (Subtype.ext hz))
  have hrows : ∀i j k,L.matrices 0 i j≠0 → L.matrices 0 i k≠0 →
      L.matrices 0 j=L.matrices 0 k := by
    intro i j k hij hik
    have h := rows_of_reduced_matching A hsK hmK i j k
      (fun hz=>hij (congrArg L.field.val hz)) (fun hz=>hik (congrArg L.field.val hz))
    funext v
    exact congrArg L.field.val (congrFun h v)
  exact ZeroOneDifunctionalComponents.component_basic (L.matrices 0) hs h01 hrows

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
