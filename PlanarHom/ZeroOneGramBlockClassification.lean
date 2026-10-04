import PlanarHom.PositiveDefiniteSupportBlocks
import PlanarHom.StrictTensorSupportBlocks
import PlanarHom.ZeroOneGramSourceAvailability
import PlanarHom.PositiveWeightRemovalReduction
import PlanarHom.ActualTwinRowFacts

/-! NEW source-facing §7 Gram block classification. Distinct nonzero zero-one
rows give the genuine PD tensor Gram. Each support block is obtained by actual
source restriction, then its positive entrywise root is taken only numerically. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.ZeroOneGramBlockClassification
open Complexity RootedRestriction StrictTensorSupportBlocks
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
variable {q : ℕ}

theorem square_symmetric (A : Matrix (Fin q) (Fin q) ℝ) (hs : ∀i j,A i j=A j i) :
    ∀i j,(A*A) i j=(A*A) j i := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [hs i k,hs k j]
  ring

theorem square_nonnegative (A : Matrix (Fin q) (Fin q) ℝ) (hnn : ∀i j,0≤A i j) :
    ∀i j,0≤(A*A) i j := by
  intro i j
  change 0≤∑k:Fin q,A i k*A k j
  exact Finset.sum_nonneg (fun k _=>mul_nonneg (hnn i k) (hnn k j))

theorem source_blocks (hPotts : PositivePottsFoundation) (L : RealLanguage q 1 0)
    (hunit : ∀i,L.weights i=1) (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (h01 : ∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1)
    (hnz : ∀i,L.matrices 0 i≠0) (hinj : Function.Injective (L.matrices 0))
    (hnot : ¬PromisedSharpPHard L.problem) :
    Blocks (colorSupport (L.matrices 0*L.matrices 0) (square_symmetric _ hs))
      (L.matrices 0*L.matrices 0) := by
  let A := L.matrices 0
  let p := max 1 (q-1)
  have hp : p≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  let Q := L.gramLanguage p
  have hwEq : L.weights=(fun _=>1) := funext hunit
  have hmat : Q.matrices 0=fun i j=>(A*A) i j^p := by
    ext i j
    simp [Q,gramLanguage,gramMatrix,unitLanguage,A,PositiveWeightRemoval.gramCoreField,hwEq,Matrix.diagonal_one]
  have hproj := Twins.zeroOne_rows_nonproportional A h01 hnz hinj
  have hpd : (Q.matrices 0).PosDef := by
    rw [hmat]
    have h := PositiveWeightRemoval.gramCore_posDef A hs (fun _=>1) (fun _=>zero_lt_one) hnz hproj
    change Matrix.PosDef (fun (i j : Fin q)=>(A * Matrix.diagonal (fun (_ : Fin q)=> (1:ℝ)) * A) i j ^ max 1 (q-1)) at h
    simpa only [Matrix.diagonal_one,Matrix.mul_one,p] using h
  have hnnA : ∀i j,0≤A i j := by
    intro i j
    change 0≤L.matrices 0 i j
    rcases h01 i j with h|h <;> rw [h] <;> norm_num
  have hnnSq := square_nonnegative A hnnA
  have hnnQ : ∀i j,0≤Q.matrices 0 i j := by
    intro i j
    rw [hmat]
    exact pow_nonneg (hnnSq i j) _
  have hsQ : ∀i j,Q.matrices 0 i j=Q.matrices 0 j i := by
    intro i j
    simpa only [star_trivial] using hpd.1.apply j i
  have red := L.gramSourceReduction hunit p
  have hnQ : ¬PromisedSharpPHard Q.problem := fun hh=>hnot (hh.trans red)
  have hblocks : Blocks (colorSupport (Q.matrices 0) hsQ) (Q.matrices 0) := by
    intro c
    exact Q.positiveDefinite_support_block_tensor hPotts (fun _=>rfl) hsQ hpd hnnQ hnQ c
  have hgraph : colorSupport (Q.matrices 0) hsQ = colorSupport (A*A) (square_symmetric A hs) := by
    ext i j
    change (i≠j ∧ Q.matrices 0 i j≠0) ↔ (i≠j ∧ (A*A) i j≠0)
    rw [show Q.matrices 0 i j=(A*A) i j^p from congrFun (congrFun hmat i) j]
    constructor
    · rintro ⟨hij,hn⟩
      refine ⟨hij,?_⟩
      intro hz
      exact hn (by rw [hz,zero_pow hp])
    · rintro ⟨hij,hn⟩
      exact ⟨hij,pow_ne_zero _ hn⟩
  rw [hgraph,hmat] at hblocks
  exact hblocks.root hnnSq hp

end PlanarHom.ZeroOneGramBlockClassification
