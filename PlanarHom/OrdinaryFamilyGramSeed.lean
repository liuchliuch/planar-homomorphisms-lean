import PlanarHom.OrdinaryClosedFamilySource
import PlanarHom.Normalization

/-! NEW positive-definite seed for an ordinary positive, nonproportional-row
source. The seed is its genuine planar two-edge Gram followed by a fixed
entrywise power. No nonsingularity of the original matrix is assumed. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity ClosedMatrixFamily TypedBipartiteContext TypedSideSourceAccess
variable {q : ℕ}

theorem signature_crossGramPath (M : Matrix (Fin q) (Fin q) ℝ) :
    TwoTerminal.signature crossGramPath M (fun _=>1) = M*M := by
  letI : DecidableEq (Fin 1) := Classical.decEq _
  ext i j
  unfold TwoTerminal.signature
  rw [Matrix.mul_apply]
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin q))
  intro η
  simp [TwoTerminal.assignmentWeight,TwoTerminal.edgeWeight,crossGramPath,
    TwoTerminal.reindexInternal,MultiGraph.reindex,TwoTerminal.twoEdgePath,
    TwoTerminal.extend,Fin.prod_univ_succ,Equiv.funUnique,Equiv.piUnique,finTwoEquiv,Equiv.ofUnique]

theorem ordinaryFamily_square (L : RealLanguage q 1 0)
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : M∈L.ordinaryFamily) : M*M∈L.ordinaryFamily := by
  have hs := L.ordinaryFamily_algebraic.symmetric M hM
  have hh : (M*M).IsHermitian := by
    rw [Matrix.IsHermitian,Matrix.conjTranspose_mul,hs.eq]
  have h := L.ordinaryFamily_gadgets.toPlanarGadgetClosed.signature_mem
    (Fin 1) (Fin 2) crossGramPath crossGramPath_planar M hM
    (by rw [signature_crossGramPath]; exact hh)
  simpa only [signature_crossGramPath] using h

theorem ordinaryFamily_positive_seed [Nonempty (Fin q)]
    (L : RealLanguage q 1 0) (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hpos : ∀ i j,0<L.matrices 0 i j)
    (hproj : ∀i j,i≠j→∀t:ℝ,L.matrices 0 i≠t • L.matrices 0 j) :
    Admissible L.ordinaryFamily (rowGramPower (L.matrices 0)) := by
  have hherm : (L.matrices 0).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hs j i
  have ht : (L.matrices 0).transpose=L.matrices 0 := by
    ext i j
    exact hs j i
  have hG := L.ordinaryFamily_square _ (L.ordinaryFamily_generator hherm)
  have hm : rowGramPower (L.matrices 0)∈L.ordinaryFamily := by
    unfold rowGramPower
    rw [ht]
    exact xFamily_entrywise_pow (y:=0) L.matrices (fun _=>sameX) _ hG _
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hpd := rowGramPower_posDef (L.matrices 0) hpos hproj
  have hpositive := rowGramPower_positive (L.matrices 0) hpos
  exact ⟨hm,fun i j=>(hpositive i j).le,hpd,
    support_connected_of_positive_entries _ hpd.1 hpositive⟩

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
