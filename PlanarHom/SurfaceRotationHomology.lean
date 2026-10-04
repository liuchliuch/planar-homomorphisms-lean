import PlanarHom.RotationFaceCycleDuality
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.FieldTheory.Finiteness

/-! NEW finite surface-rotation foundation. The input is the actual supplied
cyclic row system and its component Euler defect. Homology is the literal
primal cycle space modulo the literal face-boundary space. This module proves
its dimension and cardinality; it does not assume or assert a Pfaffian sign law. -/
noncomputable section
open scoped BigOperators
open Matrix Module
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

/-- Exact finite validity condition for a connected nonempty supplied rotation
of orientable genus h. No geometric embedding or orientation sign certificate
is packaged into this predicate. -/
def HasGenus (h : ℕ) : Prop :=
  Fintype.card V+Fintype.card R.Face+2*h=Fintype.card E+2

def cycleSpace (_R : RotationRows G) : Submodule (ZMod 2) (E→ZMod 2) :=
  LinearMap.ker (G.coboundaryMatrix (ZMod 2)).transpose.mulVecLin

def faceBoundarySpace : Submodule (ZMod 2) (E→ZMod 2) :=
  LinearMap.range (R.dualGraph.coboundaryMatrix (ZMod 2)).mulVecLin

theorem faceBoundarySpace_le : R.faceBoundarySpace≤R.cycleSpace :=
  G.dual_range_le_primal_kernel R.dualGraph R.cycleDualCompatible

def faceBoundariesInCycles : Submodule (ZMod 2) R.cycleSpace :=
  LinearMap.range (Submodule.inclusion R.faceBoundarySpace_le)

abbrev Homology := R.cycleSpace ⧸ R.faceBoundariesInCycles

theorem faceBoundariesInCycles_finrank :
    finrank (ZMod 2) R.faceBoundariesInCycles=finrank (ZMod 2) R.faceBoundarySpace :=
  LinearMap.finrank_range_of_inj (Submodule.inclusion_injective R.faceBoundarySpace_le)

theorem homology_finrank_euler (root : Dart E)
    (hG : ∀u v,G.componentSetoid Finset.univ u v) :
    finrank (ZMod 2) R.Homology+Fintype.card V+Fintype.card R.Face=Fintype.card E+2 := by
  have hGdim:=G.coboundary_rank_add_one (K:=ZMod 2) (G.dartPair root).1 hG
  have hFdim:=R.dualGraph.coboundary_rank_add_one (K:=ZMod 2) (R.faceOf root) (R.dualGraph_connected hG)
  have hcycle:=(G.coboundaryMatrix (ZMod 2)).transpose.mulVecLin.finrank_range_add_finrank_ker
  change (G.coboundaryMatrix (ZMod 2)).transpose.rank+finrank (ZMod 2) R.cycleSpace=finrank (ZMod 2) (E→ZMod 2) at hcycle
  rw [Matrix.rank_transpose,Module.finrank_pi] at hcycle
  have hquot:=R.faceBoundariesInCycles.finrank_quotient_add_finrank
  rw [R.faceBoundariesInCycles_finrank] at hquot
  change finrank (ZMod 2) R.Homology+(R.dualGraph.coboundaryMatrix (ZMod 2)).rank=finrank (ZMod 2) R.cycleSpace at hquot
  omega

/-- The 2h obstruction is derived by rank-nullity, not assumed as a basis. -/
theorem homology_finrank_of_genus (root : Dart E)
    (hG : ∀u v,G.componentSetoid Finset.univ u v) {h : ℕ} (hh : R.HasGenus h) :
    finrank (ZMod 2) R.Homology=2*h := by
  have he:=R.homology_finrank_euler root hG
  unfold HasGenus at hh
  omega

instance homologyFinite : Finite R.Homology :=
  Finite.of_injective (Module.finBasis (ZMod 2) R.Homology).equivFun
    (Module.finBasis (ZMod 2) R.Homology).equivFun.injective

/-- There are exactly 4^h actual homology classes in the supplied rotation. -/
theorem homology_card_of_genus (root : Dart E)
    (hG : ∀u v,G.componentSetoid Finset.univ u v) {h : ℕ} (hh : R.HasGenus h) :
    Nat.card R.Homology=4^h := by
  letI : Fintype R.Homology:=Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=ZMod 2),ZMod.card,
    R.homology_finrank_of_genus root hG hh,pow_mul]
  norm_num

end PlanarHom.PlanarityLRRealization.RotationRows
