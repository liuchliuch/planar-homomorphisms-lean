import PlanarHom.BipartiteFullTwinFinite
import PlanarHom.FiniteFieldQuotientLanguage
import PlanarHom.RectangularWeightedNormNormalization

/-! Two exact consumer declaration/proof slices, with their required import and
namespace wrappers. This does not claim whole consumer-module compilation. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularSideMomentPresentation
open RectangularTwinQuotient RectangularWeightedNormNormalization
open RectangularSourceNormSimulation (block block_symm)
open BipartiteFullTwins FiniteFieldQuotientLanguage
variable {p s : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)]
variable {K₀ F : IntermediateField ℚ ℝ}

def sideEquiv (C : Matrix (Fin (p+s)) (Fin (p+s)) F)
    (N : Matrix (Fin p) (Fin s) ℝ) (hN : ∀ i j,0<N i j)
    (hc : ∀ i j,(C i j:ℝ)=block N i j) :
    Quotient (Twins.rowSetoid C) ≃ Rows N⊕Columns N :=
  (realQuotientEquiv C (block N) hc).trans (finSideEquiv N hN)

omit [Nonempty (Fin p)] [Nonempty (Fin s)] in
theorem matrix_sideEquiv (C : Matrix (Fin (p+s)) (Fin (p+s)) F)
    (hs : ∀ i j,C i j=C j i)
    (N : Matrix (Fin p) (Fin s) ℝ) (hN : ∀ i j,0<N i j)
    (hc : ∀ i j,(C i j:ℝ)=block N i j) (a b : Quotient (Twins.rowSetoid C)) :
    (Twins.quotientMatrix C hs a b:ℝ)=
      double (core N) (sideEquiv C N hN hc a) (sideEquiv C N hN hc b) := by
  rw [quotientMatrix_real C hs (block N) (block_symm N) hc]
  exact quotientMatrix_finSideEquiv N hN _ _

end PlanarHom.RectangularSideMomentPresentation

namespace PlanarHom.RectangularUnitCoreSource
open RectangularTwinQuotient BipartiteFullTwins
open RectangularSourceNormSimulation (block)
variable {X Y : Type} [Fintype X] [Fintype Y]
variable [Nonempty X] [Nonempty Y]

/-- Each side has its own fixed chart; no equality of side cardinalities is assumed. -/
def rowIndex (N : Matrix X Y ℝ) : Fin (Fintype.card (Rows N)) ≃ Rows N :=
  (Fintype.equivFin _).symm

def columnIndex (N : Matrix X Y ℝ) : Fin (Fintype.card (Columns N)) ≃ Columns N :=
  (Fintype.equivFin _).symm

def sideFinIndex (N : Matrix X Y ℝ) :
    Fin (Fintype.card (Rows N)+Fintype.card (Columns N)) ≃ Rows N⊕Columns N :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (rowIndex N) (columnIndex N))

def finCore (N : Matrix X Y ℝ) :
    Matrix (Fin (Fintype.card (Rows N))) (Fin (Fintype.card (Columns N))) ℝ :=
  fun i j=>core N (rowIndex N i) (columnIndex N j)

omit [Nonempty X] [Nonempty Y] in
theorem finCore_positive (N : Matrix X Y ℝ) (hN : ∀ x y,0<N x y) :
    ∀ i j,0<finCore N i j := fun i j=>core_positive N hN (rowIndex N i) (columnIndex N j)

omit [Nonempty X] [Nonempty Y] in
theorem finCore_block (N : Matrix X Y ℝ) (i j) :
    block (finCore N) i j=double (core N) (sideFinIndex N i) (sideFinIndex N j) := by
  refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;>
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
      simp [sideFinIndex,finCore,double]

end PlanarHom.RectangularUnitCoreSource
