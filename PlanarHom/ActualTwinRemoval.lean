import PlanarHom.ActualTwinReduction
import PlanarHom.ActualTwinRowFacts
import Mathlib.Algebra.Order.Field.Subfield

/-! Source Corollary 3.8: delete the zero actual-row class, sum positive
background weights, and apply the proved positive-weight-removal machine.
The fixed finite color numbering is semantic; graph inputs are ordinary raw
planar occurrence codes, with isolates and the empty graph included. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.ActualTwins
open Complexity Complexity.MixedCode
variable {C K : Type} [Fintype C] [Field K]

/-- Exactly the nonzero actual-row classes. Equality is numerical row equality,
not equality of supports. -/
abbrev reducedColors (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) :=
  Twins.nonzeroColor (Twins.quotientMatrix A hs)

def reducedCount (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) : ℕ :=
  Fintype.card (reducedColors A hs)

def reducedIndex (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) :
    Fin (reducedCount A hs) ≃ reducedColors A hs :=
  (Fintype.equivFin (reducedColors A hs)).symm

/-- A nonzero source has at least one retained actual-row class. -/
theorem reducedCount_pos (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) (hA : A ≠ 0) :
    0 < reducedCount A hs := by
  letI := Twins.deletedQuotient_nonempty_of_ne_zero A hs hA
  exact Fintype.card_pos

/-- For the zero source every actual-row class is deleted. -/
theorem reducedCount_eq_zero (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) (hA : A = 0) :
    reducedCount A hs = 0 := by
  have hR : Twins.quotientMatrix A hs = 0 := by
    funext x y
    induction x using Quotient.inductionOn with
    | h i =>
      induction y using Quotient.inductionOn with
      | h j => exact congrFun (congrFun hA i) j
  letI : IsEmpty (reducedColors A hs) := ⟨fun i => i.property (congrFun hR i.val)⟩
  exact Fintype.card_of_isEmpty

/-- One original microscopic color from each retained actual-row class. -/
def representative (A : Matrix C C K) (hs : ∀ i j,A i j=A j i)
    (i : Fin (reducedCount A hs)) : C := (reducedIndex A hs i).val.out

/-- Retain one actual row and column from each nonzero class. -/
def reducedMatrix (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) :
    Matrix (Fin (reducedCount A hs)) (Fin (reducedCount A hs)) K :=
  fun i j => Twins.nonzeroMatrix (Twins.quotientMatrix A hs)
    (reducedIndex A hs i) (reducedIndex A hs j)

/-- Positive microscopic weights are added within the whole actual class. -/
def reducedWeight (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) (w : C → K) :
    Fin (reducedCount A hs) → K :=
  fun i => Twins.quotientWeight A w (reducedIndex A hs i).val

/-- The computational reduced matrix literally retains the original entries
at one representative row and matching column per nonzero actual class. -/
theorem reducedMatrix_eq_representatives (A : Matrix C C K) (hs : ∀ i j,A i j=A j i)
    (i j : Fin (reducedCount A hs)) :
    reducedMatrix A hs i j = A (representative A hs i) (representative A hs j) := by
  have h := Twins.quotientMatrix_mk A hs
    (reducedIndex A hs i).val.out (reducedIndex A hs j).val.out
  simpa only [Quotient.out_eq] using h

/-- Different retained classes choose different original colors. -/
theorem representative_injective (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) :
    Function.Injective (representative A hs) := by
  intro i j h
  apply (reducedIndex A hs).injective
  apply Subtype.ext
  have he := congrArg (Quotient.mk (Twins.rowSetoid A)) h
  simpa only [representative,Quotient.out_eq] using he

/-- The retained weight is the sum over exactly the original colors with
the representative's numerical row. -/
theorem reducedWeight_eq_sum_rows (A : Matrix C C K) (hs : ∀ i j,A i j=A j i)
    (w : C → K) (i : Fin (reducedCount A hs)) :
    reducedWeight A hs w i =
      ∑ c : {c // A c = A (representative A hs i)},w c.val := by
  have hi : Quotient.mk (Twins.rowSetoid A) (representative A hs i) =
      (reducedIndex A hs i).val := Quotient.out_eq _
  have he : ∀ c, Quotient.mk (Twins.rowSetoid A) c = (reducedIndex A hs i).val ↔
      A c = A (representative A hs i) := by
    intro c
    constructor
    · intro h
      exact funext (Quotient.exact (h.trans hi.symm))
    · intro h
      exact (Quotient.sound (fun k => congrFun h k)).trans hi
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight he) _ _ (fun _ => rfl)

theorem reducedMatrix_symmetric (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) :
    ∀ i j,reducedMatrix A hs i j=reducedMatrix A hs j i :=
  fun i j => Twins.quotientMatrix_symmetric A hs
    (reducedIndex A hs i).val (reducedIndex A hs j).val

theorem reducedMatrix_rows_ne_zero (A : Matrix C C K) (hs : ∀ i j,A i j=A j i)
    (i : Fin (reducedCount A hs)) : reducedMatrix A hs i ≠ 0 := by
  intro h
  apply Twins.nonzeroMatrix_rows_ne_zero (Twins.quotientMatrix A hs)
    (Twins.quotientMatrix_symmetric A hs) (reducedIndex A hs i)
  funext j
  have he := congrFun h ((reducedIndex A hs).symm j)
  simpa only [reducedMatrix, Equiv.apply_symm_apply] using he

theorem representative_row_ne_zero (A : Matrix C C K) (hs : ∀ i j,A i j=A j i)
    (i : Fin (reducedCount A hs)) : A (representative A hs i) ≠ 0 := by
  intro h
  apply reducedMatrix_rows_ne_zero A hs i
  funext j
  rw [reducedMatrix_eq_representatives]
  exact congrFun h _

/-- Every original nonzero row occurs in exactly one retained actual class;
here the existence direction supplies its chosen representative. -/
theorem exists_representative_of_row_ne_zero (A : Matrix C C K)
    (hs : ∀ i j,A i j=A j i) (c : C) (hc : A c ≠ 0) :
    ∃ i : Fin (reducedCount A hs), A c = A (representative A hs i) := by
  have hclass : Twins.quotientMatrix A hs (Quotient.mk (Twins.rowSetoid A) c) ≠ 0 := by
    intro h
    apply hc
    funext j
    exact congrFun h (Quotient.mk (Twins.rowSetoid A) j)
  let x : reducedColors A hs := ⟨Quotient.mk (Twins.rowSetoid A) c,hclass⟩
  refine ⟨(reducedIndex A hs).symm x,?_⟩
  simp only [representative,Equiv.apply_symm_apply]
  exact (funext (Quotient.exact (Quotient.out_eq x.val))).symm

theorem reducedMatrix_rows_injective (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) :
    Function.Injective (reducedMatrix A hs) := by
  intro i j h
  apply (reducedIndex A hs).injective
  apply Twins.nonzeroMatrix_rows_injective (Twins.quotientMatrix A hs)
    (Twins.quotientMatrix_symmetric A hs) (Twins.quotientMatrix_rows_injective A hs)
  funext k
  have he := congrFun h ((reducedIndex A hs).symm k)
  simpa only [reducedMatrix, Equiv.apply_symm_apply] using he

variable [Algebra ℚ K] {dimension : ℕ}

/-- The weighted nonzero quotient reduces to the original weighted source.
Component extraction and rooted attachment machines deal with every isolate;
no connectedness or absence-of-zero-row assumption is added to the inputs. -/
def weightedReducedReduction [LinearOrder K] [IsStrictOrderedRing K]
    (basis : Module.Basis (Fin dimension) ℚ K)
    (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) (w : C → K) (hw : ∀ i,0<w i) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => reducedMatrix A hs)
        (fun u : Fin 0 => Fin.elim0 u) (reducedWeight A hs w))
      (evaluationProblem basis (fun _ : Fin 1 => A) (fun u : Fin 0 => Fin.elim0 u) w) := by
  let R := Twins.quotientMatrix A hs
  let v := Twins.quotientWeight A w
  have hR : ∀ i j,R i j=R j i := Twins.quotientMatrix_symmetric A hs
  have hv : ∀ i,0<v i := Twins.quotientWeight_pos A w hw
  let first := reindexReduction basis (Twins.nonzeroMatrix R)
    (fun i : Twins.nonzeroColor R => v i.val) (reducedIndex A hs)
  let second := RootedRestriction.submatrixReduction basis R hR v hv
    (Twins.nonzeroColor R) (Twins.nonzeroColor_colorClosed R hR)
  exact first.trans (second.trans (quotientReduction basis A hs w))

end PlanarHom.ActualTwins

namespace PlanarHom.ActualTwins
open Complexity Complexity.MixedCode SpectralFieldPresentation
variable {C : Type} [Fintype C]
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀] {dimension : ℕ}

omit [FiniteDimensional ℚ K₀] in
theorem reducedRealMatrix_rows_ne_zero (A : Matrix C C K₀)
    (hs : ∀ i j,A i j=A j i) (i : Fin (reducedCount A hs)) :
    realMatrix (reducedMatrix A hs) i ≠ 0 := by
  intro h
  apply reducedMatrix_rows_ne_zero A hs i
  funext j
  apply Subtype.ext
  exact congrFun h j

omit [FiniteDimensional ℚ K₀] in
theorem reducedRealMatrix_rows_injective (A : Matrix C C K₀)
    (hs : ∀ i j,A i j=A j i) :
    Function.Injective (realMatrix (reducedMatrix A hs)) := by
  intro i j h
  apply reducedMatrix_rows_injective A hs
  funext k
  apply Subtype.ext
  exact congrFun h k

/-- The full source3.8 oracle reduction. The only extra row hypothesis is the
paper's nonproportionality over all real scalars. The positive weight removal,
zero-row restriction and actual quotient reductions are actual TM2 programs.
The construction also works if the reduced color set is empty. -/
def removeWeightsReduction (basis : Module.Basis (Fin dimension) ℚ K₀)
    (A : Matrix C C K₀) (hs : ∀ i j,A i j=A j i) (w : C → K₀)
    (hw : ∀ i,0<(w i : ℝ))
    (hproj : ∀ i j,i≠j → ∀ t : ℝ,
      realMatrix (reducedMatrix A hs) i ≠ t • realMatrix (reducedMatrix A hs) j) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => reducedMatrix A hs)
        (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1))
      (evaluationProblem basis (fun _ : Fin 1 => A) (fun u : Fin 0 => Fin.elim0 u) w) := by
  letI : IsStrictOrderedRing K₀ := Subfield.toIsStrictOrderedRing K₀.toSubfield
  have hsymm : ∀ i j,realMatrix (reducedMatrix A hs) i j =
      realMatrix (reducedMatrix A hs) j i :=
    fun i j => congrArg K₀.val (reducedMatrix_symmetric A hs i j)
  have hweight : ∀ i : Fin (reducedCount A hs),
      0 < K₀.val (reducedWeight A hs w i) := by
    intro i
    change (0 : K₀) < Twins.quotientWeight A w (reducedIndex A hs i).val
    exact Twins.quotientWeight_pos A w hw _
  exact (PositiveWeightRemoval.removePositiveWeights basis
    (fun _ : Fin 1 => reducedMatrix A hs) (fun u : Fin 0 => Fin.elim0 u)
    (reducedWeight A hs w) 0 hsymm hweight
    (reducedRealMatrix_rows_ne_zero A hs) hproj).trans
      (weightedReducedReduction basis A hs w hw)

/-- The zero–one clause discharges, rather than assumes, all row hypotheses
needed to remove arbitrary fixed positive algebraic background weights. -/
def zeroOneReduction (basis : Module.Basis (Fin dimension) ℚ K₀)
    (A : Matrix C C K₀) (hs : ∀ i j,A i j=A j i) (w : C → K₀)
    (hw : ∀ i,0<(w i : ℝ)) (h01 : ∀ i j,A i j=0 ∨ A i j=1) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => reducedMatrix A hs)
        (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1))
      (evaluationProblem basis (fun _ : Fin 1 => A) (fun u : Fin 0 => Fin.elim0 u) w) := by
  apply removeWeightsReduction basis A hs w hw
  apply Twins.zeroOne_rows_nonproportional
  · intro i j
    have h := Twins.quotientMatrix_zeroOne A hs h01
      (reducedIndex A hs i).val (reducedIndex A hs j).val
    rcases h with h | h
    · exact Or.inl (congrArg K₀.val h)
    · exact Or.inr (congrArg K₀.val h)
  · exact reducedRealMatrix_rows_ne_zero A hs
  · exact reducedRealMatrix_rows_injective A hs

end PlanarHom.ActualTwins
