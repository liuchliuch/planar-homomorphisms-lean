import PlanarHom.DependentFieldEqualityMachines
import PlanarHom.FixedFieldEncodingTransport
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! A uniform rational Gram/Cramer retraction, derived from the supplied field-inclusion machine. -/
noncomputable section
namespace PlanarHom.DependentFieldOutputDescent
open Complexity Matrix RationalCircuits
open scoped BigOperators
variable {L X : Type} [Field L] [Algebra ℚ L]
variable {sourceDimension : ℕ} (sourceBasis : Module.Basis (Fin sourceDimension) ℚ L)
variable (ex : BitEncoding X) (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
variable (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
variable (inclusion : ∀ x, L →+* K x) (c : ℕ)

/-- Fixed-width zero padding of the literal variable-length rational coordinate list. -/
def paddedCoordinates (x : X) (a : K x) : Fin c → ℚ :=
  fun i => (List.ofFn ((basis x).equivFun a)).getD i.val 0

def inclusionMatrix (x : X) : Matrix (Fin c) (Fin sourceDimension) ℚ :=
  fun i j => paddedCoordinates K dimension basis c x (inclusion x (sourceBasis j)) i

def gram (x : X) : Matrix (Fin sourceDimension) (Fin sourceDimension) ℚ :=
  (inclusionMatrix sourceBasis K dimension basis inclusion c x)ᵀ *
    inclusionMatrix sourceBasis K dimension basis inclusion c x

def coordinates (s : Σ x, K x) : Fin sourceDimension → ℚ :=
  fun j => cramer (gram sourceBasis K dimension basis inclusion c s.1)
    ((inclusionMatrix sourceBasis K dimension basis inclusion c s.1)ᵀ *ᵥ
      paddedCoordinates K dimension basis c s.1 s.2) j /
        (gram sourceBasis K dimension basis inclusion c s.1).det

/-- Total rational-linear descent. Its intended correctness is on the inclusion image. -/
def descend (s : Σ x, K x) : L :=
  sourceBasis.equivFun.symm (coordinates sourceBasis K dimension basis inclusion c s)

@[simp] theorem padded_zero (x : X) : paddedCoordinates K dimension basis c x 0 = 0 := by
  funext i
  by_cases hi : i.val < dimension x
  · simp [paddedCoordinates, List.getD_eq_getElem, hi]
  · simp [paddedCoordinates, List.getD_eq_default, hi]

theorem padded_injective (hc : ∀ x, dimension x ≤ c) (x : X) :
    Function.Injective (paddedCoordinates K dimension basis c x) := by
  intro a b h
  apply (basis x).equivFun.injective
  funext i
  have hi : i.val < c := i.isLt.trans_le (hc x)
  have hh := congrFun h ⟨i.val,hi⟩
  simpa [paddedCoordinates] using hh

theorem inclusionMatrix_mulVec (x : X) (a : L) :
    inclusionMatrix sourceBasis K dimension basis inclusion c x *ᵥ sourceBasis.equivFun a =
      paddedCoordinates K dimension basis c x (inclusion x a) := by
  funext i
  by_cases hi : i.val < dimension x
  · have he := FixedFieldEncodingTransport.coordinate_linearMap sourceBasis (basis x)
      (inclusion x).toRatAlgHom.toLinearMap a ⟨i.val,hi⟩
    simpa [inclusionMatrix, paddedCoordinates, Matrix.mulVec, dotProduct, hi] using he.symm
  · simp [inclusionMatrix, paddedCoordinates, Matrix.mulVec, dotProduct, List.getD_eq_default, hi]

theorem inclusionMatrix_kernel (hc : ∀ x, dimension x ≤ c) (x : X) (v : Fin sourceDimension → ℚ)
    (hv : inclusionMatrix sourceBasis K dimension basis inclusion c x *ᵥ v = 0) : v = 0 := by
  let a := sourceBasis.equivFun.symm v
  have h : paddedCoordinates K dimension basis c x (inclusion x a) =
      paddedCoordinates K dimension basis c x 0 := by
    rw [padded_zero, ← inclusionMatrix_mulVec sourceBasis K dimension basis inclusion c x a]
    simpa only [a, LinearEquiv.apply_symm_apply] using hv
  have ha : a = 0 := (inclusion x).injective (by
    simpa using padded_injective K dimension basis c hc x h)
  have hh := congrArg sourceBasis.equivFun ha
  simpa only [a, LinearEquiv.apply_symm_apply, map_zero] using hh

theorem gram_det_ne_zero (hc : ∀ x, dimension x ≤ c) (x : X) :
    (gram sourceBasis K dimension basis inclusion c x).det ≠ 0 := by
  intro hd
  obtain ⟨v,hv,hg⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hk : v ∈ LinearMap.ker (gram sourceBasis K dimension basis inclusion c x).mulVecLin := hg
  rw [gram, Matrix.ker_mulVecLin_transpose_mul_self] at hk
  exact hv (inclusionMatrix_kernel sourceBasis K dimension basis inclusion c hc x v hk)

/-- The rectangular inclusion matrix has full column rank, so its rational Gram
matrix recovers every original source coordinate exactly. -/
theorem descend_inclusion (hc : ∀ x, dimension x ≤ c) (x : X) (a : L) :
    descend sourceBasis K dimension basis inclusion c ⟨x,inclusion x a⟩ = a := by
  apply sourceBasis.equivFun.injective
  rw [descend, LinearEquiv.apply_symm_apply]
  funext j
  have hr : (inclusionMatrix sourceBasis K dimension basis inclusion c x)ᵀ *ᵥ
      paddedCoordinates K dimension basis c x (inclusion x a) =
      gram sourceBasis K dimension basis inclusion c x *ᵥ sourceBasis.equivFun a := by
    rw [← inclusionMatrix_mulVec sourceBasis K dimension basis inclusion c x a, Matrix.mulVec_mulVec]
    rfl
  have hd := gram_det_ne_zero sourceBasis K dimension basis inclusion c hc x
  dsimp only [coordinates]
  rw [hr, cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_div_cancel_left₀ _ hd

local notation "e" => DependentFieldListMachines.fieldEncoding K dimension basis
local notation "ev" => DependentFieldCodecs.sigma ex e

theorem fp_paddedCoordinate (i : Fin c) : FP ev BitEncoding.rat
    (fun s => paddedCoordinates K dimension basis c s.1 s.2 i) :=
  (DependentFieldEqualityMachines.fp_coordinates ex K dimension basis).comp
    (DependentMonomialMachines.fp_getD BitEncoding.rat 0 i.val)

theorem fp_inclusionMatrix
    (hinclusion : FP (ex.prod (numberFieldEncoding sourceBasis)) ev (fun p => ⟨p.1,inclusion p.1 p.2⟩))
    (i : Fin c) (j : Fin sourceDimension) :
    FP ev BitEncoding.rat (fun s => inclusionMatrix sourceBasis K dimension basis inclusion c s.1 i j) := by
  have hx := DependentEncodingMachines.fp_parameter ex e
  have hi := (hx.pair (fp_const ev (numberFieldEncoding sourceBasis) (sourceBasis j))).comp hinclusion
  exact hi.comp (fp_paddedCoordinate ex K dimension basis c i)

/-- Every matrix entry, determinant and Cramer coordinate is a fixed finite
rational circuit. The inclusion is evaluated at the fixed source basis vectors. -/
theorem fp_descend
    (hinclusion : FP (ex.prod (numberFieldEncoding sourceBasis)) ev (fun p => ⟨p.1,inclusion p.1 p.2⟩)) :
    FP ev (numberFieldEncoding sourceBasis) (descend sourceBasis K dimension basis inclusion c) := by
  have hE := fp_inclusionMatrix sourceBasis ex K dimension basis inclusion c hinclusion
  have hG (i j : Fin sourceDimension) : FP ev BitEncoding.rat
      (fun s => gram sourceBasis K dimension basis inclusion c s.1 i j) :=
    FiniteRationalCircuits.fp_sum ev Finset.univ _ (fun k =>
      ((hE k i).pair (hE k j)).comp BinaryArithmetic.fp_rational_multiplication)
  have hR (i : Fin sourceDimension) : FP ev BitEncoding.rat
      (fun s => ((inclusionMatrix sourceBasis K dimension basis inclusion c s.1)ᵀ *ᵥ
        paddedCoordinates K dimension basis c s.1 s.2) i) :=
    FiniteRationalCircuits.fp_sum ev Finset.univ _ (fun k =>
      ((hE k i).pair (fp_paddedCoordinate ex K dimension basis c k)).comp BinaryArithmetic.fp_rational_multiplication)
  have hdet := FiniteRationalCircuits.fp_det ev (fun s => gram sourceBasis K dimension basis inclusion c s.1) hG
  apply FixedFieldArithmetic.fp_of_coordinates sourceBasis ev
  intro j
  have hcr := FiniteRationalCircuits.fp_cramer ev
    (fun s => gram sourceBasis K dimension basis inclusion c s.1)
    (fun s => (inclusionMatrix sourceBasis K dimension basis inclusion c s.1)ᵀ *ᵥ
      paddedCoordinates K dimension basis c s.1 s.2) hG hR j
  exact ((hcr.pair hdet).comp fp_rational_division).congr
    (fun s => by
      change coordinates sourceBasis K dimension basis inclusion c s j = _
      rw [descend, LinearEquiv.apply_symm_apply])

end PlanarHom.DependentFieldOutputDescent
