import PlanarHom.CommonWeightedAmplitudeCoordinates
import PlanarHom.Normalization
import PlanarHom.Structures

/-! NEW: actual normalized class moments reconstruct the original positive
weighted block. Original row injectivity supplies precisely the within-fiber
amplitude injectivity required by the common weighted chart theorem. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.PositiveWeightedAmplitudeReconstruction
open Boolean Structures
variable {q d : ℕ} [Nonempty (Fin q)]

theorem allowed_block_of_weighted_moments (M : Matrix (Fin q) (Fin q) ℝ)
    (hpos : ∀ i j, 0 < M i j) (hs : ∀ i j, M i j = M j i)
    (hinj : Function.Injective M) (w : Fin q → ℝ) (hw : ∀ i, 0 < w i)
    (hmom : ∀ r s : Quotient (Twins.rowSetoid (diagonalNormalize M)), ∀ m : ℕ,
      Twins.quotientWeight (diagonalNormalize M) (fun i => w i * M i i ^ m) r =
      Twins.quotientWeight (diagonalNormalize M) (fun i => w i * M i i ^ m) s)
    (eQ : Quotient (Twins.rowSetoid (diagonalNormalize M)) ≃ Cube d)
    (ρ : Fin d → ℝ) (hρ : ∀ i, 0 < ρ i ∧ ρ i ≠ 1)
    (hcore : ∀ r s, Twins.quotientMatrix (diagonalNormalize M)
      (diagonalNormalize_symmetric M hs) r s = tensor ρ (eQ r) (eQ s)) :
    AllowedWeightedBlock M w := by
  let cls : Fin q → Quotient (Twins.rowSetoid (diagonalNormalize M)) := Quotient.mk _
  have hsurj : Function.Surjective cls := fun r => ⟨r.out, Quotient.out_eq r⟩
  letI : Nonempty (Quotient (Twins.rowSetoid (diagonalNormalize M))) :=
    ⟨cls (Classical.arbitrary (Fin q))⟩
  have hai : ∀ r, Function.Injective
      (fun x : {x // cls x = r} => Real.sqrt (M x.val x.val)) := by
    intro r x y he
    dsimp only at he
    apply Subtype.ext
    apply hinj
    apply (row_eq_iff_normalized_row_eq_and_diagonal_eq M (fun i=>hpos i i) hs _ _).mpr
    constructor
    · exact funext (Quotient.exact (x.property.trans y.property.symm))
    · have hx := Real.sq_sqrt (hpos x.val x.val).le
      have hy := Real.sq_sqrt (hpos y.val y.val).le
      rw [he] at hx
      exact hx.symm.trans hy
  obtain ⟨k,a,mass,ex,hk,ha,hm,hcls,hamp,hweight⟩ :=
    CommonWeightedAmplitudeCoordinates.exists_common_weighted_chart cls hsurj
      (fun i => Real.sqrt (M i i)) w (fun i => Real.sqrt_pos.mpr (hpos i i)) hw hai (by
        intro r s m
        have hh := hmom r s m
        change (∑ x : {x // cls x = r}, w x.val * M x.val x.val ^ m) =
          ∑ y : {y // cls y = s}, w y.val * M y.val y.val ^ m at hh
        convert hh using 1 <;>
          apply Finset.sum_congr (by ext x; simp) <;>
          intro x hx <;> rw [pow_mul, Real.sq_sqrt (hpos _ _).le])
  let e : Fin q ≃ Fin k × Cube d := ex.trans
    ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) eQ))
  have he (i : Fin q) : e i = ((ex i).2, eQ (cls i)) := by
    change ((ex i).2, eQ (ex i).1) = ((ex i).2, eQ (cls i))
    rw [hcls]
  refine .positive k d hk a mass ρ ha hm hρ e ?_ ?_
  · intro i j
    have hn : diagonalNormalize M i j = tensor ρ (eQ (cls i)) (eQ (cls j)) :=
      hcore (cls i) (cls j)
    rw [he,he]
    rw [diagonalNormalize_recover M (fun i=>hpos i i),hn,hamp,hamp]
  · intro i
    rw [he]
    exact hweight i

end PlanarHom.PositiveWeightedAmplitudeReconstruction
