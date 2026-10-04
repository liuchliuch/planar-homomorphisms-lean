import PlanarHom.CommonAmplitudeCoordinates
import PlanarHom.Normalization
import PlanarHom.Boolean

/-! NEW reconstruction of the original positive symmetric interaction from
its normalized actual-row quotient and genuine class moments. Repeated source
amplitudes are kept by the finite-moment fiber bijection. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.PositiveAmplitudeReconstruction
open Boolean
variable {q d : ℕ} [Nonempty (Fin q)]

theorem original_amplitude_tensor (M : Matrix (Fin q) (Fin q) ℝ)
    (hpos : ∀ i j, 0 < M i j) (hs : ∀ i j, M i j = M j i)
    (hmom : ∀ r s : Quotient (Twins.rowSetoid (diagonalNormalize M)), ∀ m : ℕ,
      Twins.quotientWeight (diagonalNormalize M) (fun i => M i i ^ m) r =
      Twins.quotientWeight (diagonalNormalize M) (fun i => M i i ^ m) s)
    (eQ : Quotient (Twins.rowSetoid (diagonalNormalize M)) ≃ Cube d)
    (ρ : Fin d → ℝ)
    (hcore : ∀ r s, Twins.quotientMatrix (diagonalNormalize M)
      (diagonalNormalize_symmetric M hs) r s = tensor ρ (eQ r) (eQ s)) :
    ∃ k : ℕ, ∃ a : Fin k → ℝ, ∃ e : Fin q ≃ Fin k × Cube d,
      0 < k ∧ (∀ i, 0 < a i) ∧
      ∀ i j, M i j = a (e i).1 * a (e j).1 * tensor ρ (e i).2 (e j).2 := by
  let cls : Fin q → Quotient (Twins.rowSetoid (diagonalNormalize M)) := Quotient.mk _
  have hsurj : Function.Surjective cls := fun r => ⟨r.out, Quotient.out_eq r⟩
  letI : Nonempty (Quotient (Twins.rowSetoid (diagonalNormalize M))) :=
    ⟨cls (Classical.arbitrary (Fin q))⟩
  obtain ⟨k,a,ex,hk,ha,hcls,hamp⟩ :=
    CommonAmplitudeCoordinates.exists_common_amplitude_chart cls hsurj
      (fun i => Real.sqrt (M i i)) (fun i => Real.sqrt_pos.mpr (hpos i i)) (by
        intro r s m
        have hh := hmom r s m
        change (∑ x : {x // cls x = r}, M x.val x.val ^ m) =
          ∑ y : {y // cls y = s}, M y.val y.val ^ m at hh
        convert hh using 1 <;>
          apply Finset.sum_congr (by ext x; simp) <;>
          intro x hx <;> rw [pow_mul, Real.sq_sqrt (hpos _ _).le])
  let e : Fin q ≃ Fin k × Cube d := ex.trans
    ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) eQ))
  refine ⟨k,a,e,hk,ha,?_⟩
  intro i j
  have hn : diagonalNormalize M i j = tensor ρ (eQ (cls i)) (eQ (cls j)) :=
    hcore (cls i) (cls j)
  have he (i : Fin q) : e i = ((ex i).2, eQ (cls i)) := by
    change ((ex i).2, eQ (ex i).1) = ((ex i).2, eQ (cls i))
    rw [hcls]
  rw [he,he]
  rw [diagonalNormalize_recover M (fun i=>hpos i i),hn,hamp,hamp]

end PlanarHom.PositiveAmplitudeReconstruction
