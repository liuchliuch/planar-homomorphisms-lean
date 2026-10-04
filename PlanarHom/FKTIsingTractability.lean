import PlanarHom.FKTIsingCorrectness
import PlanarHom.PromisePolynomialTime
import PlanarHom.RootedHomogeneousSemantics

/-! Ordinary planar zero-field Ising is in genuine polynomial bit time in the
specified original fixed field. Every successful raw encoding is handled by the
proved normalizer; no embedded-input or canonical-input restriction is added. -/
noncomputable section
open Classical
namespace PlanarHom.FKTIsingMachines
open Complexity
variable {K:Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension:ℕ}

theorem ising_inFP (basis:Module.Basis (Fin dimension) ℚ K) (φ:K→+*ℝ)
    (ρ:K) (hρ:1+φ ρ≠0):
    (MixedCode.evaluationProblem basis (fun _:Fin 1=>matrix ρ)
      (fun u:Fin 0=>Fin.elim0 u) (fun _=>1)).InFP:=by
  apply (MixedCode.evaluation_inFP_iff basis _ _ _).mpr
  have h:=(fp_value basis ρ).transportInput
    (ea:=MixedCode.encoding.restrict (MixedCode.PlanarValid 1 0)) Subtype.val (fun _=>rfl)
  apply h.congr
  intro g
  exact (value_eq_partition basis φ g.property ρ hρ).trans
    (MixedCode.evaluate_homogeneous g.val g.property.1 (matrix ρ) (fun _=>1)).symm

theorem ising_inFP_of_pos (basis:Module.Basis (Fin dimension) ℚ K) (φ:K→+*ℝ)
    (ρ:K) (hρ:0<φ ρ):
    (MixedCode.evaluationProblem basis (fun _:Fin 1=>matrix ρ)
      (fun u:Fin 0=>Fin.elim0 u) (fun _=>1)).InFP:=
  ising_inFP basis φ ρ (ne_of_gt (add_pos zero_lt_one hρ))

end PlanarHom.FKTIsingMachines
