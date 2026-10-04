import PlanarHom.SurfaceFKTCorrectness
import PlanarHom.SurfaceFKTValueMachines
import PlanarHom.SurfaceRowToEmbedding
import PlanarHom.RootedHomogeneousSemantics

/-! NEW supplied-surface zero-field Ising membership in actual polynomial bit
time, in the original fixed number field and on every accepted raw encoding. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceFKT
open Complexity SurfaceRowEvaluation
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}

theorem ising_evaluable (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K→+*ℝ) (ρ : K) (hρ : 1+φ ρ≠0) :
    Evaluable ambient basis (fun _:Fin 1 => matrix ρ) (fun u:Fin 0=>u.elim0) (fun _=>1) := by
  letI : CharZero K := φ.charZero
  have h := (fp_value basis ambient ρ).transportInput
    (ea:=SurfaceRowEvaluation.encoding.restrict (SurfaceRowEvaluation.Valid 1 0 ambient))
    Subtype.val (fun _ => rfl)
  apply h.congr
  intro p
  obtain ⟨hg,R,hr,hd⟩ := p.property
  exact (value_eq_partition basis ambient p.val.1 hg p.val.2 R hr hd φ ρ hρ).trans
    (MixedCode.evaluate_homogeneous p.val.1 hg (matrix ρ) (fun _=>1)).symm

theorem ising_evaluable_of_pos (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K→+*ℝ) (ρ : K) (hρ : 0<φ ρ) :
    Evaluable ambient basis (fun _:Fin 1 => matrix ρ) (fun u:Fin 0=>u.elim0) (fun _=>1) :=
  ising_evaluable ambient basis φ ρ (ne_of_gt (add_pos zero_lt_one hρ))

theorem ising_inFP (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K→+*ℝ) (ρ : K) (hρ : 1+φ ρ≠0) :
    (SurfaceRawEmbedding.evaluationProblem ambient basis (fun _:Fin 1 => matrix ρ)
      (fun u:Fin 0=>u.elim0) (fun _=>1)).InFP :=
  SurfaceRowEvaluation.evaluable_inFP ambient basis _ _ _ (ising_evaluable ambient basis φ ρ hρ)

theorem ising_inFP_of_pos (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K→+*ℝ) (ρ : K) (hρ : 0<φ ρ) :
    (SurfaceRawEmbedding.evaluationProblem ambient basis (fun _:Fin 1 => matrix ρ)
      (fun u:Fin 0=>u.elim0) (fun _=>1)).InFP :=
  ising_inFP ambient basis φ ρ (ne_of_gt (add_pos zero_lt_one hρ))

theorem positiveIsingFoundation (ambient : ℕ) : SurfaceRowEvaluation.PositiveIsingFoundation ambient := by
  intro K _ dimension basis ρ hρ
  exact ising_evaluable_of_pos ambient basis K.subtype ρ hρ

end PlanarHom.SurfaceFKT
