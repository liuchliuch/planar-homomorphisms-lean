import PlanarHom.HammingPottsProductIdentities

noncomputable section
open scoped BigOperators
namespace PlanarHom.HammingPottsIsolationRegressions
open CliqueSizePolynomials HammingPottsProductIdentities

example : (diagonal 2).eval (-3) = (10:ℝ) := by norm_num [diagonal]
example : (diagonal 3).eval (-3) = (19:ℝ) := by norm_num [diagonal]
example : (offDiagonal 2).eval (-3) = (-6:ℝ) := by norm_num [offDiagonal]
example : (offDiagonal 3).eval (-3) = (3:ℝ) := by norm_num [offDiagonal]
example : ¬ primeFactor 3 ∣ primeFactor 4 := by simp [factor_dvd_factor_iff]
example : Prime (primeFactor 3) := factor_prime (by decide)
example : emultiplicity (primeFactor 3) (offDiagonal 2) = 0 :=
  multiplicity_offDiagonal (by decide) 2
example : emultiplicity (primeFactor 3) (diagonal 3 * diagonal 2) = 1 := by
  rw [emultiplicity_mul (factor_prime (by decide)),
    multiplicity_diagonal (by decide) (by decide),
    multiplicity_diagonal (by decide) (by decide)]
  norm_num

example (u v : Color (fun r : Fin 0 => r.elim0)) (t : ℝ) :
    squareFamily (fun r : Fin 0 => r.elim0) t u v = 1 := by
  simp [squareFamily_entry]
example (u v : Color (fun r : Fin 0 => r.elim0)) (s : ℕ) :
    target (fun r : Fin 0 => r.elim0) s u v = 1 := by simp [target]

example (u : Color (fun _ : Fin 1 => 3)) :
    target (fun _ : Fin 1 => 3) 3 u u = 2 := by simp [target]
example (u v : Color (fun _ : Fin 1 => 3)) :
    target (fun _ : Fin 1 => 3) 4 u v = 1 := by simp [target]

/-- Actual generic source product interface, retaining arbitrary source color coordinates. -/
example {q d : ℕ} (sizes : Fin d → ℕ) (hsizes : ∀ r, 2 ≤ sizes r)
    {s : ℕ} (hs : 3 ≤ s) (e : Fin q ≃ Color sizes) :
    EffectiveProductTransfer.ProductIdentities
      (fun t i j => squareFamily sizes t (e i) (e j))
      (fun i j => target sizes s (e i) (e j)) :=
  productIdentities sizes hsizes (by omega) e

end PlanarHom.HammingPottsIsolationRegressions
