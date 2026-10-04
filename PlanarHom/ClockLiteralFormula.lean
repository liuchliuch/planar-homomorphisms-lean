import PlanarHom.ClockMatrixObstruction

namespace PlanarHom.ClockModel

theorem interaction_formula (q:ℕ) (K:ℝ) (i j:Fin q) :
    interaction q K i j=Real.exp (K*Real.cos (2*Real.pi*((i.val:ℝ)-(j.val:ℝ))/(q:ℝ))) := by
  unfold interaction angle
  congr 2
  ring

end PlanarHom.ClockModel
