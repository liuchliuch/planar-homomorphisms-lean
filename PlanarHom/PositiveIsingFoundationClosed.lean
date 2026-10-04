import PlanarHom.BooleanTensorEasyAssembly
import PlanarHom.FKTIsingTractability

/-! NEW source foundation discharge. The actual ordinary-input Fisher/FKT
algorithm, with internally computed orientation and calibration, proves the
positive zero-field Ising foundation in every original fixed number field. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.BooleanTensorEasyAssembly

theorem positiveIsingFoundation : PositiveIsingFoundation := by
  intro K hfinite dimension basis ρ hρ
  exact FKTIsingMachines.ising_inFP_of_pos basis K.val.toRingHom ρ hρ

end PlanarHom.BooleanTensorEasyAssembly
