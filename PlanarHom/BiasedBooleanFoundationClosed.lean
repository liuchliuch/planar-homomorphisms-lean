import PlanarHom.BiasedPositiveReduction
import PlanarHom.BooleanTensorSourceAssembly

/-! The independently requested biased Boolean hardness foundation is inhabited
by the actual signed-NAND reduction, rather than assumed at the tensor boundary. -/
noncomputable section
namespace PlanarHom.BiasedPositiveHardness

/-- Closed foundation for every real-embedded finite coefficient field and its
actual basis-coded positive, symmetric, biased, nonsingular Boolean matrix. -/
theorem biasedBooleanFoundation : BooleanTensorSourceAssembly.BiasedBooleanFoundation := by
  intro K _ dimension basis B hs hpos hbias hdet
  exact promisedSharpPHard basis K.subtype B hs hpos hbias hdet

end PlanarHom.BiasedPositiveHardness
