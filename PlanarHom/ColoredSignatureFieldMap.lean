import PlanarHom.ColoredSeriesGadget

/-! NEW reconstruction. Ring homomorphisms preserve the literal complete
colored gadget sum, with one weight per private vertex and every occurrence. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.TwoTerminal
variable {J E C R S : Type} [Fintype J] [Fintype E] [Fintype C]
    [CommSemiring R] [CommSemiring S]

theorem map_coloredSignature (φ : R →+* S) (G : TwoTerminal J E)
    (W : E → Matrix C C R) (w : C → R) (i j : C) :
    φ (coloredSignature G W w i j) =
      coloredSignature G (fun e a b => φ (W e a b)) (fun a => φ (w a)) i j := by
  simp [coloredSignature, map_sum, map_mul, map_prod]

end PlanarHom.TwoTerminal
