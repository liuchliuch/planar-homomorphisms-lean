import PlanarHom.PositivePottsFoundationClosed
import PlanarHom.MainDichotomyFinalAssembly

/-! Closed algebraic Theorems 1.1 and 1.3. Both independent
hardness and Ising foundations are instantiated by their actual source proofs.
The original complete row quotient, weights and ordinary planar-input promises
are retained. The full-real appendix is a separate statement. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.MainDichotomyScope
open AlgebraicProductInterpolation.RealLanguage

theorem theorem11 : Theorem11Statement := theorem11Statement_of_potts positivePottsFoundation

theorem theorem13 : Theorem13Statement := theorem13Statement_of_potts positivePottsFoundation

end PlanarHom.MainDichotomyScope
