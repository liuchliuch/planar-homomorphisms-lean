import PlanarHom.TypedContextualMatrixAvailability
import PlanarHom.TypedBipartiteSpectral

/-! Shared concrete two-side coordinates for the typed retained-context families.
The family membership is actual contextual program availability, not individual
oracle reducibility or a supplied closure certificate. -/
noncomputable section
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteSpectral
variable {x y s : ℕ}

def domains (x y : ℕ) : Fin 2→Set (Fin (x+y)) :=
  Fin.cases (Set.range (Fin.castAdd y)) (fun _=>Set.range (Fin.natAdd x))

def sameX : Fin 2→Fin 2→Prop := fun a b=>a=0 ∧ b=0
def sameY : Fin 2→Fin 2→Prop := fun a b=>a=1 ∧ b=1
def crossPolicy : Fin 2→Fin 2→Prop := fun a b=>a≠b

def xFamily (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) : Set (Matrix (Fin x) (Fin x) ℝ) :=
  {N | N.IsHermitian ∧ TypedContextuallyAvailable (domains x y) F FB
    (zeroExtendFin (y:=y) N) sameX}

end PlanarHom.TypedBipartiteContext
