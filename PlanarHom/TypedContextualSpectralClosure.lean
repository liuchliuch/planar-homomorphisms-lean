import PlanarHom.TypedContextualSpectralRational
import PlanarHom.TypedContextualSpectralEffective
import PlanarHom.ClosedFamilyDistanceKernels

/-! Source-facing spectral closure facts for the actual typed X-family.
The effective closure certificate is proved from programs, not a hypothesis. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open ClosedMatrixFamily
variable {x y s : ℕ}

theorem xFamily_symmetric (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) (H : Matrix (Fin x) (Fin x) ℝ)
    (hH : H∈xFamily F FB) : H.IsHermitian := hH.1

theorem xFamily_algebraic (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) (H : Matrix (Fin x) (Fin x) ℝ)
    (hH : H∈xFamily F FB) : ∀i j,IsAlgebraic ℚ (H i j) :=
  algebraic_of_zeroExtendFin H hH.2.algebraic

/-- The actual program-based family satisfies the source's effective closure
interface, including the empty side where all X matrices coincide. -/
theorem xFamily_effectiveClosed (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) : EffectiveSpectralClosed (xFamily F FB) where
  transfer_mem H hH N hpd _ hNs hN hp hi := by
    by_cases hx : Nonempty (Fin x)
    · obtain ⟨n₀,hn₀,hp⟩ := hp
      exact xFamily_effective F FB H hH hpd N hN hNs (Classical.choice hx) n₀ hn₀ hp hi
    · haveI : IsEmpty (Fin x) := not_nonempty_iff.mp hx
      have he : N=H := Subsingleton.elim _ _
      exact he.symm ▸ hH

end PlanarHom.TypedBipartiteContext
