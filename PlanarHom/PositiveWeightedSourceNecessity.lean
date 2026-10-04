import PlanarHom.PositiveNormalizedCoreSource
import PlanarHom.PositiveNormalizationMomentConsequences
import PlanarHom.PositiveWeightedAmplitudeReconstruction
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity
variable {q bt ut : ℕ} [Nonempty (Fin q)]
theorem positive_weighted_block_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hp : ∀ i j,0<L.matrices old i j) (hinj : Function.Injective (L.matrices old))
    (hw : ∀ i,0<L.weights i) (hnot : ¬PromisedSharpPHard L.problem) :
    Structures.AllowedWeightedBlock (L.matrices old) L.weights := by
  obtain ⟨d,eQ,ρ,hρ,hcore⟩ := L.normalized_quotient_tensor_of_not_hard hPotts old hs hp hw hnot
  have hm := L.normalized_weighted_moments_constant hPotts old hs hp hw hnot
  exact PositiveWeightedAmplitudeReconstruction.allowed_block_of_weighted_moments
    (L.matrices old) hp hs hinj L.weights hw (fun r s m=>hm m r s) eQ ρ hρ hcore
theorem positive_weighted_block_hard_of_not_allowed (hPotts : PositivePottsFoundation)
    (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hp : ∀ i j,0<L.matrices old i j) (hinj : Function.Injective (L.matrices old))
    (hw : ∀ i,0<L.weights i)
    (hbad : ¬Structures.AllowedWeightedBlock (L.matrices old) L.weights) :
    PromisedSharpPHard L.problem := by
  by_contra hnot
  exact hbad (L.positive_weighted_block_of_not_hard hPotts old hs hp hinj hw hnot)
end PlanarHom.AlgebraicProductInterpolation.RealLanguage
