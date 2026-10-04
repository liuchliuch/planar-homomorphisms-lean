import PlanarHom.ReimplementedFiniteTwins.QuotientReindex
import PlanarHom.WeightedStructureTransport

noncomputable section
open Classical
namespace PlanarHom.Structures
variable {C D:Type} [Fintype C] [Fintype D]
open Twins.ReconstructedReindex

theorem positiveVertexWeightClass_reindex_iff (M:Matrix C C ℝ) (w:C→ℝ)
    (hs:∀i j,M i j=M j i) (e:D≃C) :
    PositiveVertexWeightClass (matrix M e) (fun i=>w (e i)) (symmetric M e hs) ↔
      PositiveVertexWeightClass M w hs := by
  let eq:=quotientEquiv M e
  have hm:(fun i j=>Twins.quotientMatrix M hs (eq i) (eq j))=
      Twins.quotientMatrix (matrix M e) (symmetric M e hs) := by
    funext i j; exact (quotientMatrix_transport M e hs i j).symm
  have hw:(fun i=>Twins.quotientWeight M w (eq i))=
      Twins.quotientWeight (matrix M e) (fun i=>w (e i)) := by
    funext i; exact (quotientWeight_transport M e w i).symm
  constructor
  · intro h
    apply WeightedClass.of_equiv eq
    rwa [hm,hw]
  · intro h
    have h':=h.equiv eq
    rwa [hm,hw] at h'

end PlanarHom.Structures
