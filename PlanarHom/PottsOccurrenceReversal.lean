import PlanarHom.PottsRadialValueNormalization
import PlanarHom.RadialPottsHereditaryEuler
import PlanarHom.PlanarityLRRealizationGermPieces
import PlanarHom.PlanarityLRFacePermutation
import PlanarHom.FinitePermutationCycleTransport

/-! Explicit dart-convention adapter. Reversing every occurrence preserves
unoriented components and all symmetric Potts values, while matching the
clockwise drawing convention true=src used by geometric rotation rows. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsCentered
open MultiGraph PottsTwoStageInterpolation
variable {V E : Type} [Fintype V] [Fintype E]

 def reversedGraph (G : MultiGraph V E) : MultiGraph V E := ⟨G.dst,G.src⟩

 theorem reversed_component_iff (G : MultiGraph V E) (A : Finset E) (u v : V) :
    (reversedGraph G).componentSetoid A u v ↔ G.componentSetoid A u v := by
  constructor
  · intro h
    induction h with
    | rel u v h =>
      obtain ⟨e,he,rfl,rfl⟩ := h
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨e,he,rfl,rfl⟩)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij
  · intro h
    induction h with
    | rel u v h =>
      obtain ⟨e,he,rfl,rfl⟩ := h
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨e,he,rfl,rfl⟩)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

 @[simp] theorem reversed_componentCount (G : MultiGraph V E) (A : Finset E) :
    (reversedGraph G).componentCount A=G.componentCount A :=
  Fintype.card_congr (Quotient.congr (Equiv.refl V) (reversed_component_iff G A))

 theorem reversed_dartVertex (G : MultiGraph V E) (d : E×Bool) :
    (reversedGraph G).dartVertex d=(G.dartPair d).1 := by
  rcases d with ⟨e,b⟩
  cases b <;> rfl

 @[simp] theorem reversed_radialValue (G : MultiGraph V E) (δ : ℚ) (k : ℕ) :
    radialValue (reversedGraph G) δ k=radialValue G δ k := by
  simp only [radialValue,rankSubsetTutte_eq_component_sum,reversed_componentCount]

 theorem reversed_unweighted {C : Type} [Fintype C] (G : MultiGraph V E) (M : Matrix C C ℚ)
    (hM : ∀i j,M i j=M j i) : (reversedGraph G).unweighted M=G.unweighted M := by
  rw [unweighted_eq,unweighted_eq]
  exact Finset.sum_congr rfl (fun σ _ => Finset.prod_congr rfl (fun e _ => hM _ _))
end PlanarHom.PottsCentered

namespace PlanarHom.RadialPotts.Assembly
open MultiGraph FinitePermutationCycles PlanarityLRRealization
variable {E : Type} [Fintype E]

 theorem full_boundary_count_face (rotation : Equiv.Perm (Medial.Dart E)) :
    count (subsetBoundary rotation Finset.univ)=count (rotation*reversePerm E) := by
  have hp : subsetBoundary rotation Finset.univ=rotation.symm*reversePerm E := by
    apply Equiv.ext
    intro d
    simp [subsetBoundary,boundaryPermutation,selectedFlip,reversePerm,Equiv.Perm.mul_apply]
  rw [hp]
  have hc : count (rotation.symm*reversePerm E)=count ((rotation*reversePerm E).symm) := by
    apply count_of_step _ _ (reversePerm E)
    intro d
    rfl
  exact hc.trans (count_congr _ _ (Equiv.refl _) (fun _ _ => Equiv.Perm.sameCycle_inv))
end PlanarHom.RadialPotts.Assembly
