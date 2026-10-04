import PlanarHom.RadialPottsBoundaryPermutation
import PlanarHom.FinitePermutationSwapBound
import PlanarHom.FisherIncidenceOrdering

/-! Selected boundary cycles stay inside actual selected graph components.
This uses only vertex-preserving rotation, not planarity or Euler. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph FinitePermutationCycles
variable {V E : Type} [Fintype V] [Fintype E]
local instance (priority := high) : DecidableEq (Medial.Dart E) := Classical.decEq _

def subsetBoundary (rotation : Equiv.Perm (Medial.Dart E)) (A : Finset E) :=
  boundaryPermutation rotation (fun e => decide (e∈A))

@[simp] theorem subsetBoundary_empty (rotation : Equiv.Perm (Medial.Dart E)) :
    subsetBoundary rotation ∅=rotation.symm := by
  apply Equiv.ext
  intro d
  simp [subsetBoundary,boundaryPermutation,selectedFlip]

theorem subsetBoundary_insert (rotation : Equiv.Perm (Medial.Dart E)) (A : Finset E)
    (e : E) (he : e∉A) :
    subsetBoundary rotation (insert e A)=swapInput (subsetBoundary rotation A) (e,false) (e,true) := by
  apply Equiv.ext
  rintro ⟨f,b⟩
  by_cases hf : f=e
  · subst f
    cases b <;> simp [subsetBoundary,boundaryPermutation,selectedFlip,swapInput,he]
  · have h₀ : (f,b)≠(e,false) := by intro h; exact hf (congrArg Prod.fst h)
    have h₁ : (f,b)≠(e,true) := by intro h; exact hf (congrArg Prod.fst h)
    simp [subsetBoundary,boundaryPermutation,selectedFlip,swapInput,
      Equiv.swap_apply_of_ne_of_ne h₀ h₁,hf]

theorem subsetBoundary_step (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E))
    (hhost : ∀d,G.dartVertex (rotation d)=G.dartVertex d) (A : Finset E) (d : Medial.Dart E) :
    G.componentSetoid A (G.dartVertex d) (G.dartVertex (subsetBoundary rotation A d)) := by
  have hh : ∀d,G.dartVertex (rotation.symm d)=G.dartVertex d := by
    intro d
    have h := hhost (rotation.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  change G.componentSetoid A (G.dartVertex d)
    (G.dartVertex (rotation.symm (selectedFlip (fun e => decide (e∈A)) d)))
  rw [hh]
  rcases d with ⟨e,b⟩
  by_cases he : e∈A
  · cases b
    · simpa [selectedFlip,dartVertex,he] using
        (show G.componentSetoid A (G.src e) (G.dst e) from Relation.EqvGen.rel _ _ ⟨e,he,rfl,rfl⟩)
    · simpa [selectedFlip,dartVertex,he] using
        (Relation.EqvGen.symm _ _ (show G.componentSetoid A (G.src e) (G.dst e) from
          Relation.EqvGen.rel _ _ ⟨e,he,rfl,rfl⟩))
  · simp only [selectedFlip,Equiv.coe_fn_mk,he,decide_false,if_false]
    exact Relation.EqvGen.refl _

theorem subsetBoundary_sameCycle_component (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E))
    (hhost : ∀d,G.dartVertex (rotation d)=G.dartVertex d) (A : Finset E)
    {a b : Medial.Dart E} (h : (subsetBoundary rotation A).SameCycle a b) :
    G.componentSetoid A (G.dartVertex a) (G.dartVertex b) := by
  have hr := (permutation_reach_iff (subsetBoundary rotation A) a b).mpr h
  clear h
  induction hr with
  | rel a b h =>
    obtain ⟨d,_,rfl,rfl⟩ := h
    exact subsetBoundary_step G rotation hhost A d
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

theorem subsetBoundary_insert_separate (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E))
    (hhost : ∀d,G.dartVertex (rotation d)=G.dartVertex d) (A : Finset E) (e : E) (he : e∉A)
    (hsep : ¬G.componentSetoid A (G.src e) (G.dst e)) :
    count (subsetBoundary rotation (insert e A))+1=count (subsetBoundary rotation A) := by
  rw [subsetBoundary_insert rotation A e he]
  apply count_swap_of_separate
  intro h
  exact hsep (subsetBoundary_sameCycle_component G rotation hhost A h)
end PlanarHom.RadialPotts.Assembly
