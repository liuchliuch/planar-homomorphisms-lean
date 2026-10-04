import PlanarHom.BooleanSpectralCounts
import Mathlib.Data.Fintype.EquivFin

/-! NEW exact fixed classes of equal normalized parameter pairs. Every class
has an original coordinate witness, and multiplicities count actual coordinates. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanParameterClasses
variable {K : Type} {d : ℕ}

def pairs (θ w : Fin d→K) : Finset (K×K):=Finset.univ.image (fun i=>(θ i,w i))
abbrev count (θ w : Fin d→K) : ℕ := Fintype.card ↥(pairs θ w)

def representative (θ w : Fin d→K) (g : Fin (count θ w)) : K×K :=
  ((Fintype.equivFin ↥(pairs θ w)).symm g).val

def classOf (θ w : Fin d→K) (i : Fin d) : Fin (count θ w) :=
  Fintype.equivFin ↥(pairs θ w) ⟨(θ i,w i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

@[simp] theorem representative_classOf (θ w : Fin d→K) (i : Fin d) :
    representative θ w (classOf θ w i)=(θ i,w i) := by
  simp only [representative,classOf,Equiv.symm_apply_apply]

theorem representative_injective (θ w : Fin d→K) : Function.Injective (representative θ w) := by
  intro i j h
  apply (Fintype.equivFin ↥(pairs θ w)).symm.injective
  exact Subtype.ext h

theorem representative_has_coordinate (θ w : Fin d→K) (g : Fin (count θ w)) :
    ∃i:Fin d,representative θ w g=(θ i,w i) := by
  have h:=((Fintype.equivFin ↥(pairs θ w)).symm g).property
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp h
  exact ⟨i,hi.symm⟩

theorem classOf_surjective (θ w : Fin d→K) : Function.Surjective (classOf θ w) := by
  intro g
  obtain ⟨i,hi⟩:=representative_has_coordinate θ w g
  exact ⟨i,representative_injective θ w ((representative_classOf θ w i).trans hi.symm)⟩

theorem multiplicity_pos (θ w : Fin d→K) (g : Fin (count θ w)) :
    0<BooleanSpectralCounts.multiplicity (classOf θ w) g := by
  obtain ⟨i,hi⟩:=classOf_surjective θ w g
  apply Finset.card_pos.mpr
  exact ⟨i,by simp [hi]⟩

end PlanarHom.BooleanParameterClasses
