import PlanarHom.RadialPottsBoundaryContainment
import PlanarHom.PottsComponentRank
import Mathlib.Data.Finset.Interval

/-! Hereditary Euler from full Euler. The integer defect is monotone under
adding selected occurrences, starts at zero, and ends at zero for a planar
rotation. No Euler identity on a selected subgraph is supplied as a premise. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph FinitePermutationCycles
variable {V E : Type} [Fintype V] [Fintype E]

/-- A complete vertex rotation has one literal cycle at every nonisolated
vertex. Surjectivity explicitly rules out unrepresented isolated vertices. -/
theorem rotation_count_vertices (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E))
    (hcycles : ∀a b,rotation.SameCycle a b ↔ G.dartVertex a=G.dartVertex b)
    (hsurj : Function.Surjective G.dartVertex) : count rotation=Fintype.card V := by
  let f : Quotient (Equiv.Perm.SameCycle.setoid rotation) → V :=
    Quotient.lift G.dartVertex (fun a b h => (hcycles a b).mp h)
  have hi : Function.Injective f := by
    intro x y h
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b => exact Quotient.sound ((hcycles a b).mpr h)
  have hs : Function.Surjective f := by
    intro v
    obtain ⟨d,hd⟩ := hsurj v
    exact ⟨Quotient.mk _ d,hd⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).trans (Nat.card_eq_fintype_card (α:=V))

theorem subsetBoundary_empty_count (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E))
    (hcycles : ∀a b,rotation.SameCycle a b ↔ G.dartVertex a=G.dartVertex b)
    (hsurj : Function.Surjective G.dartVertex) : count (subsetBoundary rotation ∅)=Fintype.card V := by
  rw [subsetBoundary_empty]
  have hi : count rotation.symm=count rotation := count_congr _ _ (Equiv.refl _)
    (fun _ _ => Equiv.Perm.sameCycle_inv)
  rw [hi,rotation_count_vertices G rotation hcycles hsurj]

def eulerDefect (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E)) (A : Finset E) : ℤ :=
  2*(G.componentCount A:ℤ)+(A.card:ℤ)-(Fintype.card V:ℤ)-(count (subsetBoundary rotation A):ℤ)

/-- Selecting one occurrence cannot reduce the combinatorial genus defect. -/
theorem eulerDefect_insert_le (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E))
    (hhost : ∀d,G.dartVertex (rotation d)=G.dartVertex d) (A : Finset E) (e : E) (he : e∉A) :
    eulerDefect G rotation A≤eulerDefect G rotation (insert e A) := by
  have hcard := Finset.card_insert_of_not_mem he
  by_cases hc : G.componentSetoid A (G.src e) (G.dst e)
  · have hcomp := G.componentCount_insert_of_related A e hc
    have hbound := count_swap_le_add_one (subsetBoundary rotation A) (e,false) (e,true)
    rw [← subsetBoundary_insert rotation A e he] at hbound
    dsimp [eulerDefect]
    omega
  · have hcomp := G.componentCount_insert_add_one_of_not_related A e hc
    have hbound := subsetBoundary_insert_separate G rotation hhost A e he hc
    dsimp [eulerDefect]
    omega

theorem eulerDefect_monotone (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E))
    (hhost : ∀d,G.dartVertex (rotation d)=G.dartVertex d) : Monotone (eulerDefect G rotation) :=
  Finset.monotone_iff_forall_le_insert.mpr (fun A e he => eulerDefect_insert_le G rotation hhost A e he)

/-- Full planar Euler forces the exact spanning-subgraph boundary identity for
all edge subsets, retaining the inactive darts as markers. -/
theorem hereditary_boundary_euler (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E))
    (hcycles : ∀a b,rotation.SameCycle a b ↔ G.dartVertex a=G.dartVertex b)
    (hsurj : Function.Surjective G.dartVertex)
    (hfull : Fintype.card V+count (subsetBoundary rotation Finset.univ)=
      Fintype.card E+2*G.componentCount Finset.univ) (A : Finset E) :
    Fintype.card V+count (subsetBoundary rotation A)=A.card+2*G.componentCount A := by
  have hhost : ∀d,G.dartVertex (rotation d)=G.dartVertex d := by
    intro d
    exact (hcycles _ _).mp Equiv.Perm.SameCycle.rfl.apply_left
  have hempty : eulerDefect G rotation ∅=0 := by
    unfold eulerDefect
    rw [componentCount_empty,subsetBoundary_empty_count G rotation hcycles hsurj]
    simp
    ring
  have htop : eulerDefect G rotation Finset.univ=0 := by
    dsimp [eulerDefect]
    omega
  have hlow := eulerDefect_monotone G rotation hhost (Finset.empty_subset A)
  have hhigh := eulerDefect_monotone G rotation hhost (Finset.subset_univ A)
  rw [hempty] at hlow
  rw [htop] at hhigh
  dsimp [eulerDefect] at hlow hhigh
  omega
end PlanarHom.RadialPotts.Assembly
