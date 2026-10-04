import PlanarHom.PottsOccurrenceReversal
import PlanarHom.PlanarityLRDualReachability
import PlanarHom.RotationFaceCycleDuality

/-! Hereditary Euler in the literal geometric row/edge-reversal convention,
including every inactive dart marker. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn FinitePermutationCycles RadialPotts.Assembly PottsCentered
variable {V E : Type} [Fintype V] [Fintype E] [dD : DecidableEq (Dart E)] {G : MultiGraph V E}

 theorem sameCycle_iff_host (R : RotationRows G) (a b : Dart E) :
    R.rotation.SameCycle a b ↔ (G.dartPair a).1=(G.dartPair b).1 := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hh := R.rotation_iterate_host a n
    rw [Equiv.Perm.iterate_eq_pow,hn] at hh
    exact hh.symm
  · intro h
    obtain ⟨n,hn⟩ := R.exists_rotation_iterate_of_sameHost a b h
    exact ⟨(n:ℤ),by simpa only [zpow_natCast,Equiv.Perm.iterate_eq_pow] using hn⟩

 theorem rotation_count_of_incident (R : RotationRows G)
    (hi : ∀v,∃a : Dart E,(G.dartPair a).1=v) : count R.rotation=Fintype.card V := by
  apply rotation_count_vertices (reversedGraph G) R.rotation
  · intro a b
    simpa only [reversed_dartVertex] using sameCycle_iff_host R a b
  · intro v
    obtain ⟨a,ha⟩ := hi v
    exact ⟨a,by simpa only [reversed_dartVertex] using ha⟩

 theorem boundary_count_selected_face (P : Equiv.Perm (Dart E)) (choice : E→Bool) :
    count (boundaryPermutation P choice)=count (P*selectedFlip choice) := by
  have hc : count (boundaryPermutation P choice)=count ((P*selectedFlip choice).symm) := by
    apply count_of_step _ _ (selectedFlip choice)
    intro d
    rfl
  exact hc.trans (count_congr _ _ (Equiv.refl _) (fun _ _ => Equiv.Perm.sameCycle_inv))

 theorem hereditary_euler (R : RotationRows G)
    (hi : ∀v,∃a : Dart E,(G.dartPair a).1=v)
    (he : Fintype.card V+count R.facePerm=Fintype.card E+2*G.componentCount Finset.univ)
    (A : Finset E) :
    Fintype.card V+count (R.rotation*selectedFlip (fun e=>decide (e∈A)))=
      A.card+2*G.componentCount A := by
  have hc : ∀a b,R.rotation.SameCycle a b ↔
      (reversedGraph G).dartVertex a=(reversedGraph G).dartVertex b := by
    intro a b
    simpa only [reversed_dartVertex] using sameCycle_iff_host R a b
  have hs : Function.Surjective (reversedGraph G).dartVertex := by
    intro v
    obtain ⟨a,ha⟩ := hi v
    exact ⟨a,by simpa only [reversed_dartVertex] using ha⟩
  have hf : Fintype.card V+count (subsetBoundary R.rotation Finset.univ)=
      Fintype.card E+2*(reversedGraph G).componentCount Finset.univ := by
    rw [full_boundary_count_face,reversed_componentCount]
    exact he
  have h := hereditary_boundary_euler (reversedGraph G) R.rotation hc hs hf A
  rw [reversed_componentCount] at h
  simpa only [subsetBoundary,boundary_count_selected_face] using h

end PlanarHom.PlanarityLRRealization.RotationRows
