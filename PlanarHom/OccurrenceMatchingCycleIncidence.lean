import PlanarHom.OccurrenceMatchingCycleDegrees

/-! NEW exact two-port incidence of the literal simple occurrence cycle. -/
noncomputable section
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} {G : MultiGraph V E}

theorem cycleNext_injective (n : ℕ) (hn : 2≤n) : Function.Injective (cycleNext n hn) := by
  intro i j h
  rw [cycleNext_eq_finRotate,cycleNext_eq_finRotate] at h
  exact (finRotate n).injective h

theorem cycleNext_ne (n : ℕ) (hn : 2≤n) (i : Fin n) : cycleNext n hn i≠i := by
  intro hh
  have he:=congrArg Fin.val hh
  change (i.val+1)%n=i.val at he
  by_cases hi : i.val+1<n
  · rw [Nat.mod_eq_of_lt hi] at he
    omega
  · have hi' : i.val+1=n := by omega
    rw [hi',Nat.mod_self] at he
    omega

theorem dartPair_reverse_fst (a : Dart E) : (G.dartPair (a.1,!a.2)).1=(G.dartPair a).2 := by
  rcases a with ⟨e,b⟩
  cases b <;> rfl

theorem dart_eq_or_reverse_of_fst (a b : Dart E) (he : a.1=b.1) : a=b ∨ a=(b.1,!b.2) := by
  rcases a with ⟨e,x⟩
  rcases b with ⟨f,y⟩
  dsimp at he
  subst f
  cases x <;> cases y <;> simp

namespace DirectedSimpleCycle

theorem incident_at_next (c : DirectedSimpleCycle G) (i : Fin c.length) (a : Dart E)
    (ha : a.1∈c.cycleEdges) (hh : (G.dartPair a).1=c.vertex (cycleNext c.length c.length_ge_two i)) :
    a=((c.dart i).1,!(c.dart i).2) ∨ a=c.dart (cycleNext c.length c.length_ge_two i) := by
  classical
  obtain ⟨j,_,hj⟩:=Finset.mem_image.mp ha
  rcases dart_eq_or_reverse_of_fst a (c.dart j) hj.symm with he | he
  · rw [he,c.tail_eq] at hh
    have hji:=c.vertex_injective hh
    exact Or.inr (by simpa only [hji] using he)
  · rw [he,dartPair_reverse_fst,c.head_eq] at hh
    have hji:=cycleNext_injective c.length c.length_ge_two (c.vertex_injective hh)
    exact Or.inl (by simpa only [hji] using he)

theorem incident_at_next_iff (c : DirectedSimpleCycle G) (i : Fin c.length) (a : Dart E) :
    (a.1∈c.cycleEdges ∧ (G.dartPair a).1=c.vertex (cycleNext c.length c.length_ge_two i)) ↔
      a=((c.dart i).1,!(c.dart i).2) ∨ a=c.dart (cycleNext c.length c.length_ge_two i) := by
  classical
  constructor
  · exact fun h=>c.incident_at_next i a h.1 h.2
  · intro h
    rcases h with rfl | rfl
    · exact ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,by rw [dartPair_reverse_fst,c.head_eq]⟩
    · exact ⟨Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,c.tail_eq _⟩

theorem incident_ports_ne (c : DirectedSimpleCycle G) (i : Fin c.length) :
    ((c.dart i).1,!(c.dart i).2)≠c.dart (cycleNext c.length c.length_ge_two i) := by
  intro hh
  have he := congrArg (fun a:Dart E=>a.1) hh
  have hi:=c.edge_injective he
  exact cycleNext_ne c.length c.length_ge_two i hi.symm

theorem edge_nonloop (c : DirectedSimpleCycle G) (i : Fin c.length) : G.src (c.dart i).1≠G.dst (c.dart i).1 := by
  intro he
  have hh : (G.dartPair (c.dart i)).1=(G.dartPair (c.dart i)).2 := by
    cases h:(c.dart i).2 <;> simp [dartPair,h,he]
  rw [c.tail_eq,c.head_eq] at hh
  exact cycleNext_ne c.length c.length_ge_two i (c.vertex_injective hh).symm

end DirectedSimpleCycle
end PlanarHom.MultiGraph
