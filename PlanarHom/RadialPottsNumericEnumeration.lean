import PlanarHom.RadialPottsNumericEndpoints
import Mathlib.Data.List.NodupEquivFin

/-! Exact occurrence enumeration for the numeric radial program. Every typed
edge is emitted once, and the edge-position equivalence preserves both ends. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPotts.Numeric
open Complexity Assembly MultiGraph RadialPottsTile
variable {m k : ℕ}

private theorem finRange_values (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem <;> simp

private theorem map_range {B : Type} (n : ℕ) (f : Fin n → B) (g : ℕ → B)
    (h : ∀ i,f i=g i.val) : (List.finRange n).map f=(List.range n).map g := by
  rw [← finRange_values n,List.map_map]
  exact List.map_congr_left (fun i _ => h i)

private theorem flatMap_range {B : Type} (n : ℕ) (f : Fin n → List B) (g : ℕ → List B)
    (h : ∀ i,f i=g i.val) : (List.finRange n).flatMap f=(List.range n).flatMap g := by
  rw [← finRange_values n,List.flatMap_map]
  exact congrArg List.flatten (List.map_congr_left (fun i _ => h i))

 def typedRing (e : Fin m) (r : Fin k) : List (Fin m × Edge k) :=
  (List.finRange 4).flatMap (fun s => (List.finRange (r.val+1)).map (fun a => (e,.inl ⟨r,s,a⟩))) ++
    (List.finRange (4*r.val+2)).flatMap (fun j => [(e,.inr (⟨r,j⟩,false)),(e,.inr (⟨r,j⟩,true))])

 def typedEdges (m k : ℕ) : List (Fin m × Edge k) :=
  (List.finRange m).flatMap (fun e => (List.finRange k).flatMap (typedRing e))

 def typedEntry (rotation : Equiv.Perm (Medial.Dart (Fin m))) (p : Fin m × Edge k) : ℕ × (ℕ × ℕ) :=
  ((vertexIndexEquiv m k ((Assembly.graph rotation k).src p)).val,
   ((vertexIndexEquiv m k ((Assembly.graph rotation k).dst p)).val,if p.2.isLeft then 0 else 1))

 theorem typedRing_map (rotation : Equiv.Perm (Medial.Dart (Fin m))) (e : Fin m) (r : Fin k) :
    (typedRing e r).map (typedEntry rotation)=ringEntries (input rotation k) e.val r.val := by
  simp only [typedRing,List.map_append,List.map_flatMap,List.map_map,List.map_cons,List.map_nil]
  unfold ringEntries
  congr 1
  · apply flatMap_range
    intro s
    apply map_range
    intro a
    exact (longEntry_eq rotation e ⟨r,s,a⟩).symm
  · apply flatMap_range
    intro j
    congr 1
    · exact (shortEntry_eq rotation e ⟨r,j⟩ false).symm
    · exact congrArg List.singleton (shortEntry_eq rotation e ⟨r,j⟩ true).symm

 theorem typedEdges_map (rotation : Equiv.Perm (Medial.Dart (Fin m))) :
    (typedEdges m k).map (typedEntry rotation)=edgeEntries (input rotation k) := by
  simp only [typedEdges,List.map_flatMap]
  unfold edgeEntries input
  apply flatMap_range
  intro e
  apply flatMap_range
  intro r
  exact typedRing_map rotation e r

 theorem mem_typedEdges (p : Fin m × Edge k) : p∈typedEdges m k := by
  rcases p with ⟨e,f | ⟨f,b⟩⟩
  · refine List.mem_flatMap.mpr ⟨e,List.mem_finRange _,List.mem_flatMap.mpr ⟨f.1,List.mem_finRange _,?_⟩⟩
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨f.2.1,List.mem_finRange _,List.mem_map.mpr ⟨f.2.2,List.mem_finRange _,rfl⟩⟩
  · refine List.mem_flatMap.mpr ⟨e,List.mem_finRange _,List.mem_flatMap.mpr ⟨f.1,List.mem_finRange _,?_⟩⟩
    apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨f.2,List.mem_finRange _,?_⟩
    cases b <;> simp

 theorem typedEdges_length (m k : ℕ) : (typedEdges m k).length=Fintype.card (Fin m × Edge k) := by
  have hh := congrArg List.length (typedEdges_map (k:=k) (Equiv.refl (Medial.Dart (Fin m))))
  rw [List.length_map,edgeEntries_length] at hh
  rw [hh,Fintype.card_prod,Fintype.card_fin,RadialPottsTile.card_edge]
  dsimp [input]
  ring

 def edgePositionEquiv (m k : ℕ) : Fin (typedEdges m k).length ≃ (Fin m × Edge k) :=
  Equiv.ofBijective (typedEdges m k).get
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨fun p => List.mem_iff_get.mp (mem_typedEdges p),by
      rw [Fintype.card_fin,typedEdges_length]⟩)
end PlanarHom.RadialPotts.Numeric
