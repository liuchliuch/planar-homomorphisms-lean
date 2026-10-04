import PlanarHom.RadialPottsNumericEnumeration
import PlanarHom.PottsMarkedCode
import PlanarHom.RadialPottsAssemblyDegrees

/-! Actual numeric radial-code validity and occurrence incidence equivalence.
The serializer does not omit vertices, identify parallel occurrences, or supply
an embedding promise. Planarity is transported from a genuine typed drawing. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPotts.Numeric
open Complexity Assembly MultiGraph RadialPottsTile PottsCentered
variable {m k : ℕ}

 theorem output_valid (rotation : Equiv.Perm (Medial.Dart (Fin m))) :
    (output (input rotation k)).Valid 2 0 := by
  constructor
  · intro z hz
    change z∈edgeEntries (input rotation k) at hz
    rw [← typedEdges_map] at hz
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hz
    refine ⟨(vertexIndexEquiv m k ((Assembly.graph rotation k).src p)).isLt,
      (vertexIndexEquiv m k ((Assembly.graph rotation k).dst p)).isLt,?_⟩
    simp only [typedEntry]
    split_ifs <;> decide
  · simp [output]

 theorem output_edges_length (rotation : Equiv.Perm (Medial.Dart (Fin m))) :
    (output (input rotation k)).edges.length=(typedEdges m k).length := by
  have h := congrArg List.length (typedEdges_map (k:=k) rotation)
  simpa only [List.length_map,output] using h.symm

 def edgeEquiv (rotation : Equiv.Perm (Medial.Dart (Fin m))) :
    Fin (output (input rotation k)).edges.length ≃ (Fin m × Edge k) :=
  (finCongr (output_edges_length rotation)).trans (edgePositionEquiv m k)

 theorem output_get (rotation : Equiv.Perm (Medial.Dart (Fin m)))
    (i : Fin (output (input rotation k)).edges.length) :
    (output (input rotation k)).edges.get i=typedEntry rotation (edgeEquiv rotation i) := by
  have hi : i.val<(typedEdges m k).length := by rw [← output_edges_length rotation]; exact i.isLt
  have h := congrArg (fun l : List (ℕ×(ℕ×ℕ)) => l[i.val]?) (typedEdges_map (k:=k) rotation)
  dsimp only at h
  rw [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem (by exact i.isLt)] at h
  exact Option.some.inj h.symm

 def incidenceEquiv (rotation : Equiv.Perm (Medial.Dart (Fin m))) :
    ((output (input rotation k)).toMultiGraph (output_valid rotation)).IncidenceEquiv (Assembly.graph rotation k) where
  vertex := (vertexIndexEquiv m k).symm
  edge := edgeEquiv rotation
  src_eq i := by
    apply (Equiv.eq_symm_apply (vertexIndexEquiv m k)).mpr
    apply Fin.ext
    exact (congrArg Prod.fst (output_get rotation i)).symm
  dst_eq i := by
    apply (Equiv.eq_symm_apply (vertexIndexEquiv m k)).mpr
    apply Fin.ext
    exact (congrArg (fun p : ℕ×(ℕ×ℕ) => p.2.1) (output_get rotation i)).symm

 theorem output_planar (rotation : Equiv.Perm (Medial.Dart (Fin m)))
    (hp : (Assembly.graph rotation k).Planar) : (output (input rotation k)).PlanarValid 2 0 := by
  apply ((output (input rotation k)).planarValid_iff (output_valid rotation)).mpr
  exact (incidenceEquiv rotation).planar_iff.mpr hp

 theorem longPositions_iff (rotation : Equiv.Perm (Medial.Dart (Fin m)))
    (i : Fin (output (input rotation k)).edges.length) :
    i∈longPositions (output (input rotation k)) ↔ edgeEquiv rotation i∈longEdges (Fin m) k := by
  simp only [longPositions,Finset.mem_filter,Finset.mem_univ,true_and,output_get,typedEntry]
  rcases h : edgeEquiv rotation i with ⟨e,f | f⟩ <;> simp [longEdges,longEdgeMap]
end PlanarHom.RadialPotts.Numeric
