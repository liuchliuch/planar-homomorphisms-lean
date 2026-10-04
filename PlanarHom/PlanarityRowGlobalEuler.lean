import PlanarHom.PlanarityRowPfaffianOrientation
import PlanarHom.PlanarityLRGlobalEuler
import PlanarHom.OccurrenceDegreeRows

/-! NEW extraction of every actual component Euler equality from the global
rotation identity. The universal component inequality was proved from finite
incidence duality; no component Euler certificate is inserted. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRealization FinitePermutationCycles

 theorem componentEdge_nonempty_of_incident (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (hinc : ∀v : Fin g.vertices,∃a : Dart (Fin g.edges.length),((g.toMultiGraph hg).dartPair a).1=v)
    (r : Root g) : Nonempty (ComponentEdge g r.val.val) := by
  obtain ⟨a,ha⟩ := hinc r.val
  refine ⟨⟨a.1,?_⟩⟩
  rw [←original_host_componentRoot g hg a,ha]
  exact componentRoot_eq_self g r.val.isLt r.property

 theorem componentEuler_of_global (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg))
    (hinc : ∀v : Fin g.vertices,∃a : Dart (Fin g.edges.length),((g.toMultiGraph hg).dartPair a).1=v)
    (hglobal : g.vertices+count R.facePerm=g.edges.length+2*(g.toMultiGraph hg).componentCount Finset.univ) :
    ComponentEuler g hg R := by
  let L := fun r : Root g=>Nat.card (ComponentVertex g r.val.val)+count (componentFace g hg r.val.val R)
  let U := fun r : Root g=>Nat.card (ComponentEdge g r.val.val)+2
  have hle : ∀r : Root g,L r≤U r := by
    intro r
    letI := componentEdge_nonempty_of_incident g hg hinc r
    let a : Dart (ComponentEdge g r.val.val) := (Classical.choice inferInstance,true)
    have h := (componentRows g hg r.val.val R).euler_le a (componentGraph_connected g hg r.val r.property)
    simpa only [L,U,Nat.card_eq_fintype_card,count,RotationRows.Face,RotationRows.facePerm,componentFace] using h
  have hsum : (∑r : Root g,L r)=∑r : Root g,U r := by
    simp only [L,U,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul]
    rw [←vertices_eq_sum_components g,←edges_eq_sum_components g hg,←face_count_eq_sum_components g hg R]
    simpa only [globalRowFace,RotationRows.facePerm,componentCount_eq_roots,Nat.mul_comm] using hglobal
  have heq : ∀r : Root g,L r=U r := by
    intro r
    by_contra hn
    have hlt : L r<U r := Nat.lt_of_le_of_ne (hle r) hn
    have hh := Finset.sum_lt_sum (fun s (_ : s∈(Finset.univ : Finset (Root g)))=>hle s)
      ⟨r,Finset.mem_univ _,hlt⟩
    omega
  intro r hr _
  exact heq ⟨r,hr⟩

 theorem incident_of_cubic (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (hcubic : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3) :
    ∀v : Fin g.vertices,∃a : Dart (Fin g.edges.length),((g.toMultiGraph hg).dartPair a).1=v := by
  intro v
  have hp : 0<Fintype.card {a : Dart (Fin g.edges.length) // ((g.toMultiGraph hg).dartPair a).1=v} := by
    have hh := (g.toMultiGraph hg).host_card v
    rw [hcubic] at hh
    convert (show 0 < 3 by omega) using 1
    convert hh using 1 <;> congr <;> exact Subsingleton.elim _ _
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hp
  exact ⟨a.val,a.property⟩

 theorem orientationLog_isPfaffian_of_global_euler (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R)
    (hinc : ∀v : Fin g.vertices,∃a : Dart (Fin g.edges.length),((g.toMultiGraph hg).dartPair a).1=v)
    (hglobal : g.vertices+count R.facePerm=g.edges.length+2*(g.toMultiGraph hg).componentCount Finset.univ) :
    (g.toMultiGraph hg).IsPfaffianOrientation (fun e=>logOrientation (orientationLog g rows) e.val) :=
  orientationLog_isPfaffian g hg rows R hrows (componentEuler_of_global g hg R hinc hglobal)

end PlanarHom.PlanarityRowFaceCode
