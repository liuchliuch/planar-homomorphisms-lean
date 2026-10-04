import PlanarHom.IndexedRotationRows
import PlanarHom.FinitePermutationCyclicEmbedding

/-! NEW exact transfer of a hosted numeric gap word to the typed incoming
face markers used by shared-vertex splicing. -/
noncomputable section
open Classical
namespace PlanarHom.IndexedRotationCertificate
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles RadialPotts.Assembly
variable {n m : ℕ} (host : Fin (2*m)→Fin n) (P : Equiv.Perm (Fin (2*m)))
variable (C : LabelCertificate (P*flip m) (Fin n)) (hc : C.label=host)

 theorem rows_cyclic_markers (gs : List (Fin (2*m))) (h : CyclicSublist P (gs.map P.symm)) :
    CyclicSublist (rows host P C hc).facePerm (gs.map (fun q=>reversePerm (Fin m) (closingDart P q))) := by
  have hs : ∀q,(rows host P C hc).facePerm ((faceIndex m).symm q)=(faceIndex m).symm (P q) := by
    intro q
    apply (faceIndex m).injective
    rw [rows_face_step,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  have hh:=CyclicSublist.map_embedding P (rows host P C hc).facePerm (faceIndex m).symm (faceIndex m).symm.injective hs h
  have hm (q : Fin (2*m)) : (faceIndex m).symm (P.symm q)=reversePerm (Fin m) (closingDart P q) := by
    apply (faceIndex m).injective
    rw [Equiv.apply_symm_apply,closing_marker_index]
  simpa only [List.map_map,Function.comp_apply,hm] using hh

end PlanarHom.IndexedRotationCertificate
