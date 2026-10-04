import PlanarHom.PlanarityLRForwardRows

/-! NEW exact outward-back occurrence projection of the actual contour cycle.
The membership/permutation theorem fixes the multiset before its order proof. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints

 def outwardBackFlag (g : MixedCode) (a : Dart (Fin g.edges.length)) : Bool :=
   isBack g a.1.val && decide (a=typedOutward g a.1)

 def contourBackEvents (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (a : Dart (Fin g.edges.length)) : List ℕ :=
   ((contourPortWord (directRotationRows g hg bits) (fun e=>isTree g e.val) a).filter
     (outwardBackFlag g)).map (fun b=>b.1.val)

 def componentBackEvents (g : MixedCode) (bits : List Bool) (root : ℕ) : List ℕ :=
   (backEvents g bits).filter (fun e=>decide (componentRoot g (source g e)=root))

 theorem mem_contourBackEvents (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) (e : ℕ) :
    e∈contourBackEvents g hg bits a ↔
      isBack g e=true ∧ componentRoot g (source g e)=componentRoot g (dartHost g a) := by
  constructor
  · intro he
    obtain ⟨b,hb,hbe⟩:=List.mem_map.mp he
    rcases List.mem_filter.mp hb with ⟨hb,hflag⟩
    have hh : isBack g b.1.val=true ∧ b=typedOutward g b.1 := by
      simpa only [outwardBackFlag,Bool.and_eq_true,decide_eq_true_eq] using hflag
    have hout:=hh.2
    have hc:=(mem_dfsContourPortWord g hg bits a b).mp hb
    rw [hout,dartHost_typedOutward] at hc
    exact ⟨hbe ▸ hh.1,by simpa only [hbe] using hc.1.symm⟩
  · rintro ⟨he,hroot⟩
    let edge : Fin g.edges.length:=⟨e,(of_decide_eq_true he).1⟩
    let b:=typedOutward g edge
    have hb : b∈contourPortWord (directRotationRows g hg bits) (fun e=>isTree g e.val) a := by
      rw [mem_dfsContourPortWord]
      exact ⟨by simpa only [b,dartHost_typedOutward] using hroot.symm,(of_decide_eq_true he).2.1⟩
    refine List.mem_map.mpr ⟨b,List.mem_filter.mpr ⟨hb,?_⟩,rfl⟩
    simp only [outwardBackFlag,b,typedOutward_index,edge,he,decide_true,Bool.true_and]

 theorem contourBackEvents_nodup (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) : (contourBackEvents g hg bits a).Nodup := by
  apply (List.nodup_map_iff_inj_on ((contourPortWord_nodup _ _ _).filter _)).mpr
  intro b hb c hc hbc
  have hb' : b=typedOutward g b.1 := by
    have hh : isBack g b.1.val=true ∧ b=typedOutward g b.1 := by
      simpa only [outwardBackFlag,Bool.and_eq_true,decide_eq_true_eq] using (List.mem_filter.mp hb).2
    exact hh.2
  have hc' : c=typedOutward g c.1 := by
    have hh : isBack g c.1.val=true ∧ c=typedOutward g c.1 := by
      simpa only [outwardBackFlag,Bool.and_eq_true,decide_eq_true_eq] using (List.mem_filter.mp hc).2
    exact hh.2
  have hedge:b.1=c.1:=Fin.ext hbc
  exact hb'.trans ((congrArg (typedOutward g) hedge).trans hc'.symm)

 theorem contourBackEvents_perm (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    (contourBackEvents g hg bits a).Perm (componentBackEvents g bits (componentRoot g (dartHost g a))) := by
  apply (List.perm_ext_iff_of_nodup (contourBackEvents_nodup g hg bits a)
    ((backEvents_nodup g bits).filter _)).mpr
  intro e
  simp only [mem_contourBackEvents,componentBackEvents,List.mem_filter,mem_backEvents,decide_eq_true_eq]

end PlanarHom.PlanarityLRRealization
