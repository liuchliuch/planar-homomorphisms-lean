import PlanarHom.SurfaceFaceRepresentatives
import PlanarHom.SurfaceRootedBoundaryPartition

/-! NEW actual root-face/isolated-boundary selection: exactly one chosen
boundary in each ordinary graph component, with all remaining boundaries the
literal densely enumerated disk list of the compiler. -/
noncomputable section
open Classical
namespace PlanarHom.SurfacePlanarCompiler
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PlanarityLRDirect
open SurfaceRibbonComplement PlanarityRowFaceCode
variable (g : MixedCode) {bt ut : ℕ} (hg:g.Valid bt ut) (rs : Rows)
variable (R : RotationRows (g.toMultiGraph hg)) (hrs:Realizes g hg rs R)

 theorem representative_component_eq_iff (a b:FaceRep g rs) :
    faceComponent R (representativeFace g hg rs R a)=faceComponent R (representativeFace g hg rs R b) ↔
    componentRoot g (PlanarityRotationCode.host g a.val)=componentRoot g (PlanarityRotationCode.host g b.val) := by
  change (Quotient.mk _ ((g.toMultiGraph hg).dartPair (liftDart a.val _)).1:
      (g.toMultiGraph hg).Components Finset.univ)=
    Quotient.mk _ ((g.toMultiGraph hg).dartPair (liftDart b.val _)).1 ↔ _
  rw [Quotient.eq,component_iff_vertexRoot g hg,root_eq_iff,vertexRoot_val,vertexRoot_val]
  rw [←eraseDart_host g hg,←eraseDart_host g hg,erase_liftDart,erase_liftDart]

 def IsRootBoundary : Boundary R→Prop
  | .inl f=>rootRepresentative g rs (faceRepresentative g hg rs R hrs f).val=
      (faceRepresentative g hg rs R hrs f).val
  | .inr _=>True

 theorem isolated_component_eq (v:Isolated (G:=g.toMultiGraph hg)) (w:Fin g.vertices)
    (h:vertexComponent (G:=g.toMultiGraph hg) v.val=vertexComponent w) : w=v.val :=
  (g.toMultiGraph hg).eq_of_connected_degree_zero v.val
    ((SurfaceRawEmbedding.isolated_iff_degree_zero g hg v.val).mp v.property) (Quotient.exact h)

 theorem face_component_ne_isolated (f:R.Face) (v:Isolated (G:=g.toMultiGraph hg)) :
    faceComponent R f≠vertexComponent (G:=g.toMultiGraph hg) v.val := by
  intro h
  induction f using Quotient.inductionOn with | h a=>
    have hh:=isolated_component_eq g hg v ((g.toMultiGraph hg).dartPair a).1 h.symm
    exact v.property a hh

 theorem boundary_component_surjective : Function.Surjective (boundaryComponent R) := by
  intro c
  induction c using Quotient.inductionOn with | h v=>
    by_cases hv:∃a:Dart (Fin g.edges.length),((g.toMultiGraph hg).dartPair a).1=v
    · obtain ⟨a,ha⟩:=hv
      refine ⟨.inl (R.faceOf a),?_⟩
      change vertexComponent ((g.toMultiGraph hg).dartPair a).1=vertexComponent v
      rw [ha]
    · refine ⟨.inr ⟨v,?_⟩,rfl⟩
      intro a ha
      exact hv ⟨a,ha⟩

 theorem exists_root_same_component (b:Boundary R) :
    ∃a:Boundary R,boundaryComponent R a=boundaryComponent R b ∧ IsRootBoundary g hg rs R hrs a := by
  cases b with
  | inr v=>exact ⟨.inr v,rfl,True.intro⟩
  | inl f=>
    let a:=faceRepresentative g hg rs R hrs f
    let r:FaceRep g rs:=⟨rootRepresentative g rs a.val,rootRepresentative_mem g rs a.property⟩
    refine ⟨.inl (representativeFace g hg rs R r),?_,?_⟩
    · change faceComponent R (representativeFace g hg rs R r)=faceComponent R f
      rw [←representativeFace_left g hg rs R hrs f]
      apply (representative_component_eq_iff g hg rs R r a).mpr
      exact rootRepresentative_component g rs a.property
    · change rootRepresentative g rs (faceRepresentative g hg rs R hrs (representativeFace g hg rs R r)).val=
        (faceRepresentative g hg rs R hrs (representativeFace g hg rs R r)).val
      rw [representativeFace_right]
      exact rootRepresentative_idempotent g rs a.property

 theorem root_unique (a b:Boundary R) (ha:IsRootBoundary g hg rs R hrs a)
    (hb:IsRootBoundary g hg rs R hrs b) (hc:boundaryComponent R a=boundaryComponent R b) : a=b := by
  cases a with
  | inl f=>
    cases b with
    | inr v=>exact (face_component_ne_isolated g hg R f v hc).elim
    | inl h=>
      have hc':componentRoot g (PlanarityRotationCode.host g (faceRepresentative g hg rs R hrs f).val)=
          componentRoot g (PlanarityRotationCode.host g (faceRepresentative g hg rs R hrs h).val) := by
        apply (representative_component_eq_iff g hg rs R _ _).mp
        simpa only [representativeFace_left] using hc
      have he:=rootRepresentative_unique g rs (faceRepresentative g hg rs R hrs f).property ha hb hc'
      congr 1
      apply (faceRepEquiv g hg rs R hrs).injective
      exact Subtype.ext he
  | inr v=>
    cases b with
    | inl f=>exact (face_component_ne_isolated g hg R f v hc.symm).elim
    | inr w=>
      congr 1
      apply Subtype.ext
      exact (isolated_component_eq g hg v w.val hc).symm

 theorem exists_chosenRoot (c:Component (G:=g.toMultiGraph hg)) :
    ∃a:Boundary R,boundaryComponent R a=c ∧ IsRootBoundary g hg rs R hrs a := by
  obtain ⟨b,hb⟩:=boundary_component_surjective g hg R c
  obtain ⟨a,ha,hr⟩:=exists_root_same_component g hg rs R hrs b
  exact ⟨a,ha.trans hb,hr⟩

 def chosenRoot (c:Component (G:=g.toMultiGraph hg)) : Boundary R :=
  Classical.choose (exists_chosenRoot g hg rs R hrs c)

 theorem chosenRoot_spec (c:Component (G:=g.toMultiGraph hg)) :
    boundaryComponent R (chosenRoot g hg rs R hrs c)=c ∧ IsRootBoundary g hg rs R hrs (chosenRoot g hg rs R hrs c) :=
  Classical.choose_spec (exists_chosenRoot g hg rs R hrs c)

 theorem isRoot_iff_chosen (b:Boundary R) : IsRootBoundary g hg rs R hrs b ↔
    b=chosenRoot g hg rs R hrs (boundaryComponent R b) := by
  constructor
  · intro hb
    exact root_unique g hg rs R hrs b _ hb (chosenRoot_spec g hg rs R hrs _).2
      (chosenRoot_spec g hg rs R hrs _).1.symm
  · intro h
    rw [h]
    exact (chosenRoot_spec g hg rs R hrs _).2

 theorem mem_typedDisks (b:Boundary R) : b∈typedDisks g hg rs R ↔ ¬IsRootBoundary g hg rs R hrs b := by
  cases b with
  | inr v=>simp [typedDisks,IsRootBoundary]
  | inl f=>
    constructor
    · intro h hf
      obtain ⟨a,ha,he⟩:=List.mem_map.mp h
      have he':representativeFace g hg rs R ⟨a.val,(List.mem_filter.mp a.property).1⟩=f:=Sum.inl.inj he
      have hh:=congrArg (faceRepresentative g hg rs R hrs) he'
      rw [representativeFace_right] at hh
      have hne:=of_decide_eq_true (List.mem_filter.mp a.property).2
      change rootRepresentative g rs (faceRepresentative g hg rs R hrs f).val=
        (faceRepresentative g hg rs R hrs f).val at hf
      rw [←hh] at hf
      exact hne hf
    · intro hf
      let a:=faceRepresentative g hg rs R hrs f
      have hm:a.val∈disks g rs := by simp only [disks,List.mem_filter,decide_eq_true_eq]; exact ⟨a.property,hf⟩
      apply List.mem_map.mpr
      exact ⟨⟨a.val,hm⟩,List.mem_attach _ _,congrArg Sum.inl (representativeFace_left g hg rs R hrs f)⟩

 def rootedPartition : SurfaceRootedBoundaryPartition.Data (boundaryComponent R) where
  root:=chosenRoot g hg rs R hrs
  root_component c:=(chosenRoot_spec g hg rs R hrs c).1
  disks:=typedDisks g hg rs R
  nodup:=typedDisks_nodup g hg rs R hrs
  mem_disks b:=by rw [mem_typedDisks,isRoot_iff_chosen]

end PlanarHom.SurfacePlanarCompiler
