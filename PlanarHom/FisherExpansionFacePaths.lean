import PlanarHom.FisherExpansionFaces
import PlanarHom.FinitePermutationArrowSubdivision

/-! NEW actual finite face paths through every added path/loop dart. These
paths identify the old face cycles after erasing the added markers. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable (o : G.IncidenceOrdering)

 def expansionExternalDart (a : Dart E) : Dart (ExpansionEdge o) := (.inl a.1,a.2)
 def originalPortDart (v : V) (i : Fin (o.degree v)) : Dart E := reversePerm E (o.darts ⟨v,i⟩)

@[simp] theorem expansionPortDart_external (v : V) (i : Fin (o.degree v)) :
    expansionPortDart o v i=expansionExternalDart o (originalPortDart o v i) := rfl

 theorem expansionExternalDart_endpoint (v : V) (i : Fin (o.degree v)) :
    expansionExternalDart o (o.darts ⟨v,i⟩)=reversePerm _ (expansionPortDart o v i) := by
  simp [expansionExternalDart,expansionPortDart,reversePerm]

 def portNextIndex {d : ℕ} (i : Fin d) : Fin d := ⟨(i.val+1)%d,Nat.mod_lt _ (by have := i.isLt; omega)⟩

 theorem original_port_rotation (v : V) (i : Fin (o.degree v)) :
    o.rotationRows.rotation (originalPortDart o v i)=originalPortDart o v (portNextIndex i) := by
  have hh : (G.dartPair (originalPortDart o v i)).1=v :=
    (o.mem_cyclicRow v _).mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
  rw [RotationRows.rotation_apply,hh]
  have h := List.formPerm_apply_getElem (o.cyclicRow v) (o.cyclicRow_nodup v) i.val (by simpa [IncidenceOrdering.cyclicRow] using i.isLt)
  simpa only [IncidenceOrdering.rotationRows,IncidenceOrdering.cyclicRow,List.length_ofFn,List.getElem_ofFn,
    originalPortDart,portNextIndex,Fin.eta] using h

 theorem original_face_endpoint (v : V) (i : Fin (o.degree v)) :
    o.rotationRows.facePerm (o.darts ⟨v,i⟩)=originalPortDart o v (portNextIndex i) :=
  original_port_rotation o v i

 theorem expansion_face_step (d : Dart (ExpansionEdge o)) :
    (expansionRows o).facePerm.SameCycle d ((expansionRows o).facePerm d) :=
  Equiv.Perm.SameCycle.rfl.apply_right

variable (hpos : ∀v,0<o.degree v)

 def firstPort (v : V) : Fin (o.degree v) := ⟨0,hpos v⟩

 def expansionPathTarget (v : V) (k : Fin (o.degree v+1)) : Fin (o.degree v) :=
  if h : k.val<o.degree v then ⟨k.val,h⟩ else firstPort o hpos v

 theorem expansionPathTarget_succ (v : V) (i : Fin (o.degree v)) :
    expansionPathTarget o hpos v i.succ=portNextIndex i := by
  apply Fin.ext
  by_cases h : i.val+1<o.degree v
  · simp [expansionPathTarget,portNextIndex,h,Nat.mod_eq_of_lt h]
  · have he : i.val+1=o.degree v := by omega
    simp [expansionPathTarget,portNextIndex,h,he,firstPort]

 theorem expansion_path_backward_reaches (v : V) (k : Fin (o.degree v+1)) :
    (expansionRows o).facePerm.SameCycle (expansionPathDart o v k false)
      (expansionPortDart o v (firstPort o hpos v)) := by
  obtain ⟨k,hk⟩ := k
  induction k with
  | zero =>
      have h₁ := expansion_face_step o (expansionPathDart o v 0 false)
      rw [expansion_face_path_zero] at h₁
      have h₂ := expansion_face_step o (expansionLoopDart o v false true)
      rw [expansion_face_loop_zero] at h₂
      have h₃ := expansion_face_step o (expansionPathDart o v (firstPort o hpos v).castSucc true)
      rw [expansion_face_path_forward] at h₃
      exact h₁.trans (h₂.trans h₃)
  | succ k ih =>
      let i : Fin (o.degree v) := ⟨k,by omega⟩
      have hs := expansion_face_step o (expansionPathDart o v i.succ false)
      rw [expansion_face_path_backward] at hs
      exact hs.trans (ih (by omega))

 theorem expansion_loop_reaches (v : V) (b : Bool) :
    (expansionRows o).facePerm.SameCycle (expansionLoopDart o v b true)
      (expansionPortDart o v (firstPort o hpos v)) := by
  cases b
  · have h₁ := expansion_face_step o (expansionLoopDart o v false true)
    rw [expansion_face_loop_zero] at h₁
    have h₂ := expansion_face_step o (expansionPathDart o v (firstPort o hpos v).castSucc true)
    rw [expansion_face_path_forward] at h₂
    exact h₁.trans h₂
  · have h₁ := expansion_face_step o (expansionLoopDart o v true true)
    rw [expansion_face_loop_last] at h₁
    exact h₁.trans (expansion_path_backward_reaches o hpos v _)

 theorem expansion_path_forward_reaches (v : V) (k : Fin (o.degree v+1)) :
    (expansionRows o).facePerm.SameCycle (expansionPathDart o v k true)
      (expansionPortDart o v (expansionPathTarget o hpos v k)) := by
  by_cases hk : k.val<o.degree v
  · let i : Fin (o.degree v) := ⟨k.val,hk⟩
    have hi : i.castSucc=k := Fin.ext rfl
    have hs := expansion_face_step o (expansionPathDart o v i.castSucc true)
    rw [expansion_face_path_forward,hi] at hs
    simpa only [expansionPathTarget,dif_pos hk] using hs
  · have he : k=Fin.last (o.degree v) := Fin.ext (by change k.val=o.degree v; have := k.isLt; omega)
    have hs := expansion_face_step o (expansionPathDart o v k true)
    rw [he,expansion_face_path_last] at hs
    have hh := hs.trans (expansion_loop_reaches o hpos v true)
    simpa [expansionPathTarget,he] using hh

 include hpos in
 theorem expansion_old_step_lifts (a : Dart E) :
    (expansionRows o).facePerm.SameCycle (expansionExternalDart o a)
      (expansionExternalDart o (o.rotationRows.facePerm a)) := by
  obtain ⟨⟨v,i⟩,rfl⟩ := o.darts.surjective a
  have hs := expansion_face_step o (expansionExternalDart o (o.darts ⟨v,i⟩))
  rw [expansionExternalDart_endpoint,expansion_face_port] at hs
  have ht := expansion_path_forward_reaches o hpos v i.succ
  rw [expansionPathTarget_succ,expansionPortDart_external,←original_face_endpoint] at ht
  simpa only [←expansionExternalDart_endpoint] using hs.trans ht

end PlanarHom.Fisher
