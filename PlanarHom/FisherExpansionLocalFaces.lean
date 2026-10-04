import PlanarHom.FisherExpansionFacePaths

/-! NEW vertex-local face paths, valid without excluding other isolated vertices. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable (o : G.IncidenceOrdering)


 def localFirstPort (v : V) (hv : 0<o.degree v) : Fin (o.degree v) := ⟨0,hv⟩

 def localPathTarget (v : V) (hv : 0<o.degree v) (k : Fin (o.degree v+1)) : Fin (o.degree v) :=
  if h : k.val<o.degree v then ⟨k.val,h⟩ else localFirstPort o v hv

 theorem localPathTarget_succ (v : V) (hv : 0<o.degree v) (i : Fin (o.degree v)) :
    localPathTarget o v hv i.succ=portNextIndex i := by
  apply Fin.ext
  by_cases h : i.val+1<o.degree v
  · simp [localPathTarget,portNextIndex,h,Nat.mod_eq_of_lt h]
  · have he : i.val+1=o.degree v := by omega
    simp [localPathTarget,portNextIndex,h,he,localFirstPort]

 theorem local_path_backward_reaches (v : V) (hv : 0<o.degree v) (k : Fin (o.degree v+1)) :
    (expansionRows o).facePerm.SameCycle (expansionPathDart o v k false)
      (expansionPortDart o v (localFirstPort o v hv)) := by
  obtain ⟨k,hk⟩ := k
  induction k with
  | zero =>
      have h₁ := expansion_face_step o (expansionPathDart o v 0 false)
      rw [expansion_face_path_zero] at h₁
      have h₂ := expansion_face_step o (expansionLoopDart o v false true)
      rw [expansion_face_loop_zero] at h₂
      have h₃ := expansion_face_step o (expansionPathDart o v (localFirstPort o v hv).castSucc true)
      rw [expansion_face_path_forward] at h₃
      exact h₁.trans (h₂.trans h₃)
  | succ k ih =>
      let i : Fin (o.degree v) := ⟨k,by omega⟩
      have hs := expansion_face_step o (expansionPathDart o v i.succ false)
      rw [expansion_face_path_backward] at hs
      exact hs.trans (ih (by omega))

 theorem local_loop_reaches (v : V) (hv : 0<o.degree v) (b : Bool) :
    (expansionRows o).facePerm.SameCycle (expansionLoopDart o v b true)
      (expansionPortDart o v (localFirstPort o v hv)) := by
  cases b
  · have h₁ := expansion_face_step o (expansionLoopDart o v false true)
    rw [expansion_face_loop_zero] at h₁
    have h₂ := expansion_face_step o (expansionPathDart o v (localFirstPort o v hv).castSucc true)
    rw [expansion_face_path_forward] at h₂
    exact h₁.trans h₂
  · have h₁ := expansion_face_step o (expansionLoopDart o v true true)
    rw [expansion_face_loop_last] at h₁
    exact h₁.trans (local_path_backward_reaches o v hv _)

 theorem local_path_forward_reaches (v : V) (hv : 0<o.degree v) (k : Fin (o.degree v+1)) :
    (expansionRows o).facePerm.SameCycle (expansionPathDart o v k true)
      (expansionPortDart o v (localPathTarget o v hv k)) := by
  by_cases hk : k.val<o.degree v
  · let i : Fin (o.degree v) := ⟨k.val,hk⟩
    have hi : i.castSucc=k := Fin.ext rfl
    have hs := expansion_face_step o (expansionPathDart o v i.castSucc true)
    rw [expansion_face_path_forward,hi] at hs
    simpa only [localPathTarget,dif_pos hk] using hs
  · have he : k=Fin.last (o.degree v) := Fin.ext (by change k.val=o.degree v; have := k.isLt; omega)
    have hs := expansion_face_step o (expansionPathDart o v k true)
    rw [he,expansion_face_path_last] at hs
    have hh := hs.trans (local_loop_reaches o v hv true)
    simpa [localPathTarget,he] using hh

 theorem local_old_step_lifts (a : Dart E) :
    (expansionRows o).facePerm.SameCycle (expansionExternalDart o a)
      (expansionExternalDart o (o.rotationRows.facePerm a)) := by
  obtain ⟨⟨v,i⟩,rfl⟩ := o.darts.surjective a
  have hs := expansion_face_step o (expansionExternalDart o (o.darts ⟨v,i⟩))
  rw [expansionExternalDart_endpoint,expansion_face_port] at hs
  have hv : 0<o.degree v := Nat.zero_lt_of_lt i.isLt
  have ht := local_path_forward_reaches o v hv i.succ
  rw [localPathTarget_succ,expansionPortDart_external,←original_face_endpoint] at ht
  simpa only [←expansionExternalDart_endpoint] using hs.trans ht

end PlanarHom.Fisher
