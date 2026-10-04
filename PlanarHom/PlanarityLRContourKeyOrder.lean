import PlanarHom.PlanarityLRContourKeySteps

/-! NEW strict contour-key increase except for the actual root-row wrap. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityRotationCode
open PlanarityLRRealization
local instance contourKeyOrderDartBEq : BEq Dart := instBEqOfDecidableEq

 theorem contourKey_port_step (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) (ht : isTree g a.1=false) :
    contourKey g bits a<contourKey g bits (rawContourStep g bits a) ∨
      RootFirst g bits (rawContourStep g bits a) := by
  have hstep:rawContourStep g bits a=directRotation g bits a:=by simp [rawContourStep,ht]
  rw [hstep]
  have hv:=host_valid g hg ha
  have hr:=localRank_lt g hg bits hv ha rfl
  have hrot:=localRank_directRotation g hg bits ha
  have hhost:=directRotation_host_raw g hg bits ha
  by_cases hlt:localRank g bits (host g a) a+1<(visitRow g bits (host g a)).length
  · left
    rw [Nat.mod_eq_of_lt hlt] at hrot
    unfold contourKey
    rw [hhost,hrot]
    exact List.Lex.append_left (·<·) (List.Lex.rel (Nat.lt_succ_self _)) _
  · have heq:localRank g bits (host g a) a+1=(visitRow g bits (host g a)).length:=by omega
    have hz:height g (host g a)=0 := by
      by_contra hn
      have hp:0<height g (host g a):=by omega
      have he:=localRank_last_eq_parent g hg bits hv hp
        ((mem_visitRow g hg bits hv a).mpr ⟨ha,rfl⟩) heq
      have hh:isTree g a.1=true := by
        rw [he]
        exact (parentEdge_tree g hg hv hp).1
      rw [ht] at hh
      contradiction
    exact Or.inr (rootFirst_of_rotation_wrap g hg bits ha hz heq)

 theorem contourKey_reverse_tree_step (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e : ℕ} (he : isTree g e=true) :
    contourKey g bits (reverse (outward g e))<
      contourKey g bits (rawContourStep g bits (reverse (outward g e))) ∨
      RootFirst g bits (rawContourStep g bits (reverse (outward g e))) := by
  have ha:e<g.edges.length:=(of_decide_eq_true he).1
  have hv:=(source_target_valid g hg ha).1
  have hstep:rawContourStep g bits (reverse (outward g e))=directRotation g bits (outward g e) := by
    simp [rawContourStep,he]
  rw [hstep]
  have hr:=localRank_lt g hg bits hv (a := outward g e) ha (host_outward g e)
  have hrot:=localRank_directRotation g hg bits (a := outward g e) ha
  simp only [host_outward] at hrot
  have hhost:=directRotation_host_raw g hg bits (a := outward g e) ha
  rw [host_outward] at hhost
  by_cases hlt:localRank g bits (source g e) (outward g e)+1<(visitRow g bits (source g e)).length
  · left
    rw [Nat.mod_eq_of_lt hlt] at hrot
    unfold contourKey
    rw [host_reverse_outward,hhost,visitTreeWord_tree_target g hg bits he,hrot]
    rw [List.append_assoc]
    exact List.Lex.append_left (·<·) (List.Lex.rel (Nat.lt_succ_self _)) _
  · have heq:localRank g bits (source g e) (outward g e)+1=(visitRow g bits (source g e)).length:=by omega
    have hz:height g (source g e)=0 := by
      have hh:=rotation_wrap_root g hg bits (a := outward g e) ha
        (outward_ne_reversed g e (parentEdge g (host g (outward g e)))) (by simpa only [host_outward] using heq)
      simpa only [host_outward] using hh
    exact Or.inr (rootFirst_of_rotation_wrap g hg bits (a := outward g e) ha
      (by simpa only [host_outward] using hz) (by simpa only [host_outward] using heq))

 theorem contourKey_step (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) :
    contourKey g bits a<contourKey g bits (rawContourStep g bits a) ∨
      RootFirst g bits (rawContourStep g bits a) := by
  cases ht:isTree g a.1
  · exact contourKey_port_step g hg bits ha ht
  · rcases dart_outward_cases g a with h | h
    · exact Or.inl (by simpa only [← h] using contourKey_outward_tree_lt g hg bits ht)
    · simpa only [← h] using contourKey_reverse_tree_step g hg bits ht

 theorem rootFirst_unique (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a b : Dart} (ha : a.1<g.edges.length) (hb : b.1<g.edges.length)
    (hfa : RootFirst g bits a) (hfb : RootFirst g bits b)
    (hr : componentRoot g (host g a)=componentRoot g (host g b)) : a=b := by
  have hhost:host g a=host g b := by
    simpa only [componentRoot_eq_self g (host_valid g hg ha) hfa.1,
      componentRoot_eq_self g (host_valid g hg hb) hfb.1] using hr
  exact Option.some.inj (hfa.2.symm.trans (by simpa only [hhost] using hfb.2))

end PlanarHom.PlanarityLRDirect
