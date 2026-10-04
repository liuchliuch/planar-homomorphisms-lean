import PlanarHom.OccurrenceMatchingWalk

/-! NEW finite extraction of a vertex-simple even alternating orbit.
The proof uses the first repeated vertex and exact matching-port uniqueness. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph.PerfectMatching
open Kasteleyn
variable {V E : Type*} [Finite V] {G : MultiGraph V E} {M N : Finset E}
variable (hM : G.PerfectMatching M) (hN : G.PerfectMatching N)

theorem exists_simple_even_walk (v : V) :
    ∃n,2≤n ∧ Even n ∧ hM.walkState hN v n=(v,true) ∧
      Function.Injective (fun i:Fin n=>hM.walkVertex hN v i.val) := by
  let P:=hM.stepPerm hN
  let s:V×Bool:=(v,true)
  have hex : ∃n,0<n ∧ ∃i,i<n ∧ hM.walkVertex hN v n=hM.walkVertex hN v i := by
    let n:=Function.minimalPeriod P s
    have hp:0<n:=Function.minimalPeriod_pos_of_mem_periodicPts (P.injective.mem_periodicPts s)
    refine ⟨n,hp,0,hp,?_⟩
    exact congrArg Prod.fst (Function.isPeriodicPt_minimalPeriod P s)
  let n:=Nat.find hex
  obtain ⟨hn,i,hi,he⟩:=Nat.find_spec hex
  change 0<n at hn
  change i<n at hi
  change hM.walkVertex hN v n=hM.walkVertex hN v i at he
  have hprefix : ∀j k,j<n→k<n→hM.walkVertex hN v j=hM.walkVertex hN v k→j=k := by
    intro j k hj hk hjk
    rcases lt_trichotomy j k with h | h | h
    · have hh:=Nat.find_min' hex ⟨by omega,j,h,hjk.symm⟩
      change n≤k at hh
      omega
    · exact h
    · have hh:=Nat.find_min' hex ⟨by omega,k,h,hjk⟩
      change n≤j at hh
      omega
  have hi1 : i+1<n := by
    by_contra h
    have heq:i+1=n:=by omega
    have hh:=hM.walkVertex_succ_ne hN v i
    rw [heq] at hh
    exact hh he
  let t:=n-1
  have ht:t<n:=by omega
  have htn:t+1=n:=by omega
  have hneColor : (hM.walkState hN v i).2≠(hM.walkState hN v t).2 := by
    intro hc
    have hv : (hM.stepPerm hN (hM.walkState hN v t)).1=(hM.walkState hN v i).1 := by
      rw [←walkState_succ,htn]
      exact he
    have hd:=hM.stepPort_backtrack hN (hM.walkState hN v i) (hM.walkState hN v t) hc hv
    change hM.walkDart hN v i=((hM.walkDart hN v t).1,!(hM.walkDart hN v t).2) at hd
    have hend:=congrArg (fun a:Dart E=>(G.dartPair a).2) hd
    dsimp only at hend
    rw [walkDart_head,dartPair_reverse_snd,walkDart_host] at hend
    have hit:=hprefix (i+1) t hi1 ht hend
    have hflip : (hM.walkState hN v t).2= !(hM.walkState hN v i).2 := by
      rw [←hit,walkState_succ,step_color]
    have hh:=hc.trans hflip
    cases hb:(hM.walkState hN v i).2 <;> simp [hb] at hh
  have hcolor : (hM.walkState hN v n).2=(hM.walkState hN v i).2 := by
    have hh : (hM.walkState hN v n).2= !(hM.walkState hN v t).2 := by
      rw [←htn,walkState_succ,step_color]
    rw [hh]
    cases hb:(hM.walkState hN v i).2 <;> cases hc:(hM.walkState hN v t).2 <;> simp_all
  have hstate : hM.walkState hN v n=hM.walkState hN v i := Prod.ext he hcolor
  have hreturn : hM.walkState hN v (n-i)=(v,true) := by
    apply P.injective.iterate i
    change P^[i] (P^[n-i] s)=P^[i] s
    rw [←Function.iterate_add_apply,Nat.add_sub_of_le hi.le]
    exact hstate
  have hsmall:=Nat.find_min' hex ⟨by omega,0,by omega,congrArg Prod.fst hreturn⟩
  change n≤n-i at hsmall
  have hi0:i=0:=by omega
  rw [hi0,walkState_zero] at hstate
  have heven:Even n := by
    have hc:=congrArg Prod.snd hstate
    rw [walkState_color] at hc
    exact Nat.even_iff.mpr (of_decide_eq_true hc)
  refine ⟨n,by omega,heven,hstate,?_⟩
  intro a b hab
  exact Fin.ext (hprefix a.val b.val a.isLt b.isLt hab)

end PlanarHom.MultiGraph.PerfectMatching
