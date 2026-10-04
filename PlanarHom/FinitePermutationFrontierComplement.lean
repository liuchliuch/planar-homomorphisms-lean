import PlanarHom.FinitePermutationCyclicFrontier
import PlanarHom.FinitePermutationSublistBoundaryArcs

/-! NEW actual exterior arc after deleting an input block from a cyclic
frontier. The length and all marker-avoidance facts are derived from word ranks. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords
variable {A:Type} [Fintype A]

 theorem orbitPrefix_drop (P:A→A) (a:A) (N k:ℕ) (hk:k≤N) :
    (orbitPrefix P N a).drop k=orbitPrefix P (N-k) (P^[k] a) := by
  have hh:=orbitPrefix_add P k (N-k) a
  rw [Nat.add_sub_of_le hk] at hh
  rw [hh]
  simp

 theorem frontier_complement (P:Equiv.Perm A) (root:A) (n:ℕ) (x:Fin (n+1)→A)
    (pre post:List A) (h:(pre++List.ofFn x++post).Sublist (cycleWord P root)) :
    ∃l,P^[l] (P (x (Fin.last n)))=x 0 ∧
      (∀i<l,∀j:Fin (n+1),P^[i] (P (x (Fin.last n)))≠x j) ∧
      (post++pre).Sublist (orbitPrefix P l (P (x (Fin.last n)))) := by
  have hne:List.ofFn x≠[]:=by simp
  have hhead:(List.ofFn x).head hne=x 0:=by
    rw [List.head_ofFn]
    congr 1
  have hlast:(List.ofFn x).getLast hne=x (Fin.last n):=by
    rw [List.getLast_ofFn]
    congr 1
  have hx0:x 0∈cycleWord P root:=h.subset (by simp)
  have hrotate:(cycleWord P root).rotate ((cycleWord P root).idxOf (x 0))=cycleWord P (x 0):=by
    rw [←cycleWord_rotate,cycleWord_iterate_idxOf P root (x 0) hx0]
  have hfront:(List.ofFn x++post++pre).Sublist (cycleWord P (x 0)):=by
    have hh:=FiniteCycleSublistCuts.rotate_input_head (cycleWord_nodup P root) hne h
    simpa only [hhead,hrotate] using hh
  have hcomp:(post++pre).Sublist ((cycleWord P (x 0)).drop
      ((cycleWord P (x 0)).idxOf (x (Fin.last n))+1)):=by
    have hh:=FiniteCycleSublistCuts.complementary_arc (cycleWord_nodup P root) hne h
    simpa only [hhead,hlast,hrotate] using hh
  have hx:(List.ofFn x).Sublist (cycleWord P (x 0)):=
    (List.sublist_append_left (List.ofFn x) (post++pre)).trans (by simpa only [List.append_assoc] using hfront)
  let rank:=fun j:Fin (n+1)=>(cycleWord P (x 0)).idxOf (x j)
  let N:=Function.minimalPeriod P (x 0)
  have hm:StrictMono rank:=cycleWord_sublist_rank_strictMono P (x 0) x hx
  have hmem (j:Fin (n+1)):x j∈cycleWord P (x 0):=hx.subset (List.mem_ofFn.mpr ⟨j,rfl⟩)
  have hlt (j:Fin (n+1)):rank j<N:=by
    simpa only [cycleWord,orbitPrefix_length] using List.idxOf_lt_length_iff.mpr (hmem j)
  have hit (j:Fin (n+1)):P^[rank j] (x 0)=x j:=cycleWord_iterate_idxOf P (x 0) (x j) (hmem j)
  let k:=rank (Fin.last n)+1
  have hk:k≤N:=by have hh:=hlt (Fin.last n);omega
  have hstart:P^[k] (x 0)=P (x (Fin.last n)):=by
    change P^[rank (Fin.last n)+1] (x 0)=_
    rw [Function.iterate_succ_apply',hit]
  refine ⟨N-k,?_,?_,?_⟩
  · rw [←hstart,←Function.iterate_add_apply,Nat.sub_add_cancel hk]
    exact Function.isPeriodicPt_minimalPeriod P (x 0)
  · intro i hi j he
    rw [←hstart,←Function.iterate_add_apply,←hit j] at he
    have hil:i+k<N:=by omega
    have hh: i+k=rank j:=
      (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hil (hlt j)).mp he
    have hmj:=hm.monotone (Fin.le_last j)
    dsimp only [k] at hh
    omega
  · have hd:(cycleWord P (x 0)).drop k=orbitPrefix P (N-k) (P (x (Fin.last n))):=by
      change (orbitPrefix P N (x 0)).drop k=_
      rw [orbitPrefix_drop P (x 0) N k hk,hstart]
    rw [←hd]
    exact hcomp

end PlanarHom.FinitePermutationCycles
