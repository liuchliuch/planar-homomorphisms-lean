import PlanarHom.FinitePermutationBoundaryArcGluing
import PlanarHom.FinitePermutationCycleWords
import Mathlib.Data.Fin.Rev

/-! NEW genuine original-permutation boundary arcs extracted from a literal
nodup cycle-word sublist. Arc lengths are differences of actual word ranks. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords
variable {A:Type} [Fintype A]

 theorem cycleWord_sublist_rank_strictMono (P:Equiv.Perm A) (root:A) {n:ℕ}
    (x:Fin n→A) (hx:(List.ofFn x).Sublist (cycleWord P root)) :
    StrictMono (fun i=>(cycleWord P root).idxOf (x i)) := by
  have hp:(cycleWord P root).Pairwise (fun a b=>(cycleWord P root).idxOf a<(cycleWord P root).idxOf b):=by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa only [List.idxOf_getElem (cycleWord_nodup P root)] using hij
  exact (List.pairwise_ofFn (f:=x)
    (R:=fun a b=>(cycleWord P root).idxOf a<(cycleWord P root).idxOf b)).mp (hp.sublist hx)

 theorem cycleWord_iterate_idxOf (P:Equiv.Perm A) (root a:A) (ha:a∈cycleWord P root) :
    P^[(cycleWord P root).idxOf a] root=a := by
  have hh:=List.getElem_idxOf (l:=cycleWord P root) (a:=a) (List.idxOf_lt_length_iff.mpr ha)
  simpa only [cycleWord,orbitPrefix,List.getElem_map,List.getElem_range] using hh

 def boundaryArc_of_sublist (P:Equiv.Perm A) (root:A) {n:ℕ} (x:Fin (n+1)→A)
    (hx:(List.ofFn x).Sublist (cycleWord P root)) (i:Fin n) :
    BoundaryArc P (extendBoundaryPath n x) (n+1) (x i.castSucc) (x i.succ) := by
  let rank:=fun j:Fin (n+1)=>(cycleWord P root).idxOf (x j)
  have hm:StrictMono rank:=cycleWord_sublist_rank_strictMono P root x hx
  have hmem (j:Fin (n+1)):x j∈cycleWord P root:=hx.subset (List.mem_ofFn.mpr ⟨j,rfl⟩)
  have hlt (j:Fin (n+1)):rank j<Function.minimalPeriod P root:=by
    simpa only [cycleWord,orbitPrefix_length] using List.idxOf_lt_length_iff.mpr (hmem j)
  have hit (j:Fin (n+1)):P^[rank j] root=x j:=cycleWord_iterate_idxOf P root (x j) (hmem j)
  have hi:rank i.castSucc<rank i.succ:=hm (by exact i.castSucc_lt_succ)
  refine {length:=rank i.succ-rank i.castSucc,positive:=by omega,endpoint:=?_,interior:=?_}
  · rw [←hit i.castSucc,←Function.iterate_add_apply,Nat.sub_add_cancel hi.le,hit i.succ]
  · intro k hk hk' j hj he
    let jj:Fin (n+1):=⟨j,hj⟩
    have hje:extendBoundaryPath n x j=x jj:=extendBoundaryPath_at n x jj
    rw [hje,←hit i.castSucc,←Function.iterate_add_apply,←hit jj] at he
    have hki:k+rank i.castSucc<Function.minimalPeriod P root:=by have hh:=hlt i.succ;omega
    have hr:k+rank i.castSucc=rank jj:=
      (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hki (hlt jj)).mp he
    by_cases hlo : jj ≤ i.castSucc
    · have hh:=hm.monotone hlo
      omega
    · have hhigh : i.succ ≤ jj := by
        change i.val + 1 ≤ j
        have hh : ¬ j ≤ i.val := hlo
        omega
      have hh:=hm.monotone hhigh
      omega

 theorem ofFn_rev (n:ℕ) (x:Fin n→A) : List.ofFn (fun i=>x i.rev)=(List.ofFn x).reverse := by
  apply List.ext_getElem (by simp)
  intro j hj hk
  simp only [List.getElem_ofFn,List.getElem_reverse,List.length_ofFn]
  congr 1
  apply Fin.ext
  simp only [Fin.val_rev]
  omega

 def boundaryArc_of_reverse_sublist (P:Equiv.Perm A) (root:A) {n:ℕ} (x:Fin (n+1)→A)
    (hx:(List.ofFn x).reverse.Sublist (cycleWord P root)) (i:Fin n) :
    BoundaryArc P (extendBoundaryPath n x) (n+1) (x i.succ) (x i.castSucc) := by
  let y:=fun j:Fin (n+1)=>x j.rev
  have hy:(List.ofFn y).Sublist (cycleWord P root):=by simpa only [y,ofFn_rev] using hx
  let arc:=boundaryArc_of_sublist P root y hy i.rev
  have hend:P^[arc.length] (x i.succ)=x i.castSucc:=by
    simpa only [y,Fin.rev_castSucc,Fin.rev_succ,Fin.rev_rev] using arc.endpoint
  refine {length:=arc.length,positive:=arc.positive,endpoint:=hend,interior:=?_}
  intro k hk hk' j hj he
  let jj:Fin (n+1):=⟨j,hj⟩
  have hh:=arc.interior k hk hk' jj.rev.val jj.rev.isLt
  apply hh
  have hje:extendBoundaryPath n x j=x jj:=extendBoundaryPath_at n x jj
  rw [hje] at he
  simpa only [y,extendBoundaryPath_at,Fin.rev_castSucc,Fin.rev_rev] using he

end PlanarHom.FinitePermutationCycles
