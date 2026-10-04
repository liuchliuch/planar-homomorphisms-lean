import PlanarHom.FinitePermutationFrontierComplement
import PlanarHom.FinitePermutationSingleCarrierFrontier

/-! NEW complete finite-word boundary-splice induction step on one canonical
carrier. Literal cycle-word order and different-face separation derive every
arc, disjointness, exterior, count and updated-frontier obligation. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open FinitePermutationReturnWords
variable {A:Type} [Fintype A]

 theorem separate_cycles_iterate_ne (P:Equiv.Perm A) {a b u v:A}
    (hsep:¬P.SameCycle a b) (hu:P.SameCycle a u) (hv:P.SameCycle b v) (k:ℕ) :
    P^[k] u≠v := by
  intro he
  have hh:P.SameCycle a (P^[k] u):=by
    simpa only [Equiv.Perm.iterate_eq_pow,Equiv.Perm.sameCycle_pow_right] using hu
  rw [he] at hh
  exact hsep (hh.trans hv.symm)

 theorem splicePrefix_frontier_step (P:Equiv.Perm A) (n:ℕ) (x y:Fin (n+1)→A)
    (pre post outs:List A)
    (hold:CyclicSublist P (pre++List.ofFn x++post))
    (hnew:CyclicSublist P ((List.ofFn y).reverse++outs))
    (hsep:¬P.SameCycle (x 0) (y 0)) :
    let S:=splicePrefix P (extendBoundaryPath n x) (extendBoundaryPath n y) (n+1)
    count S+1=count P+n ∧ CyclicSublist S (pre++outs++post) := by
  obtain ⟨oldroot,hold⟩:=hold
  obtain ⟨newroot,hnew⟩:=hnew
  let X:=extendBoundaryPath n x
  let Y:=extendBoundaryPath n y
  let yrev:=fun j:Fin (n+1)=>y j.rev
  have hx:(List.ofFn x).Sublist (cycleWord P oldroot):=by
    exact ((List.sublist_append_right pre (List.ofFn x)).trans
      (List.sublist_append_left (pre++List.ofFn x) post)).trans hold
  have hy:(List.ofFn y).reverse.Sublist (cycleWord P newroot):=
    (List.sublist_append_left _ outs).trans hnew
  have hyr:(List.ofFn yrev).Sublist (cycleWord P newroot):=by simpa only [yrev,ofFn_rev] using hy
  have hxi:Function.Injective x:=by
    intro a b hab
    exact (cycleWord_sublist_rank_strictMono P oldroot x hx).injective
      (congrArg (fun z=>(cycleWord P oldroot).idxOf z) hab)
  have hyi:Function.Injective y:=by
    intro a b hab
    have hh:= (cycleWord_sublist_rank_strictMono P newroot yrev hyr).injective
      (congrArg (fun z=>(cycleWord P newroot).idxOf z) (show yrev a.rev=yrev b.rev by simpa only [yrev,Fin.rev_rev] using hab))
    exact Fin.rev_injective hh
  have hxc (j:Fin (n+1)):P.SameCycle (x 0) (x j):=by
    exact ((mem_cycleWord P oldroot _).mp (hx.subset (by simp))).symm.trans
      ((mem_cycleWord P oldroot _).mp (hx.subset (List.mem_ofFn.mpr ⟨j,rfl⟩)))
  have hyc (j:Fin (n+1)):P.SameCycle (y 0) (y j):=by
    exact ((mem_cycleWord P newroot _).mp (hy.subset (by simp))).symm.trans
      ((mem_cycleWord P newroot _).mp (hy.subset (by simpa only [List.mem_reverse] using List.mem_ofFn.mpr ⟨j,rfl⟩)))
  have hX (j:ℕ):P.SameCycle (x 0) (X j):=hxc _
  have hY (j:ℕ):P.SameCycle (y 0) (Y j):=hyc _
  have hsep':¬P.SameCycle (y 0) (x 0):=fun h=>hsep h.symm
  have hcross (i j:ℕ):X i≠Y j:=by
    exact separate_cycles_iterate_ne P hsep (hX i) (hY j) 0
  have hd:DistinctPathMarkers X Y (n+1):=
    ⟨extendBoundaryPath_injective n x hxi,extendBoundaryPath_injective n y hyi,fun i _ j _=>hcross i j⟩
  have hs:¬P.SameCycle (X 0) (Y 0):=by simpa only [X,Y,←extendBoundaryPath_at n x (0:Fin (n+1)),←extendBoundaryPath_at n y (0:Fin (n+1))] using hsep
  have hleft:∀i,i<n→MarkedBoundaryArc P X Y (n+1) (X i) (X (i+1)):=by
    intro i hi
    let ii:Fin n:=⟨i,hi⟩
    let arc:=boundaryArc_of_sublist P oldroot x hx ii
    have h0:X i=x ii.castSucc:=extendBoundaryPath_at n x ii.castSucc
    have h1:X (i+1)=x ii.succ:=extendBoundaryPath_at n x ii.succ
    refine ⟨arc.length,arc.positive,?_,?_⟩
    · simpa only [h0,h1] using arc.endpoint
    · intro k hk hk' j hj
      constructor
      · simpa only [h0] using arc.interior k hk hk' j hj
      · exact separate_cycles_iterate_ne P hsep (hX i) (hY j) k
  have hright:∀i,i<n→MarkedBoundaryArc P X Y (n+1) (Y (i+1)) (Y i):=by
    intro i hi
    let ii:Fin n:=⟨i,hi⟩
    let arc:=boundaryArc_of_reverse_sublist P newroot y hy ii
    have h0:Y i=y ii.castSucc:=extendBoundaryPath_at n y ii.castSucc
    have h1:Y (i+1)=y ii.succ:=extendBoundaryPath_at n y ii.succ
    refine ⟨arc.length,arc.positive,?_,?_⟩
    · simpa only [h0,h1] using arc.endpoint
    · intro k hk hk' j hj
      constructor
      · exact separate_cycles_iterate_ne P hsep' (hY (i+1)) (hX j) k
      · simpa only [h1] using arc.interior k hk hk' j hj
  have hc:=count_splicePrefix_arcs P X Y n hd hs hleft hright
  obtain ⟨l,hl,hal,hlword⟩:=frontier_complement P oldroot n x pre post hold
  obtain ⟨r,hr,har,hrword⟩:=frontier_complement P newroot n yrev [] outs (by simpa only [List.nil_append,yrev,ofFn_rev] using hnew)
  have hX0:X 0=x 0:=extendBoundaryPath_at n x (0:Fin (n+1))
  have hXn:X n=x (Fin.last n):=extendBoundaryPath_at n x (Fin.last n)
  have hY0:Y 0=y 0:=extendBoundaryPath_at n y (0:Fin (n+1))
  have hYn:Y n=y (Fin.last n):=extendBoundaryPath_at n y (Fin.last n)
  have heL:P^[l] (P (X n))=X 0:=by simpa only [hX0,hXn] using hl
  have heR:P^[r] (P (Y 0))=Y n:=by
    simpa only [yrev,Fin.rev_last,Fin.rev_zero,hY0,hYn] using hr
  have haL:∀i<l,∀j<n+1,P^[i] (P (X n))≠X j ∧ P^[i] (P (X n))≠Y j:=by
    intro i hi j hj
    constructor
    · have hXj:X j=x ⟨j,hj⟩:=extendBoundaryPath_at n x ⟨j,hj⟩
      simpa only [hXn,hXj] using hal i hi ⟨j,hj⟩
    · exact separate_cycles_iterate_ne P hsep (Equiv.Perm.sameCycle_apply_right.mpr (hX n)) (hY j) i
  have haR:∀i<r,∀j<n+1,P^[i] (P (Y 0))≠X j ∧ P^[i] (P (Y 0))≠Y j:=by
    intro i hi j hj
    constructor
    · exact separate_cycles_iterate_ne P hsep' (Equiv.Perm.sameCycle_apply_right.mpr (hY 0)) (hX j) i
    · have hYj:Y j=y ⟨j,hj⟩:=extendBoundaryPath_at n y ⟨j,hj⟩
      simpa only [yrev,Fin.rev_last,Fin.rev_rev,hY0,hYj] using har i hi (Fin.rev ⟨j,hj⟩)
  refine ⟨hc,splicePrefix_cyclic_frontier P X Y n l r hd hs heL heR haL haR pre post outs ?_ ?_⟩
  · simpa only [hXn] using hlword
  · simpa only [yrev,Fin.rev_last,hY0,List.append_nil] using hrword

end PlanarHom.FinitePermutationCycles
