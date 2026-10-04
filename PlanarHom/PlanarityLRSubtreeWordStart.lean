import PlanarHom.PlanarityLRContourRowWords

/-! NEW literal start-point invariance for a computed child subtree port word. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open FinitePermutationReturnWords

def subtreePortKeep (g : MixedCode) (e : Fin g.edges.length) (a : Dart (Fin g.edges.length)) : Bool :=
  !(isTree g a.1.val) && decide (target g e.val=dartHost g a ∨ target g e.val∈PlanarityDepthFirstSearch.ancestors g (dartHost g a))

def subtreeContourPorts (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) : List (Dart (Fin g.edges.length)) :=
  (orbitPrefix (dfsContourForRows g hg rows)
    (Function.minimalPeriod (dfsContourForRows g hg rows) (typedOutward g e))
    (typedOutward g e)).filter (subtreePortKeep g e)

@[simp] theorem subtreePortKeep_eq_true (g : MixedCode) (e : Fin g.edges.length)
    (a : Dart (Fin g.edges.length)) :
    subtreePortKeep g e a=true ↔ isTree g a.1.val=false ∧ Desc g (target g e.val) (dartHost g a) := by
  simp only [subtreePortKeep,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,Desc]

theorem mem_subtreeContourPorts (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) (he : isTree g e.val=true)
    (a : Dart (Fin g.edges.length)) :
    a∈subtreeContourPorts g hg rows e ↔
      isTree g a.1.val=false ∧ Desc g (target g e.val) (dartHost g a) := by
  constructor
  · intro h
    exact (subtreePortKeep_eq_true g e a).mp (List.mem_filter.mp h).2
  · intro h
    have hr : componentRoot g (dartHost g (typedOutward g e))=componentRoot g (dartHost g a) := by
      rw [dartHost_typedOutward,tree_componentRoot g hg he]
      exact componentRoot_eq_of_desc g (dartHost_valid g hg a) h.2
    have hm := (mem_dfsContourForRowsPortWord g hg rows (typedOutward g e) a).mpr ⟨hr,h.1⟩
    exact List.mem_filter.mpr ⟨(List.mem_filter.mp hm).1,(subtreePortKeep_eq_true g e a).mpr h⟩

theorem subtreeContourPorts_reverse_start (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (e : Fin g.edges.length) (he : isTree g e.val=true) :
    subtreeContourPorts g hg rows e=
      (orbitPrefix (dfsContourForRows g hg rows)
        (Function.minimalPeriod (dfsContourForRows g hg rows) (reversePerm _ (typedOutward g e)))
        (reversePerm _ (typedOutward g e))).filter (subtreePortKeep g e) := by
  let P := dfsContourForRows g hg rows
  let a := typedOutward g e
  let N := Function.minimalPeriod P a
  obtain ⟨k,hkpos,hk,hend,hcut⟩ := dfsContourForRows_subtree_interval_exists g hg rows e he
  have hp : Function.minimalPeriod P (reversePerm _ a)=N := by
    rw [←hend]
    exact Function.minimalPeriod_apply_iterate (P.injective.mem_periodicPts a) k
  have hdrop : ((orbitPrefix P N a).drop k).filter (subtreePortKeep g e)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro b hb hkeep
    obtain ⟨i,hi,hib⟩ := List.mem_iff_getElem.mp hb
    have hij : k+i<N := by
      simp only [List.length_drop,orbitPrefix_length] at hi
      omega
    have hib' : P^[k+i] a=b := by
      simpa only [List.getElem_drop,orbitPrefix,List.getElem_map,List.getElem_range] using hib
    have hs := Bool.and_eq_true_iff.mp hkeep
    have hd := of_decide_eq_true hs.2
    rw [←hib'] at hd
    have hki : k+i≤k := ((hcut (k+i) hij).mp hd).2
    have hz : i=0 := by omega
    have hb' : b=reversePerm _ a := by
      calc b=P^[k] a := by simpa only [hz,Nat.add_zero] using hib'.symm
           _=reversePerm _ a := hend
    have hfalse : isTree g b.1.val=false := by simpa only [Bool.not_eq_true'] using hs.1
    rw [hb'] at hfalse
    change isTree g e.val=false at hfalse
    rw [he] at hfalse
    cases hfalse
  change (orbitPrefix P N a).filter _=(orbitPrefix P (Function.minimalPeriod P (reversePerm _ a)) (reversePerm _ a)).filter _
  rw [hp,←hend,orbitPrefix_cycle_rotate]
  exact (filter_rotate_eq_of_drop_eq_nil _ _ k (by simpa only [orbitPrefix_length] using Nat.le_of_lt hk) hdrop).symm

end PlanarHom.PlanarityLRRealization
