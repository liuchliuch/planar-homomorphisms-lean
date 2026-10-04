import PlanarHom.OccurrenceMatchingWalkCycle
import PlanarHom.OccurrenceMatchingCycleConfinement

/-! NEW occurrence-injective alternating cycles extracted from differing matchings. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph.PerfectMatching
open Kasteleyn
variable {V E : Type*} {G : MultiGraph V E} {M N : Finset E}
variable (hM : G.PerfectMatching M) (hN : G.PerfectMatching N)

theorem walkVertex_cycleNext (v : V) (n : ℕ) (hn : 2≤n)
    (hreturn : hM.walkState hN v n=(v,true)) (i : Fin n) :
    hM.walkVertex hN v (i.val+1)=hM.walkVertex hN v (cycleNext n hn i).val := by
  by_cases hi:i.val+1<n
  · simp only [cycleNext,Nat.mod_eq_of_lt hi]
  · have hh:i.val+1=n:=by omega
    simp only [cycleNext,hh,Nat.mod_self]
    exact congrArg Prod.fst hreturn

def alternatingCycleOfWalk (v : V) (hd : hM.Differ hN v) (n : ℕ) (hn : 2≤n) (heven : Even n)
    (hreturn : hM.walkState hN v n=(v,true))
    (hinj : Function.Injective (fun i:Fin n=>hM.walkVertex hN v i.val)) : DirectedSimpleCycle G where
  length := n
  length_ge_two := hn
  vertex i := hM.walkVertex hN v i.val
  vertex_injective := hinj
  dart i := hM.walkDart hN v i.val
  edge_injective := by
    intro i j hij
    dsimp only at hij
    have hparity : Even i.val ↔ Even j.val := by
      rw [←hM.walkDart_mem_left hN v hd i.val,←hM.walkDart_mem_left hN v hd j.val,hij]
    rcases dart_eq_or_reverse_of_fst (hM.walkDart hN v i.val) (hM.walkDart hN v j.val) hij with h | h
    · apply hinj
      have hh:=congrArg (fun a:Dart E=>(G.dartPair a).1) h
      dsimp only at hh
      simpa only [walkDart_host] using hh
    · have hh:=congrArg (fun a:Dart E=>(G.dartPair a).1) h
      dsimp only at hh
      rw [walkDart_host,dartPair_reverse_fst,walkDart_head,hM.walkVertex_cycleNext hN v n hn hreturn j] at hh
      have hi:=hinj hh
      rw [hi] at hparity
      have hbad : Even j.val ↔ ¬Even j.val := hparity.symm.trans (cycleNext_even_iff n hn heven j)
      by_cases hj:Even j.val
      · exact ((hbad.mp hj) hj).elim
      · exact (hj (hbad.mpr hj)).elim
  tail_eq i := hM.walkDart_host hN v i.val
  head_eq i := (hM.walkDart_head hN v i.val).trans (hM.walkVertex_cycleNext hN v n hn hreturn i)

include hM hN in
theorem exists_alternating_cycle [Finite V] (hne : M≠N) :
    ∃c:DirectedSimpleCycle G,Even c.length ∧
      (∀i,(c.dart i).1∈M ↔ Even i.val) ∧ (∀i,(c.dart i).1∈N ↔ Odd i.val) := by
  obtain ⟨v,hd⟩:=hM.exists_differ hN hne
  obtain ⟨n,hn,heven,hreturn,hinj⟩:=hM.exists_simple_even_walk hN v
  let c:=hM.alternatingCycleOfWalk hN v hd n hn heven hreturn hinj
  exact ⟨c,heven,fun i=>hM.walkDart_mem_left hN v hd i.val,fun i=>hM.walkDart_mem_right hN v hd i.val⟩

end PlanarHom.MultiGraph.PerfectMatching
