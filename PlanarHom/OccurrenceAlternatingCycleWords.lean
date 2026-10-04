import PlanarHom.AlternatingIndexWords
import PlanarHom.OccurrenceMatchingCycleConnectivity
import PlanarHom.OccurrenceKasteleynDartWords

/-! NEW exact even/odd directed endpoint words of the actual alternating cycle. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph.DirectedSimpleCycle
open Kasteleyn
variable {V E : Type*} [LinearOrder V] {G : MultiGraph V E}

def vertexAt (c : DirectedSimpleCycle G) (i : ℕ) : V := c.vertex ⟨i%c.length,Nat.mod_lt _ (by have:=c.length_ge_two; omega)⟩
def dartAt (c : DirectedSimpleCycle G) (i : ℕ) : Dart E := c.dart ⟨i%c.length,Nat.mod_lt _ (by have:=c.length_ge_two; omega)⟩
def leftDarts (c : DirectedSimpleCycle G) : List (Dart E) := (List.range (c.length/2)).map (fun i=>c.dartAt (2*i))
def rightDarts (c : DirectedSimpleCycle G) : List (Dart E) := (List.range (c.length/2)).map (fun i=>c.dartAt (2*i+1))
def vertexWord (c : DirectedSimpleCycle G) : List V := (List.range c.length).map c.vertexAt

theorem dartAt_tail (c : DirectedSimpleCycle G) (i : ℕ) : (G.dartPair (c.dartAt i)).1=c.vertexAt i := c.tail_eq _
theorem dartAt_head (c : DirectedSimpleCycle G) (i : ℕ) : (G.dartPair (c.dartAt i)).2=c.vertexAt (i+1) := by
  rw [dartAt,c.head_eq]
  apply congrArg c.vertex
  apply Fin.ext
  simp [cycleNext,vertexAt,Nat.add_mod]

theorem half_twice (c : DirectedSimpleCycle G) (heven : Even c.length) : 2*(c.length/2)=c.length := by
  have hh:=Nat.even_iff.mp heven
  omega

theorem dartAt_range (c : DirectedSimpleCycle G) : (List.range c.length).map c.dartAt=c.cycleDarts := by
  apply List.ext_getElem (by simp [cycleDarts])
  intro i hi hj
  have hi':i<c.length:=by simpa using hi
  simp only [List.getElem_map,List.getElem_range,cycleDarts,List.getElem_ofFn,dartAt,Nat.mod_eq_of_lt hi']

theorem vertexWord_eq_ofFn (c : DirectedSimpleCycle G) : c.vertexWord=List.ofFn c.vertex := by
  apply List.ext_getElem (by simp [vertexWord])
  intro i hi hj
  have hi':i<c.length:=by simpa [vertexWord] using hi
  simp only [vertexWord,List.getElem_map,List.getElem_range,List.getElem_ofFn,vertexAt,Nat.mod_eq_of_lt hi']

theorem left_right_perm (c : DirectedSimpleCycle G) (heven : Even c.length) :
    (c.leftDarts++c.rightDarts).Perm c.cycleDarts := by
  have hh:=(even_odd_range_perm (c.length/2)).map c.dartAt
  rw [c.half_twice heven,c.dartAt_range] at hh
  simpa only [List.map_append,List.map_map,Function.comp_def,leftDarts,rightDarts] using hh

theorem left_word (c : DirectedSimpleCycle G) (heven : Even c.length) : G.dartWord c.leftDarts=c.vertexWord := by
  have hh:=congrArg (List.map c.vertexAt) (range_pair_flatMap (c.length/2))
  rw [c.half_twice heven] at hh
  simpa only [leftDarts,dartWord,pairWord,List.flatMap_map,List.map_map,Function.comp_def,
    dartAt_tail,dartAt_head,List.map_flatMap,List.map_cons,List.map_nil] using hh

theorem right_word (c : DirectedSimpleCycle G) (heven : Even c.length) :
    G.dartWord c.rightDarts=(List.range c.length).map (fun i=>c.vertexAt (i+1)) := by
  have hh:=congrArg (List.map (fun i=>c.vertexAt (i+1))) (range_pair_flatMap (c.length/2))
  rw [c.half_twice heven] at hh
  simpa only [rightDarts,dartWord,pairWord,List.flatMap_map,List.map_map,Function.comp_def,
    dartAt_tail,dartAt_head,List.map_flatMap,List.map_cons,List.map_nil] using hh

def restWord (c : DirectedSimpleCycle G) : List V := (List.range (c.length-1)).map (fun i=>c.vertexAt (i+1))

theorem left_word_cons (c : DirectedSimpleCycle G) (heven : Even c.length) :
    G.dartWord c.leftDarts=c.vertexAt 0::c.restWord := by
  rw [c.left_word heven]
  unfold vertexWord
  conv_lhs => arg 2; rw [show c.length=(c.length-1)+1 by have:=c.length_ge_two; omega,List.range_succ_eq_map]
  simp only [List.map_cons,List.map_map,Function.comp_def,restWord]

theorem right_word_append (c : DirectedSimpleCycle G) (heven : Even c.length) :
    G.dartWord c.rightDarts=c.restWord++[c.vertexAt 0] := by
  rw [c.right_word heven]
  have hn:c.length-1+1=c.length:=by have:=c.length_ge_two; omega
  conv_lhs => arg 2; rw [←hn,List.range_succ]
  simp only [List.map_append,List.map_singleton,hn,restWord]
  congr 1
  simp [vertexAt]

end PlanarHom.MultiGraph.DirectedSimpleCycle
