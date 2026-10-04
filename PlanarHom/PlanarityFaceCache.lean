import PlanarHom.PlanarityFaceCodeMachines

/-! NEW exact memoization for executable face-table regression and consumers.
The cache stores the actual raw successor of every original dart; the resulting
full table is proved equal to the uncached program on every raw graph. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRConstraints

 def faceTransitions (g : MixedCode) (bits : List Bool) : List (Dart×Dart) :=
   (allDarts g).map (fun a=>(a,faceStep g bits a))
 def transition (ts : List (Dart×Dart)) (a : Dart) : Dart := (ts.lookup a).getD a
 def finiteOrbit (f : Dart→Dart) (n : ℕ) (a : Dart) := (List.range n).map (fun i=>f^[i] a)
 def finiteBoundary (f : Dart→Dart) (n : ℕ) (a : Dart) :=
   (finiteOrbit f n a).take 1 ++ (finiteOrbit f n a).tail.takeWhile (fun b=>b != a)
 def finiteRepresentatives (ds : List Dart) (f : Dart→Dart) (n : ℕ) :=
   ds.filter (fun a=>decide ((ds.filter (fun b=>decide (b∈finiteOrbit f n a))).headD a=a))
 def cachedFullTable (g : MixedCode) (bits : List Bool) : List MultiGraph.Kasteleyn.RawFace :=
   let ts:=faceTransitions g bits
   let f:=transition ts
   let rs:=finiteRepresentatives (allDarts g) f (2*g.edges.length)
   rs.zipIdx.map (fun p=>(p.2,finiteBoundary f (2*g.edges.length) p.1))
 def cachedComputedTable (g : MixedCode) := cachedFullTable g (decideAligned g).2

 theorem transition_eq (g : MixedCode) (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) :
    transition (faceTransitions g bits) a=faceStep g bits a := by
  unfold transition faceTransitions
  rw [List.lookup_graph (faceStep g bits) ((mem_allDarts g a).mpr ha)]
  rfl

 theorem transition_iterate (g : MixedCode) (bits : List Bool) {a : Dart}
    (ha : a.1<g.edges.length) (n : ℕ) :
    (transition (faceTransitions g bits))^[n] a=(faceStep g bits)^[n] a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,transition_eq g bits]
    · exact (Function.iterate_succ_apply' (faceStep g bits) n a).symm
    · rcases iterate_index_bound g bits a n with h | h
      · exact h
      · simpa only [h] using ha

 theorem finiteOrbit_eq (g : MixedCode) (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) :
    finiteOrbit (transition (faceTransitions g bits)) (2*g.edges.length) a=orbit g bits a := by
  unfold finiteOrbit orbit walk
  apply List.map_congr_left
  intro n hn
  exact transition_iterate g bits ha n

 theorem finiteBoundary_eq (g : MixedCode) (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) :
    finiteBoundary (transition (faceTransitions g bits)) (2*g.edges.length) a=boundary g bits a := by
  simp only [finiteBoundary,finiteOrbit_eq g bits ha,boundary]

 theorem finiteRepresentatives_eq (g : MixedCode) (bits : List Bool) :
    finiteRepresentatives (allDarts g) (transition (faceTransitions g bits)) (2*g.edges.length)=
      representatives g bits := by
  unfold finiteRepresentatives representatives representative
  apply List.filter_congr
  intro a ha
  rw [finiteOrbit_eq g bits ((mem_allDarts g a).mp ha)]

 theorem cachedFullTable_eq (g : MixedCode) (bits : List Bool) : cachedFullTable g bits=fullTable g bits := by
  simp only [cachedFullTable,finiteRepresentatives_eq,fullTable]
  apply List.map_congr_left
  intro p hp
  have ha:=(List.mem_filter.mp (List.fst_mem_of_mem_zipIdx hp)).1
  rw [finiteBoundary_eq g bits ((mem_allDarts g p.1).mp ha)]

 theorem cachedComputedTable_eq (g : MixedCode) : cachedComputedTable g=computedTable g :=
   cachedFullTable_eq g _

 theorem fp_cachedComputedTable : FP MixedCode.encoding MultiGraph.Kasteleyn.tableCode cachedComputedTable :=
   fp_computedTable.congr (fun g=>(cachedComputedTable_eq g).symm)

end PlanarHom.PlanarityFaceCode
