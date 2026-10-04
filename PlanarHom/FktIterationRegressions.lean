import PlanarHom.OccurrenceKasteleynOrientationIteration
import PlanarHom.RadialPottsAssemblyRibbonMiddle
import PlanarHom.PlanarFaces

/-! NEW generic regression checks. Arbitrary occurrence types and endpoint maps
retain loops, parallel occurrences and isolates. No connectedness or nonemptiness
hypothesis is used. -/
noncomputable section
open Set unitInterval
open PlanarHom PlanarHom.MultiGraph

-- Finite ordinary-planarity input, no embedding supplied.
example {V E : Type*} [Finite V] [Finite E] (G : MultiGraph V E) (h : G.Planar) :
    ∃ (R : RibbonDrawing G) (p : PolygonalDrawing G), p.drawing = R.centerDrawing :=
  h.exists_polygonal_ribbon_center

-- The complete closed edge is incident to both assigned actual faces.
example {V E : Type*} {G : MultiGraph V E} (R : RibbonDrawing G) (e : E) (t : I) :
    R.centerDrawing.curve e t ∈ closure (R.sideFace false e) ∧
    R.centerDrawing.curve e t ∈ closure (R.sideFace true e) :=
  ⟨R.curve_mem_closure_sideFace false e t,R.curve_mem_closure_sideFace true e t⟩

-- Opposite open sides remain disjoint even for the same loop occurrence.
example {V E : Type*} {G : MultiGraph V E} (R : RibbonDrawing G) (e : E)
    (_loop : G.src e = G.dst e) :
    Disjoint (R.sideRegion false e) (R.sideRegion true e) :=
  R.sideRegion_disjoint (by simp)

-- Distinct parallel occurrences still have disjoint collar sides.
example {V E : Type*} {G : MultiGraph V E} (R : RibbonDrawing G) (e f : E)
    (hne : e ≠ f) (_src : G.src e = G.src f) (_dst : G.dst e = G.dst f) (b c : Bool) :
    Disjoint (R.sideRegion b e) (R.sideRegion c f) :=
  R.sideRegion_disjoint (fun h => hne (congrArg Prod.fst h))

-- Every host vertex, including an isolate, is avoided by both nonzero sides.
example {V E : Type*} {G : MultiGraph V E} (R : RibbonDrawing G)
    (v : V) (b : Bool) (e : E) (t s : I) (ht : Inside t) (hs : 0 < (s : ℝ)) :
    R.sideBand b e (t,s) ≠ R.centerDrawing.point v := by
  intro h
  exact R.sideBand_not_mem_support b e t s ht hs (Or.inl ⟨v,h.symm⟩)

-- Empty occurrence type needs no invented edge witness.
example {V : Type*} [Finite V] (G : MultiGraph V Empty) (h : G.Planar) :
    ∃ (R : RibbonDrawing G) (p : PolygonalDrawing G), p.drawing = R.centerDrawing :=
  h.exists_polygonal_ribbon_center

-- Literal ordinary planar single-edge and finite parallel-edge examples.
example : ∃ (R : RibbonDrawing TwoTerminal.singleEdge)
    (p : PolygonalDrawing TwoTerminal.singleEdge), p.drawing = R.centerDrawing :=
  TwoTerminal.StripDrawing.singleEdge.planar.exists_polygonal_ribbon_center

example (n : ℕ) : ∃ (R : RibbonDrawing (TwoTerminal.parallelEdges n))
    (p : PolygonalDrawing (TwoTerminal.parallelEdges n)), p.drawing = R.centerDrawing :=
  (TwoTerminal.StripDrawing.parallelEdges n).planar.exists_polygonal_ribbon_center


namespace PlanarHom.MultiGraph.Kasteleyn

-- An empty table returns the empty toggle history.
example : computeOrientation [] = [] := by decide

-- A forward triangle already has an odd number of agreeing traversals.
example : computeOrientation [(1,[(0,true),(1,true),(2,true)])] = [] := by decide

-- An even forward boundary actually causes one recorded reversal.
example : computeOrientation [(1,[(0,true),(1,true),(2,true),(3,true)])] = [0] := by decide

-- Reverse substitution solves two coupled rows; naive forward repair fails here.
example : computeOrientation [(1,[(0,true),(1,true)]),(2,[(1,true),(2,true)])] = [1] := by decide

example : FaceOdd
    (logOrientation (computeOrientation [(1,[(0,true),(1,true)]),(2,[(1,true),(2,true)])]))
    [(0,true),(1,true)] := by unfold FaceOdd; decide

example : FaceOdd
    (logOrientation (computeOrientation [(1,[(0,true),(1,true)]),(2,[(1,true),(2,true)])]))
    [(1,true),(2,true)] := by unfold FaceOdd; decide

-- A bridge's opposite darts are retained, not incorrectly deduplicated.
example : incidenceParity 7 [(7,true),(7,false)] = false := by decide
example : pickPivot (fun _ : Nat => [(7,true),(7,false)]) [1] = none := by decide
example : FaceOdd (fun _ : Nat => true) [(7,true),(7,false)] := by unfold FaceOdd; decide

-- A genuinely unsatisfiable empty boundary is not certified by the solver.
example : ¬ FaceOdd (logOrientation (computeOrientation [(1,[])])) [] := by unfold FaceOdd; decide

-- Toggle-log parity, as required by occurrence-skew evaluation.
example : logOrientation [4,4] 4 = true := by decide
example : logOrientation [4,4,4] 4 = false := by decide
example : logOrientation [1,2,1] 9 = true := by decide

end PlanarHom.MultiGraph.Kasteleyn

-- Exact recovered middle-band consumer works on each constructed side ribbon.
example {V E : Type*} {G : MultiGraph V E} (R : RibbonDrawing G) (positive : Bool)
    (a b : I) (hab : a < b) (ha : Inside a) (hb : Inside b) (e : E) :
    Topology.IsClosedEmbedding ((R.sideRibbon positive).middleBand a b hab.le e) :=
  (R.sideRibbon positive).middleBand_isClosedEmbedding a b hab ha hb e


namespace PlanarHom.MultiGraph.Kasteleyn

example (table : List RawFace) : computeOrientationIterative table = computeOrientation table :=
  computeOrientationIterative_eq_computeOrientation table

example : computeOrientationIterative [(1,[(0,true),(1,true)]),(2,[(1,true),(2,true)])] = [1] := by decide
example : (peelState [(1,[(0,true),(1,true)]),(2,[(1,true),(2,true)])]).2.2 =
    [(2,1),(1,0)] := by decide

-- Failure clears the residual list and does not fabricate a pivot.
example : (peelState [(1,[])]).2 = ([],[]) := by decide

-- Malformed duplicate labels are still handled by the same total finite program.
example : (peelState [(1,[(0,true)]),(1,[(0,true)])]).2.2 = [(1,0),(1,0)] := by decide

example (table : List RawFace) (n : Nat) (fs : List Nat) (stack : List RawPivot) :
    (peelStep^[n] (table,(fs,stack))).2.2.length ≤ n+stack.length :=
  peelStep_iterate_stack_length table n fs stack

example (table : List RawFace) (stack : List RawPivot) (log : List Nat) :
    (stack.foldl (repairLog table) log).Sublist ((stack.map Prod.snd).reverse ++ log) :=
  repairLog_foldl_sublist table stack log

end PlanarHom.MultiGraph.Kasteleyn
