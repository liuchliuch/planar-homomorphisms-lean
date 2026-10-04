import PlanarHom.PlanarityLRComponentMatching
import PlanarHom.PlanarityLRComponentFaceProducts

/-! NEW exact transport of an actual alternating occurrence-cycle flip into
its computed DFS component. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints

 def componentFlip (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {M N : Finset (Fin g.edges.length)} (flip : AlternatingCycleFlip (g.toMultiGraph hg) M N) :
    AlternatingCycleFlip (componentGraph g hg (DirectedSimpleCycle.componentIndex g hg flip.cycle).val)
      (componentMatching g (DirectedSimpleCycle.componentIndex g hg flip.cycle).val M)
      (componentMatching g (DirectedSimpleCycle.componentIndex g hg flip.cycle).val N) where
  cycle := DirectedSimpleCycle.inComponent g hg flip.cycle
  even_length := flip.even_length
  left_perfect := componentMatching_perfect g hg _ M flip.left_perfect
  right_perfect := componentMatching_perfect g hg _ N flip.right_perfect
  left_even i := by
    rw [mem_componentMatching]
    exact flip.left_even i
  right_odd i := by
    rw [mem_componentMatching]
    exact flip.right_odd i
  agree_off e he := by
    rw [mem_componentMatching,mem_componentMatching]
    apply flip.agree_off e.val
    intro i hi
    apply he i
    exact Subtype.ext hi

 theorem componentFlip_boundarySign (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {M N : Finset (Fin g.edges.length)} (flip : AlternatingCycleFlip (g.toMultiGraph hg) M N)
    (orientation : ℕ→Bool) :
    boundarySign (componentOrientation g (DirectedSimpleCycle.componentIndex g hg flip.cycle).val orientation)
      (componentFlip g hg flip).cycle.cycleDarts=
      boundarySign (fun e : Fin g.edges.length=>orientation e.val) flip.cycle.cycleDarts := by
  simp [boundarySign,MultiGraph.DirectedSimpleCycle.cycleDarts,List.map_ofFn,componentFlip,
    DirectedSimpleCycle.inComponent,componentOrientation,dartSign,Function.comp_def]

end PlanarHom.PlanarityLRRealization
