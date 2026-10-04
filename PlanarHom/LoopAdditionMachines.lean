import PlanarHom.RootedLoop
import PlanarHom.RootedCodeNormalization
import PlanarHom.UnaryRangeMachines

/-! Actual planar insertion of one selected-label loop per original vertex,
including isolated vertices. The zero-vertex input is unchanged. -/
noncomputable section
namespace PlanarHom.Complexity.MixedCode
open PlanarHom PairProjectionMachines

def addLoopsAt (selected : ℕ) (xs : List ℕ) (g : MixedCode) : MixedCode :=
  ⟨g.vertices,g.edges ++ xs.map (fun r => (r,r,selected)),g.unaries⟩

def addLoops (selected : ℕ) (g : MixedCode) : MixedCode :=
  addLoopsAt selected (List.range g.vertices).reverse g

@[simp] theorem addLoopsAt_nil (selected : ℕ) (g : MixedCode) : addLoopsAt selected [] g=g := by
  cases g
  simp [addLoopsAt]

@[simp] theorem loop_attachment (selected r : ℕ) (g : MixedCode) :
    RootedCodeMachines.attach RootedGraph.singleLoop selected (r,g) = addLoopsAt selected [r] g := by
  simp [RootedCodeMachines.attach,RootedCodeMachines.newEdges,RootedCodeMachines.endpoint,
    RootedGraph.singleLoop,addLoopsAt,List.ofFn_succ]

theorem addLoopsAt_cons (selected r : ℕ) (xs : List ℕ) (g : MixedCode) :
    addLoopsAt selected (r::xs) g = addLoopsAt selected xs (addLoopsAt selected [r] g) := by
  simp [addLoopsAt,List.append_assoc]

theorem addLoopsAt_planar {b u : ℕ} (selected : ℕ) (hs : selected<b)
    (xs : List ℕ) (g : MixedCode) (hg : g.PlanarValid b u)
    (hx : ∀ r∈xs,r<g.vertices) : (addLoopsAt selected xs g).PlanarValid b u := by
  induction xs generalizing g with
  | nil => simpa using hg
  | cons r xs ih =>
    rw [addLoopsAt_cons]
    have hroot : r<g.vertices := hx r (by simp)
    have hp := RootedCodeMachines.attach_planarValid RootedGraph.singleLoop RootedGraph.singleLoop_planar
      selected g hg ⟨r,hroot⟩ hs
    rw [loop_attachment] at hp
    exact ih _ hp (fun v hv => hx v (by simp [hv]))

theorem addLoops_planar {b u : ℕ} (selected : ℕ) (hs : selected<b)
    (g : MixedCode) (hg : g.PlanarValid b u) : (addLoops selected g).PlanarValid b u := by
  apply addLoopsAt_planar selected hs _ g hg
  intro r hr
  exact List.mem_range.mp (List.mem_reverse.mp hr)

theorem fp_addLoops (selected : ℕ) : FP encoding encoding (addLoops selected) := by
  let edge := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)
  have hi : FP BitEncoding.nat edge (fun r => (r,r,selected)) :=
    (fp_id BitEncoding.nat).pair ((fp_id BitEncoding.nat).pair
      (fp_const BitEncoding.nat BitEncoding.nat selected))
  have hl := (fp_vertices.comp UnaryRangeMachines.fp_range).comp (ListMapMachines.fp_map BitEncoding.nat edge _ hi)
  have he := (fp_edges.pair hl).comp (ListMutationMachines.fp_append edge)
  exact (fp_vertices.pair (he.pair fp_unaries)).transportOutput (fun _ => rfl)

end PlanarHom.Complexity.MixedCode
