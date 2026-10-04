import PlanarHom.GraphDegreeMachines
import PlanarHom.LoopAdditionMachines
import PlanarHom.FiniteLanguageJointReductions

/-! Fixed source loops attached at both ends of every marked edge occurrence.
Old vertices and explicit unaries are retained, and a marked loop receives
both endpoint decorations at its single vertex. -/
noncomputable section
namespace PlanarHom.EndpointLoopMachines
open Complexity Complexity.MixedCode PairProjectionMachines FiniteLabelLookupMachines

def dropAux {b : ℕ} (old : Fin b) : Fin (b+1)→Fin b := Fin.lastCases old id

def loopVertices (selected k : ℕ) (g : MixedCode) : List ℕ :=
  ((GraphDegreeMachines.endpoints (g.edges.filter (fun e=>decide (e.2.2=selected)))).map
    (List.replicate k)).flatten

def transform {b : ℕ} (old : Fin b) (k : ℕ) (g : MixedCode) : MixedCode :=
  addLoopsAt old.val (loopVertices b k g) (g.relabelBinary (finTable (dropAux old)))

theorem fp_repeat (k : ℕ) : FP BitEncoding.nat BitEncoding.nat.list (List.replicate k) := by
  induction k with
  | zero => exact fp_const _ _ []
  | succ k ih => exact ((fp_id BitEncoding.nat).pair ih).comp (ListMutationMachines.fp_cons BitEncoding.nat)

theorem fp_loopVertices (selected k : ℕ) : FP encoding BitEncoding.nat.list (loopVertices selected k) := by
  let edge := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)
  have hlabel := (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)).comp
    (fp_snd BitEncoding.nat BitEncoding.nat)
  have htest := (hlabel.pair (fp_const edge BitEncoding.nat selected)).comp NatListSumMachines.fp_equal
  have hs := (MixedCode.fp_edges.comp (ListFilterMachines.fp_filter edge _ htest)).comp GraphDegreeMachines.fp_endpoints
  exact (hs.comp (ListMapMachines.fp_map BitEncoding.nat BitEncoding.nat.list _ (fp_repeat k))).comp
    (ListFlattenMachines.fp_flatten BitEncoding.nat)

theorem fp_addLoopsAt (selected : ℕ) : FP (BitEncoding.nat.list.prod encoding) encoding
    (fun p : List ℕ×MixedCode=>addLoopsAt selected p.1 p.2) := by
  let input := BitEncoding.nat.list.prod encoding
  let edge := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)
  have hi : FP BitEncoding.nat edge (fun r=>(r,r,selected)) :=
    (fp_id BitEncoding.nat).pair ((fp_id BitEncoding.nat).pair (fp_const _ _ selected))
  have xs := fp_fst BitEncoding.nat.list encoding
  have g := fp_snd BitEncoding.nat.list encoding
  have ls := xs.comp (ListMapMachines.fp_map BitEncoding.nat edge _ hi)
  have es := ((g.comp MixedCode.fp_edges).pair ls).comp (ListMutationMachines.fp_append edge)
  exact ((g.comp MixedCode.fp_vertices).pair (es.pair (g.comp MixedCode.fp_unaries))).transportOutput (fun _=>rfl)

theorem fp_transform {b : ℕ} (old : Fin b) (k : ℕ) : FP encoding encoding (transform old k) :=
  ((fp_loopVertices b k).pair (fp_relabelBinary (finTable (dropAux old)))).comp (fp_addLoopsAt old.val)

theorem loopVertices_lt {b u : ℕ} (g : MixedCode) (hg : g.Valid b u) (selected k : ℕ) :
    ∀r∈loopVertices selected k g,r<g.vertices := by
  intro r hr
  obtain ⟨xs,hxs,hr⟩ := List.mem_flatten.mp hr
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hxs
  have hrv : r=v := (List.mem_replicate.mp hr).2
  subst r
  obtain ⟨e,he,hv⟩ := List.mem_flatMap.mp hv
  have hb := hg.1 e (List.mem_filter.mp he).1
  have hv2 : v=e.1 ∨ v=e.2.1 := by simpa using hv
  rcases hv2 with rfl|rfl
  · exact hb.1
  · exact hb.2.1

theorem transform_planar {b u : ℕ} (old : Fin b) (k : ℕ) (g : MixedCode)
    (hg : g.PlanarValid (b+1) u) : (transform old k g).PlanarValid b u := by
  apply addLoopsAt_planar old.val old.isLt _ _
    (relabelBinary_planar _ hg (lookup_finTable_lt (dropAux old)))
  exact loopVertices_lt g hg.1 b k

end PlanarHom.EndpointLoopMachines
