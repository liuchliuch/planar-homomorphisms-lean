import PlanarHom.FiniteLabelLookupMachines
import PlanarHom.MixedUnaryParallelMachines
import PlanarHom.MixedPlanarCode

/-! Actual fixed label aliases for joint-availability reductions. A target may
contain both the old and auxiliary types; its queried auxiliary label is mapped
to the existing source label, with endpoints, vertex data and occurrences intact. -/
namespace PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLabelLookupMachines

def relabelBinary (table : List (ℕ × ℕ)) (g : MixedCode) : MixedCode:=
  ⟨g.vertices,g.edges.map (fun e=>(e.1,e.2.1,lookup table e.2.2)),g.unaries⟩

def relabelUnary (table : List (ℕ × ℕ)) (g : MixedCode) : MixedCode:=
  ⟨g.vertices,g.edges,g.unaries.map (fun u=>(u.1,lookup table u.2))⟩

theorem relabelBinary_valid (table : List (ℕ × ℕ)) {g : MixedCode} {a b u : ℕ}
    (hg : g.Valid a u) (hlabels : ∀i,i<a→lookup table i<b) : (g.relabelBinary table).Valid b u:=by
  constructor
  · intro e he
    obtain ⟨old,hold,rfl⟩:=List.mem_map.mp he
    obtain ⟨hs,hd,hl⟩:=hg.1 old hold
    exact ⟨hs,hd,hlabels old.2.2 hl⟩
  · exact hg.2

theorem relabelUnary_valid (table : List (ℕ × ℕ)) {g : MixedCode} {b a u : ℕ}
    (hg : g.Valid b a) (hlabels : ∀i,i<a→lookup table i<u) : (g.relabelUnary table).Valid b u:=by
  constructor
  · exact hg.1
  · intro entry he
    obtain ⟨old,hold,rfl⟩:=List.mem_map.mp he
    obtain ⟨hv,hl⟩:=hg.2 old hold
    exact ⟨hv,hlabels old.2 hl⟩

theorem relabelBinary_underlying (table : List (ℕ × ℕ)) (g : MixedCode) :
    (g.relabelBinary table).underlying=g.underlying:=by
  cases g
  simp [relabelBinary,underlying,List.map_map,Function.comp_def]

theorem relabelUnary_underlying (table : List (ℕ × ℕ)) (g : MixedCode) :
    (g.relabelUnary table).underlying=g.underlying:=rfl

theorem fp_relabelBinary (table : List (ℕ × ℕ)) : FP encoding encoding (relabelBinary table):=by
  let n:=BitEncoding.nat
  have hfirst:=PairProjectionMachines.fp_fst n (n.prod n)
  have hsecond:=PairProjectionMachines.fp_snd n (n.prod n)
  have htarget:=hsecond.comp (PairProjectionMachines.fp_fst n n)
  have hlabel:=(hsecond.comp (PairProjectionMachines.fp_snd n n)).comp (fp_lookup table)
  have hitem:=hfirst.pair (htarget.pair hlabel)
  have hedges:=fp_edges.comp (PlanarHom.ListMapMachines.fp_map (n.prod (n.prod n))
    (n.prod (n.prod n)) (fun e=>(e.1,e.2.1,lookup table e.2.2)) hitem)
  exact (fp_vertices.pair (hedges.pair fp_unaries)).transportOutput (fun _=>rfl)

theorem fp_relabelUnary (table : List (ℕ × ℕ)) : FP encoding encoding (relabelUnary table):=by
  let n:=BitEncoding.nat
  have hfirst:=PairProjectionMachines.fp_fst n n
  have hlabel:=(PairProjectionMachines.fp_snd n n).comp (fp_lookup table)
  have hitem:=hfirst.pair hlabel
  have hunaries:=fp_unaries.comp (PlanarHom.ListMapMachines.fp_map (n.prod n)
    (n.prod n) (fun u=>(u.1,lookup table u.2)) hitem)
  exact (fp_vertices.pair (fp_edges.pair hunaries)).transportOutput (fun _=>rfl)

end PlanarHom.Complexity.MixedCode
