import PlanarHom.FixedGadgetNetworkCompiler
import PlanarHom.ColoredEdgeGadgetJointReduction

/-! NEW reconstruction: literal edge occurrences become network gates. The old
unary occurrence list and all old vertices are retained, including isolates. -/
noncomputable section
namespace PlanarHom.EdgeSubstitution
open Complexity FixedGadgetNetwork PairProjectionMachines

def gate (e : ℕ × ℕ × ℕ) : Gate := (e.2.2,[e.1,e.2.1])

def network (g : MixedCode) : Network :=
  {base:=⟨g.vertices,[],g.unaries⟩,gates:=g.edges.map gate}

def substitute (ts : List Template) (g : MixedCode) : MixedCode :=
  FixedGadgetNetwork.compile ts (network g)

theorem network_valid (ts : List Template) {bt ut : ℕ}
    (ht : ∀ t∈ts,t.code.Valid bt ut) (hb : ∀t∈ts,t.boundary=2)
    (g : MixedCode) (hg : g.Valid ts.length ut) : (network g).Valid ts bt ut := by
  refine ⟨⟨by simp [network,MixedCode.Valid],hg.2⟩,ht,?_⟩
  intro a ha
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
  have hv := hg.1 e he
  refine ⟨hv.2.2,?_,?_⟩
  · simpa [gate] using (hb _ (gateTemplate_mem (a:=gate e) hv.2.2)).symm
  · intro v hv'
    simp only [gate,List.mem_cons,List.not_mem_nil,or_false] at hv'
    rcases hv' with rfl|rfl
    · exact hv.1
    · exact hv.2.1

theorem substitute_valid (ts : List Template) {bt ut : ℕ}
    (ht : ∀ t∈ts,t.code.Valid bt ut) (hb : ∀t∈ts,t.boundary=2)
    (g : MixedCode) (hg : g.Valid ts.length ut) : (substitute ts g).Valid bt ut := by
  have h := network_valid ts ht hb g hg
  exact compile_valid ts ht (network g).base (network g).gates h.1 le_rfl h.2.2

theorem fp_gate : FP edgeItemEncoding gateEncoding gate := by
  have hs := fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hr := fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hd := hr.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hl := hr.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hnil := fp_const edgeItemEncoding BitEncoding.nat.list []
  have htail := (hd.pair hnil).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  exact hl.pair ((hs.pair htail).comp (ListMutationMachines.fp_cons BitEncoding.nat))

theorem fp_network : FP MixedCode.encoding networkEncoding network := by
  have hb : FP MixedCode.encoding MixedCode.encoding (fun g=>⟨g.vertices,[],g.unaries⟩) :=
    (MixedCode.fp_vertices.pair ((fp_const MixedCode.encoding edgeItemEncoding.list []).pair
      MixedCode.fp_unaries)).transportOutput (fun _=>rfl)
  have hg := MixedCode.fp_edges.comp (ListMapMachines.fp_map _ _ gate fp_gate)
  exact (hb.pair hg).transportOutput (fun _=>rfl)

theorem fp_substitute (ts : List Template) : FP MixedCode.encoding MixedCode.encoding (substitute ts) :=
  fp_network.comp (fp_compile ts)

end PlanarHom.EdgeSubstitution
