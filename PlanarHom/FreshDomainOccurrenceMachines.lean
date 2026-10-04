import PlanarHom.SelectedStretchMachines
import PlanarHom.BinarySubtractionMachine

/-! Actual insertion of intrinsic full-domain metadata for newly allocated
vertices. This is not a free pinning operation: the semantic wrapper uses the
fixed full-color domain and proves each appended indicator equals one. -/
namespace PlanarHom.Complexity.MixedCode
open PairProjectionMachines PlanarHom

/-- Keep the graph and original unary occurrences, then attach one fixed
intrinsic-domain label to each new vertex at or beyond the original header. -/
def withFreshDomains (g : MixedCode) (oldVertices domainLabel : ℕ) : MixedCode :=
  ⟨g.vertices, g.edges,
    g.unaries ++ (List.range (g.vertices-oldVertices)).map (fun j => (oldVertices+j,domainLabel))⟩

@[simp] theorem withFreshDomains_vertices (g : MixedCode) (oldVertices label : ℕ) :
    (g.withFreshDomains oldVertices label).vertices = g.vertices := rfl
@[simp] theorem withFreshDomains_edges (g : MixedCode) (oldVertices label : ℕ) :
    (g.withFreshDomains oldVertices label).edges = g.edges := rfl

theorem withFreshDomains_valid {a u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (oldVertices label : ℕ) (hl : label < u) : (g.withFreshDomains oldVertices label).Valid a u := by
  refine ⟨hg.1, ?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hg.2 x hx
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    have hj' := List.mem_range.mp hj
    refine ⟨?_, hl⟩
    change oldVertices+j < g.vertices
    omega

/-- A genuine typed ordinary machine materializes the entire new intrinsic
metadata suffix under the existing unary-header/mixed-code input representation. -/
theorem fp_withFreshDomains (label : ℕ) :
    FP (BitEncoding.unaryNat.prod encoding) encoding (fun p => p.2.withFreshDomains p.1 label) := by
  let e := BitEncoding.unaryNat.prod encoding
  let n := BitEncoding.nat
  have ho := fp_fst BitEncoding.unaryNat encoding
  have hg := fp_snd BitEncoding.unaryNat encoding
  have hv := hg.comp fp_vertices
  have hob := ho.comp UnaryNatConversionMachine.fp_conversion
  have hvb := hv.comp UnaryNatConversionMachine.fp_conversion
  have hd := (hvb.pair hob).comp BinaryArithmetic.fp_subtraction
  have hc : FP e BitEncoding.unaryNat (fun p => p.2.vertices-p.1) := by
    have h := (hv.pair hd).comp (show FP (BitEncoding.unaryNat.prod n) BitEncoding.unaryNat
      (fun p => min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
    exact h.congr (fun p => min_eq_right (Nat.sub_le p.2.vertices p.1))
  have hr := hc.comp UnaryArithmeticMachines.fp_range
  have hitem : FP (n.prod n) (n.prod n) (fun p : ℕ×ℕ => (p.1+p.2,label)) :=
    BinaryArithmetic.fp_addition.pair (fp_const (n.prod n) n label)
  have hf := (hob.pair hr).comp (ListContextMachines.fp_mapWithContext n n (n.prod n)
    (fun p : ℕ×ℕ => (p.1+p.2,label)) hitem)
  have hu := ((hg.comp fp_unaries).pair hf).comp (ListMutationMachines.fp_append (n.prod n))
  exact (hv.pair ((hg.comp fp_edges).pair hu)).transportOutput (fun _ => rfl)

end PlanarHom.Complexity.MixedCode
