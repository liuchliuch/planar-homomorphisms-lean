import PlanarHom.RootedAttachment
import PlanarHom.MixedUnaryParallelMachines
import PlanarHom.UnaryPolynomialMachines
import PlanarHom.UnaryNatConversionMachine
import PlanarHom.FixedVectorMachines
import PlanarHom.ListMutationMachines

/-! Actual fixed rooted-gadget attachment on the mixed occurrence codec.
The supplied root is a binary vertex index. Every original unary occurrence
is retained, and every new edge has the fixed selected label. -/
noncomputable section
namespace PlanarHom.RootedCodeMachines
open Complexity Complexity.MixedCode PairProjectionMachines FixedVectorMachines
variable {n m : ℕ}

def endpoint (vertices root : ℕ) : PUnit ⊕ Fin n → ℕ :=
  Sum.elim (fun _ => root) (fun v => vertices + v.val)

def newEdges (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) (p : ℕ × MixedCode) :
    List (ℕ × (ℕ × ℕ)) :=
  List.ofFn (fun e => (endpoint p.2.vertices p.1 (H.src e),
    endpoint p.2.vertices p.1 (H.dst e), selected))

def attach (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) (p : ℕ × MixedCode) : MixedCode :=
  ⟨p.2.vertices+n, p.2.edges ++ newEdges H selected p, p.2.unaries⟩

def inputEncoding : BitEncoding (ℕ × MixedCode) := BitEncoding.nat.prod MixedCode.encoding

theorem fp_endpoint (a : PUnit ⊕ Fin n) :
    FP inputEncoding BitEncoding.nat (fun p => endpoint p.2.vertices p.1 a) := by
  cases a with
  | inl u => exact fp_fst _ _
  | inr v =>
    have hg := (fp_snd BitEncoding.nat MixedCode.encoding).comp MixedCode.fp_vertices
    have hv := hg.comp UnaryNatConversionMachine.fp_conversion
    exact ((hv.pair (fp_const inputEncoding BitEncoding.nat v.val)).comp
      BinaryArithmetic.fp_addition)

theorem fp_newEdges (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) :
    FP inputEncoding MixedCode.edgeEncoding (newEdges H selected) := by
  have h := fp_assemble inputEncoding
    (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)) m
    (fun p e => (endpoint p.2.vertices p.1 (H.src e),
      endpoint p.2.vertices p.1 (H.dst e),selected))
    (fun e => (fp_endpoint (H.src e)).pair ((fp_endpoint (H.dst e)).pair
      (fp_const inputEncoding BitEncoding.nat selected)))
  exact h.transportOutput (fun _ => rfl)

/-- A genuine compiled FP witness. The fixed gadget size contributes only fixed
constants; neither root validity nor planarity is assumed by this total program. -/
theorem fp_attach (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) :
    FP inputEncoding MixedCode.encoding (attach H selected) := by
  have hg := fp_snd BitEncoding.nat MixedCode.encoding
  have hv := ((hg.comp MixedCode.fp_vertices).comp (UnaryPolynomialMachines.fp_offset n)).congr
    (fun p => Nat.add_comm n p.2.vertices)
  have he := (((hg.comp MixedCode.fp_edges).pair (fp_newEdges H selected)).comp
    (ListMutationMachines.fp_append (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat))))
  exact (hv.pair (he.pair (hg.comp MixedCode.fp_unaries))).transportOutput (fun _ => rfl)

end PlanarHom.RootedCodeMachines
