import PlanarHom.MixedRootedInstances
import PlanarHom.RootedCodeMachines

/-! Literal fixed mixed rooted-gadget attachment. Original occurrences remain,
and every added binary/unary occurrence retains its own label. Total malformed
input behavior is the same explicit endpoint/allocation arithmetic. -/
noncomputable section
namespace PlanarHom.MixedRootedCodeMachines
open Complexity Complexity.MixedCode RootedCodeMachines PairProjectionMachines FixedVectorMachines
variable {n m k b u:ℕ}

def newEdges (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode) : List (ℕ×(ℕ×ℕ)) :=
  List.ofFn (fun e=>(endpoint p.2.vertices p.1 (H.graph.src e),
    endpoint p.2.vertices p.1 (H.graph.dst e),(H.edgeLabel e).val))

def newUnaries (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode) : List (ℕ×ℕ) :=
  List.ofFn (fun f=>(endpoint p.2.vertices p.1 (H.unaryHost f),(H.unaryLabel f).val))

def attach (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode) : MixedCode :=
  ⟨p.2.vertices+n,p.2.edges++newEdges H p,p.2.unaries++newUnaries H p⟩

theorem fp_newEdges (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) :
    FP inputEncoding MixedCode.edgeEncoding (newEdges H) := by
  have h:=fp_assemble inputEncoding (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)) m
    (fun p e=>(endpoint p.2.vertices p.1 (H.graph.src e),endpoint p.2.vertices p.1 (H.graph.dst e),(H.edgeLabel e).val))
    (fun e=>(fp_endpoint (H.graph.src e)).pair ((fp_endpoint (H.graph.dst e)).pair
      (fp_const _ _ (H.edgeLabel e).val)))
  exact h.transportOutput (fun _=>rfl)

theorem fp_newUnaries (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) :
    FP inputEncoding (BitEncoding.nat.prod BitEncoding.nat).list (newUnaries H) := by
  have h:=fp_assemble inputEncoding (BitEncoding.nat.prod BitEncoding.nat) k
    (fun p f=>(endpoint p.2.vertices p.1 (H.unaryHost f),(H.unaryLabel f).val))
    (fun f=>(fp_endpoint (H.unaryHost f)).pair (fp_const _ _ (H.unaryLabel f).val))
  exact h.transportOutput (fun _=>rfl)

theorem fp_attach (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) :
    FP inputEncoding MixedCode.encoding (attach H) := by
  have hg:=fp_snd BitEncoding.nat MixedCode.encoding
  have hv:=((hg.comp MixedCode.fp_vertices).comp (UnaryPolynomialMachines.fp_offset n)).congr
    (fun p=>Nat.add_comm n p.2.vertices)
  have he:=(((hg.comp MixedCode.fp_edges).pair (fp_newEdges H)).comp
    (ListMutationMachines.fp_append (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat))))
  have hu:=(((hg.comp MixedCode.fp_unaries).pair (fp_newUnaries H)).comp
    (ListMutationMachines.fp_append (BitEncoding.nat.prod BitEncoding.nat)))
  exact (hv.pair (he.pair hu)).transportOutput (fun _=>rfl)

end PlanarHom.MixedRootedCodeMachines
