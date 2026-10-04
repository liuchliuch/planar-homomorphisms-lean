import PlanarHom.ProductRepresentativeMachines
import PlanarHom.UnaryOccurrenceCount
import PlanarHom.ListUnaryLengthMachine
import PlanarHom.ListReverseMachines

/-! Actual polynomial-size batches of the positive thickening queries used in
joint product interpolation. All original graph data is copied by real machines. -/
namespace PlanarHom.GraphInterpolationQueries
open PlanarHom.Complexity

def inputEncoding : BitEncoding (ℕ × MixedCode):=BitEncoding.unaryNat.prod MixedCode.encoding

def queries (transform : ℕ→MixedCode→MixedCode) (p : ℕ × MixedCode) : List MixedCode:=
  (List.range p.1).map (fun i=>transform (i+1) p.2)

/-- A materialized unary query count supplies every positive exponent1..N.
The machine works on arbitrary typed codes; query promise preservation is a
separate semantic/planarity theorem. -/
theorem fp_queries (transform : ℕ→MixedCode→MixedCode)
    (ht : FP inputEncoding MixedCode.encoding (fun p=>transform p.1 p.2)) :
    FP inputEncoding MixedCode.encoding.list (queries transform):=by
  have hc:=PairProjectionMachines.fp_fst inputEncoding BitEncoding.nat
  have hi:=PairProjectionMachines.fp_snd inputEncoding BitEncoding.nat
  have hn:=hc.comp (PairProjectionMachines.fp_fst BitEncoding.unaryNat MixedCode.encoding)
  have hg:=hc.comp (PairProjectionMachines.fp_snd BitEncoding.unaryNat MixedCode.encoding)
  have hs:=hi.comp PlanarHom.BinaryArithmetic.fp_successor
  have he:=(hn.pair hs).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    BitEncoding.unaryNat (fun p=>min p.1 p.2) from ⟨PlanarHom.BoundedUnaryMachines.computer⟩)
  have body:=(he.pair hg).comp ht
  have hm:=PlanarHom.ListContextMachines.fp_mapWithContext inputEncoding BitEncoding.nat MixedCode.encoding
    (fun p=>transform (min p.1.1 (p.2+1)) p.1.2) body
  have hrange:= (PlanarHom.UnaryRangeMachines.fp_range.comp
    (PlanarHom.ListReverseMachines.fp_reverse BitEncoding.nat)).congr (fun n=>List.reverse_reverse (List.range n))
  have hr:=(PairProjectionMachines.fp_fst BitEncoding.unaryNat MixedCode.encoding).comp hrange
  have h:=((fp_id inputEncoding).pair hr).comp hm
  apply h.congr
  intro p
  apply List.map_congr_left
  intro i hi
  have hi' : i<p.1:=List.mem_range.mp hi
  change transform (min p.1 (i+1)) p.2=transform (i+1) p.2
  rw [min_eq_right (by omega)]

theorem queries_length (transform : ℕ→MixedCode→MixedCode) (p : ℕ × MixedCode) :
    (queries transform p).length=p.1:=by simp [queries]

theorem mem_queries {transform : ℕ→MixedCode→MixedCode} {p : ℕ × MixedCode} {g : MixedCode}
    (hg : g∈queries transform p) : ∃n,1≤n ∧ n≤p.1 ∧ g=transform n p.2:=by
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hg
  have hlt : i<p.1:=List.mem_range.mp hi
  exact ⟨i+1,by omega,by omega,rfl⟩

theorem fp_binaryQueries (selected : ℕ) :
    FP inputEncoding MixedCode.encoding.list (queries (MixedCode.parallelLabel selected)):=
  fp_queries _ (PlanarHom.MixedParallelMachines.fp_parallelLabel selected)

theorem fp_unaryQueries (selected : ℕ) :
    FP inputEncoding MixedCode.encoding.list (queries (MixedCode.parallelUnaryLabel selected)):=
  fp_queries _ (MixedCode.fp_parallelUnaryLabel selected)

variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension t : ℕ}

/-- The batch size is the actual number of computed distinct nonzero products. -/
theorem fp_binaryQueryCount (basis : Module.Basis (Fin dimension) ℚ K)
    (A B : Fin t→K) (selected : ℕ) :
    FP MixedCode.encoding BitEncoding.unaryNat
      (fun g=>(ExponentProductTables.representatives A B (g.markedCount selected)).length):=
  ((MixedCode.fp_unaryMarkedCount selected).comp (ExponentProductTables.fp_representatives basis A B)).comp
    (PlanarHom.ListUnaryLengthMachine.fp_length ((numberFieldEncoding basis).prod (numberFieldEncoding basis)))

theorem fp_unaryQueryCount (basis : Module.Basis (Fin dimension) ℚ K)
    (A B : Fin t→K) (selected : ℕ) :
    FP MixedCode.encoding BitEncoding.unaryNat
      (fun g=>(ExponentProductTables.representatives A B (g.unaryMarkedCount selected)).length):=
  ((MixedCode.fp_unaryMarkedCount_unary selected).comp (ExponentProductTables.fp_representatives basis A B)).comp
    (PlanarHom.ListUnaryLengthMachine.fp_length ((numberFieldEncoding basis).prod (numberFieldEncoding basis)))

theorem fp_binaryBatch (basis : Module.Basis (Fin dimension) ℚ K)
    (A B : Fin t→K) (selected : ℕ) :
    FP MixedCode.encoding MixedCode.encoding.list (fun g=>queries (MixedCode.parallelLabel selected)
      ((ExponentProductTables.representatives A B (g.markedCount selected)).length,g)):=
  ((fp_binaryQueryCount basis A B selected).pair (fp_id MixedCode.encoding)).comp (fp_binaryQueries selected)

theorem fp_unaryBatch (basis : Module.Basis (Fin dimension) ℚ K)
    (A B : Fin t→K) (selected : ℕ) :
    FP MixedCode.encoding MixedCode.encoding.list (fun g=>queries (MixedCode.parallelUnaryLabel selected)
      ((ExponentProductTables.representatives A B (g.unaryMarkedCount selected)).length,g)):=
  ((fp_unaryQueryCount basis A B selected).pair (fp_id MixedCode.encoding)).comp (fp_unaryQueries selected)

end PlanarHom.GraphInterpolationQueries
