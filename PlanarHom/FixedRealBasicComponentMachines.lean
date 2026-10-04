import PlanarHom.FixedRealTwinReduction
import PlanarHom.TargetGraphDichotomyMachines
import PlanarHom.FixedRealListProductCorrectness

/-! NEW literal clique, zero and complete-bipartite arithmetic in the represented
fixed-real model. The original parity program is used for bipartiteness, and
actual dense extension products evaluate arbitrary positive fixed weights. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealBasicComponents
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open PairProjectionMachines ArithmeticCircuitPrimitives
variable {n e k l:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

abbrev constCode (x:K) : Code n e := (presentation basis).constant x
@[simp] theorem constant_valid (x:K) : Valid n (constCode basis x) := (presentation basis).constant_valid x
@[simp] theorem constant_value (x:K) : value basis (constCode basis x)=x := (presentation basis).constant_value x

def powerCode (x:K) (m:ℕ) : Code n e :=
  FixedRealListProduct.product basis ((List.range m).map (fun _=>constCode basis x))
theorem fp_powerCode (x:K) : FP BitEncoding.unaryNat (encoding n e) (powerCode basis x) :=
  (FixedRealListProduct.fp_rangeMap BitEncoding.unaryNat (encoding n e) id (fp_id _) _
    (fp_const _ _ (constCode basis x))).comp (FixedRealListProduct.fp_product basis)
theorem powerCode_valid (x:K) (m:ℕ) : Valid n (powerCode basis x m) := by
  apply FixedRealListProduct.product_valid
  intro a ha
  obtain ⟨_,_,rfl⟩:=List.mem_map.mp ha
  exact constant_valid basis x
theorem powerCode_value (x:K) (m:ℕ) : value basis (powerCode basis x m)=x^m := by
  rw [powerCode,FixedRealListProduct.product_value]
  · simp [List.map_map,Function.comp_def,List.map_const',List.prod_replicate]
  · intro a ha
    obtain ⟨_,_,rfl⟩:=List.mem_map.mp ha
    exact constant_valid basis x

def sideValue (μ:Fin k→K) (ν:Fin l→K) (side:Bool) : K := if side then ∑i,ν i else ∑i,μ i
def branchCode (μ:Fin k→K) (ν:Fin l→K) (flip:Bool) (xs:List (Bool×ℕ)) : Code n e :=
  FixedRealListProduct.product basis (xs.map (fun p=>constCode basis (sideValue μ ν (p.1 ^^ flip))))

theorem fp_branchCode (μ:Fin k→K) (ν:Fin l→K) (flip:Bool) :
    FP BipartiteRankTwoTractability.rowCode.list (encoding n e) (branchCode basis μ ν flip) := by
  have hb:=(fp_fst BitEncoding.bool BitEncoding.unaryNat).comp
    (fp_bool_unary BitEncoding.bool (fun b=>decide ((b ^^ flip)=true)))
  have hc:=hb.ite (fp_const _ (encoding n e) (constCode basis (∑i,ν i)))
    (fp_const _ _ (constCode basis (∑i,μ i)))
  have he:FP BipartiteRankTwoTractability.rowCode (encoding n e)
      (fun p=>constCode basis (sideValue μ ν (p.1 ^^ flip))) := by
    apply hc.congr
    intro p
    cases h:p.1 ^^ flip <;> simp [sideValue,h]
  exact (ListMapMachines.fp_map _ _ _ he).comp (FixedRealListProduct.fp_product basis)

theorem branchCode_valid (μ:Fin k→K) (ν:Fin l→K) (flip:Bool) (xs:List (Bool×ℕ)) :
    Valid n (branchCode basis μ ν flip xs) := by
  apply FixedRealListProduct.product_valid
  intro a ha
  obtain ⟨_,_,rfl⟩:=List.mem_map.mp ha
  exact constant_valid basis _

theorem branchCode_value (μ:Fin k→K) (ν:Fin l→K) (flip:Bool) (xs:List (Bool×ℕ)) :
    value basis (branchCode basis μ ν flip xs)=
      BipartiteRankTwoTractability.tableValue (fun _=>1) μ (fun _=>1) ν flip xs := by
  rw [branchCode,FixedRealListProduct.product_value]
  · simp only [List.map_map,Function.comp_def,constant_value]
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    simp [sideValue,BipartiteRankTwoTractability.sideFactor,RankOneEvaluationMachine.factor]
  · intro a ha
    obtain ⟨_,_,rfl⟩:=List.mem_map.mp ha
    exact constant_valid basis _

def bipartiteCode (μ:Fin k→K) (ν:Fin l→K) (g:MixedCode) : Code n e :=
  if (BipartiteRankTwoTractability.coloring g).1 then
    FixedRealExtension.add n (branchCode basis μ ν false (BipartiteRankTwoTractability.table g))
      (branchCode basis μ ν true (BipartiteRankTwoTractability.table g)) else constCode basis 0

theorem fp_bipartiteCode (μ:Fin k→K) (ν:Fin l→K) :
    FP MixedCode.encoding (encoding n e) (bipartiteCode basis μ ν) := by
  have hb:=(BipartiteRankTwoTractability.fp_coloring.comp
    (fp_fst BitEncoding.bool PlanarityParitySolver.assignmentCode)).comp
      (fp_bool_unary BitEncoding.bool (fun b=>decide (b=true)))
  have hl:=BipartiteRankTwoTractability.fp_table.comp (fp_branchCode basis μ ν false)
  have hr:=BipartiteRankTwoTractability.fp_table.comp (fp_branchCode basis μ ν true)
  exact hb.ite ((hl.pair hr).comp (FixedRealExtension.fp_add n e)) (fp_const _ _ (constCode basis 0))

theorem bipartiteCode_valid (μ:Fin k→K) (ν:Fin l→K) (g:MixedCode) : Valid n (bipartiteCode basis μ ν g) := by
  unfold bipartiteCode
  split
  · exact add_valid _ _ (branchCode_valid basis μ ν false _) (branchCode_valid basis μ ν true _)
  · exact constant_valid basis _

theorem bipartiteCode_value (μ:Fin k→K) (ν:Fin l→K) (g:MixedCode) :
    value basis (bipartiteCode basis μ ν g)=
      BipartiteRankTwoTractability.evaluateConnected (fun _=>1) μ (fun _=>1) ν g := by
  unfold bipartiteCode BipartiteRankTwoTractability.evaluateConnected
  split
  · rw [value_add basis _ _ (branchCode_valid basis μ ν false _) (branchCode_valid basis μ ν true _),
      branchCode_value,branchCode_value]
  · exact constant_value basis 0

end PlanarHom.FixedRealBasicComponents
