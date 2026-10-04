import PlanarHom.FixedRealListProductCorrectness
import PlanarHom.FixedRealComponentReduction
import PlanarHom.BipartiteRankTwoEvaluationMachines

/-! Two independent fixed side weights on proper two-colorings. The actual
parity/component machines handle odd cycles, loops, isolates and empty input.
No equality between the two positive side constants is imposed. -/
noncomputable section
namespace PlanarHom.FixedRealTwoSideWeights
open DensePolynomial Complexity PairProjectionMachines FixedRealExtension
open BipartiteRankTwoTractability PlanarityParitySolver
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

abbrev Side:=Fin 1⊕Fin 1
def interaction : Matrix Side Side K := BipartiteRankTwoTractability.matrix (fun _=>1) (fun _=>1)
def weights (α β:K) : Side→K := Sum.elim (fun _=>α) (fun _=>β)

def factorCode (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (flip:Bool) (p:Bool×ℕ) : Code n e :=
  if Bool.xor p.1 flip then (presentation basis).constant β else (presentation basis).constant α

theorem fp_factorCode (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (flip:Bool) :
    FP rowCode (encoding n e) (factorCode basis α β flip) := by
  have hb:=(fp_fst BitEncoding.bool BitEncoding.unaryNat).comp
    (ArithmeticCircuitPrimitives.fp_bool_unary BitEncoding.bool (fun b=>Bool.xor b flip))
  exact (hb.congr (fun p=>by cases h:p.1 <;> cases flip <;> simp [h])).ite (fp_const _ _ ((presentation basis).constant β)) (fp_const _ _ ((presentation basis).constant α))

theorem factorCode_valid (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (flip:Bool) (p:Bool×ℕ) :
    Valid n (factorCode basis α β flip p) := by
  unfold factorCode
  split_ifs <;> exact (presentation basis).constant_valid _

theorem factorCode_value (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (flip:Bool) (p:Bool×ℕ) :
    value basis (factorCode basis α β flip p)=
      sideFactor (fun _:Fin 1=>1) (fun _=>α) (fun _:Fin 1=>1) (fun _=>β) (Bool.xor p.1 flip) p.2 := by
  unfold factorCode sideFactor
  split_ifs <;> simp only [RankOneEvaluationMachine.factor,one_pow,
    mul_one,Finset.univ_unique,Fin.default_eq_zero,Finset.sum_singleton]
  · exact (presentation basis).constant_value _
  · exact (presentation basis).constant_value _

def orientation (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (flip:Bool) (g:MixedCode) : Code n e :=
  FixedRealListProduct.product basis ((table g).map (factorCode basis α β flip))

theorem fp_orientation (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (flip:Bool) :
    FP MixedCode.encoding (encoding n e) (orientation basis α β flip) :=
  (fp_table.comp (ListMapMachines.fp_map rowCode (encoding n e) _ (fp_factorCode basis α β flip))).comp
    (FixedRealListProduct.fp_product basis)

theorem orientation_valid (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (flip:Bool) (g:MixedCode) :
    Valid n (orientation basis α β flip g) := by
  apply FixedRealListProduct.product_valid
  intro a ha
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp ha
  exact factorCode_valid basis α β flip p

theorem orientation_value (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (flip:Bool) (g:MixedCode) :
    value basis (orientation basis α β flip g)=
      tableValue (fun _:Fin 1=>1) (fun _=>α) (fun _:Fin 1=>1) (fun _=>β) flip (table g) := by
  rw [orientation,FixedRealListProduct.product_value]
  · simp only [List.map_map,Function.comp_def,factorCode_value,tableValue]
  · intro a ha
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp ha
    exact factorCode_valid basis α β flip p

def connectedProgram (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (g:MixedCode) : Code n e :=
  if (coloring g).1 then add n (orientation basis α β false g) (orientation basis α β true g) else zeroCode n e

theorem fp_connectedProgram (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) :
    FP MixedCode.encoding (encoding n e) (connectedProgram basis α β) := by
  have hc:=fp_coloring.comp (fp_fst BitEncoding.bool assignmentCode)
  have ha:=((fp_orientation basis α β false).pair (fp_orientation basis α β true)).comp (fp_add n e)
  exact (hc.congr (fun g=>by simp)).ite ha (fp_const _ _ (zeroCode n e))

theorem connectedProgram_valid (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (g:MixedCode) :
    Valid n (connectedProgram basis α β g) := by
  unfold connectedProgram
  split_ifs
  · exact add_valid _ _ (orientation_valid basis α β false g) (orientation_valid basis α β true g)
  · exact zeroCode_valid n e

theorem connectedProgram_value (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K)
    (g:MixedCode) (hg:g.Valid 1 0) (hc:(GraphComponentCode.support g).Connected) (hn:0<g.vertices) :
    value basis (connectedProgram basis α β g)=
      g.evaluate hg (fun _:Fin 1=>interaction) (fun u:Fin 0=>u.elim0) (weights α β) := by
  letI : Algebra ℚ K := ((algebraMap (RationalFunction n) K).comp
    ((algebraMap (Poly n) (RationalFunction n)).comp (qHom n))).toAlgebra
  have hv:value basis (connectedProgram basis α β g)=
      evaluateConnected (fun _:Fin 1=>1) (fun _=>α) (fun _:Fin 1=>1) (fun _=>β) g := by
    unfold connectedProgram evaluateConnected
    split_ifs
    · rw [value_add basis _ _ (orientation_valid basis α β false g) (orientation_valid basis α β true g),
        orientation_value,orientation_value]
    · exact zeroCode_value basis
  rw [hv]
  exact evaluateConnected_correct g hg hc hn _ _ _ _

def program (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (g:MixedCode) : Code n e :=
  FixedRealListProduct.product basis ((GraphComponentCode.components g).map (connectedProgram basis α β))

theorem fp_program (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) :
    FP MixedCode.encoding (encoding n e) (program basis α β) :=
  (GraphComponentMachines.fp_components.comp
    (ListMapMachines.fp_map MixedCode.encoding (encoding n e) _ (fp_connectedProgram basis α β))).comp
      (FixedRealListProduct.fp_product basis)

theorem program_valid (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K) (g:MixedCode) :
    Valid n (program basis α β g) := by
  apply FixedRealListProduct.product_valid
  intro a ha
  obtain ⟨c,hc,rfl⟩:=List.mem_map.mp ha
  exact connectedProgram_valid basis α β c

theorem program_value (basis:Module.Basis (Fin e) (RationalFunction n) K) (α β:K)
    (g:MixedCode) (hg:g.PlanarValid 1 0) : value basis (program basis α β g)=
      g.evaluate hg.1 (fun _:Fin 1=>interaction) (fun u:Fin 0=>u.elim0) (weights α β) := by
  rw [program,FixedRealListProduct.product_value]
  · rw [GraphComponentCode.evaluate_components g hg.1]
    apply congrArg List.prod
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro c hc
    have hp:=GraphComponentCode.components_promises g hg c hc
    rw [MixedCode.totalEvaluation_valid _ _ _ c hp.1.1]
    exact connectedProgram_value basis α β c hp.1.1 hp.2.1 hp.2.2
  · intro a ha
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp ha
    exact connectedProgram_valid basis α β c

end PlanarHom.FixedRealTwoSideWeights
