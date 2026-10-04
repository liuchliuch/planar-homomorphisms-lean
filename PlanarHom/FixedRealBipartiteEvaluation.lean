import PlanarHom.FixedRealGraphEvaluation
import PlanarHom.BipartiteRankTwoEvaluationMachines

/-! NEW represented weighted bipartite rank-two computer. Both independent
side-orientation products are computed and summed before actual component
aggregation; unequal sides, isolates, zeros and signs are retained. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealGraphEvaluation
open Complexity Complexity.MixedCode DensePolynomial FixedRealEvaluation PairProjectionMachines
open BipartiteRankTwoTractability ArithmeticCircuitPrimitives
variable {n e k l:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def factorProgram {q:ℕ} (a w:Fin q→K) :
    Program basis BitEncoding.unaryNat (fun _=>True) (RankOneEvaluationMachine.factor a w) :=
  Program.sum Finset.univ (fun i d=>w i*a i^d)
    (fun i=>(Program.constant basis _ _ (w i)).mul (power basis (a i)))

def sideProgram (a μ:Fin k→K) (b ν:Fin l→K) :
    Program basis rowCode (fun _=>True) (fun p=>sideFactor a μ b ν p.1 p.2) :=
  Program.ite Prod.fst (fp_fst BitEncoding.bool BitEncoding.unaryNat)
    ((factorProgram basis b ν).pullback _ _ Prod.snd (fp_snd BitEncoding.bool BitEncoding.unaryNat) (fun _ _=>True.intro))
    ((factorProgram basis a μ).pullback _ _ Prod.snd (fp_snd BitEncoding.bool BitEncoding.unaryNat) (fun _ _=>True.intro))

def orientationProgram (a μ:Fin k→K) (b ν:Fin l→K) (flip:Bool) :
    Program basis MixedCode.encoding (FixedRealComponents.connectedValid (b:=1) (u:=0))
      (fun g=>tableValue a μ b ν flip (table g)) := by
  have hf:FP rowCode rowCode (fun p:Bool×ℕ=>(p.1 ^^ flip,p.2)):=
    (((fp_fst BitEncoding.bool BitEncoding.unaryNat).comp
      (fp_bool_unary BitEncoding.bool (fun b=>b ^^ flip))).pair
      (fp_snd BitEncoding.bool BitEncoding.unaryNat))
  let P:Program basis rowCode (fun _=>True) (fun p=>sideFactor a μ b ν (p.1 ^^ flip) p.2):=
    (sideProgram basis a μ b ν).pullback _ _ (fun p:Bool×ℕ=>(p.1 ^^ flip,p.2)) hf (fun _ _=>True.intro)
  exact P.productMap.pullback _ _ table fp_table (fun _ _ _ _=>True.intro)

theorem bipartite (a μ:Fin k→K) (b ν:Fin l→K) :
    Evaluable basis (matrix a b) (Sum.elim μ ν) := by
  have hc:FP MixedCode.encoding BitEncoding.bool (fun g=>(coloring g).1):=
    fp_coloring.comp (fp_fst BitEncoding.bool PlanarityParitySolver.assignmentCode)
  let P:Program basis MixedCode.encoding (FixedRealComponents.connectedValid (b:=1) (u:=0))
      (evaluateConnected a μ b ν):=
    Program.ite (fun g=>(coloring g).1) hc
      ((orientationProgram basis a μ b ν false).add (orientationProgram basis a μ b ν true))
      (Program.constant basis _ _ 0)
  apply components basis (matrix a b) (Sum.elim μ ν)
  refine P.congr _ ?_
  intro g hp
  rw [value,totalEvaluation_valid _ _ _ g hp.1.1]
  letI:Algebra ℚ K:=((algebraMap (RationalFunction n) K).comp
    ((algebraMap (Poly n) (RationalFunction n)).comp (DensePolynomial.qHom n))).toAlgebra
  exact evaluateConnected_correct g hp.1.1 hp.2.1 hp.2.2 a μ b ν

end PlanarHom.FixedRealGraphEvaluation
