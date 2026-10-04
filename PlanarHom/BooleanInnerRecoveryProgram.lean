import PlanarHom.BooleanGroupedMetadataMachines

/-! NEW complete inner-interpolation recovery program: literal metadata,
positive-moment answer attachment and base-coordinate extraction are composed
as actual ordinary polynomial-time machines. -/
noncomputable section
namespace PlanarHom.BooleanInnerRecoveryProgram
open Complexity PairProjectionMachines
open BooleanGroupedMetadataMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension b : ℕ}

def recover (c a w : Fin b→K) (mult : Fin b→ℕ) (g0 : Fin b)
    (p : Input × List K) : K :=
  BooleanGroupedTableRecoveryMachines.recover b
    (attachAnswers (metadata c a w mult g0 p.1,p.2))

theorem fp_recover (basis : Module.Basis (Fin dimension) ℚ K)
    (c a w : Fin b→K) (mult : Fin b→ℕ) (g0 : Fin b) :
    FP (inputEncoding.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis)
      (recover c a w mult g0) := by
  have hm:=(fp_fst inputEncoding (numberFieldEncoding basis).list).comp
    (fp_metadata basis c a w mult g0)
  exact ((hm.pair (fp_snd inputEncoding (numberFieldEncoding basis).list)).comp
    (fp_attachAnswers basis b)).comp (BooleanGroupedTableRecoveryMachines.fp_recover basis b)

/-- Every query is a positive power, with no zeroth-moment oracle. -/
def queryCount (mult : Fin b→ℕ) (m : ℕ) : ℕ :=
  BooleanGroupedTableRecoveryMachines.degreeCap (((∑i,mult i)*m+1)^b)

def queryCountPolynomial (mult : Fin b→ℕ) : Polynomial ℕ :=
  let N := (Polynomial.C (∑i,mult i)*Polynomial.X+1)^b
  (N+1)*(N+2)

theorem queryCount_eq_eval (mult : Fin b→ℕ) (m : ℕ) :
    queryCount mult m = (queryCountPolynomial mult).eval m := by
  simp [queryCount,queryCountPolynomial,BooleanGroupedTableRecoveryMachines.degreeCap,Polynomial.eval_finset_sum]

theorem fp_queryCount (mult : Fin b→ℕ) :
    FP BitEncoding.unaryNat BitEncoding.unaryNat (queryCount mult) :=
  (UnaryPolynomialMachines.fp_eval (queryCountPolynomial mult)).congr (fun m=>(queryCount_eq_eval mult m).symm)

theorem queryCount_matches_metadata (c a w : Fin b→K) (mult : Fin b→ℕ) (g0 : Fin b)
    (m : ℕ) (x : ℚ) :
    queryCount mult m = BooleanGroupedTableRecoveryMachines.degreeCap
      (nodes c a w mult g0 (m,x)).length := by
  simp [queryCount,length_nodes,cap]

end PlanarHom.BooleanInnerRecoveryProgram
