import PlanarHom.GroupedProjectorValueMachines
import PlanarHom.BooleanFieldTowerProductMachines
import PlanarHom.RuntimeDotProductMachines

/-! Actual runtime grouped-projector evaluation in the fixed-dimensional radical
algebra, with only the base field carrying a Field instance. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerProjectorMachines
open Complexity PairProjectionMachines BooleanFieldTower BooleanFieldTowerMachines
open BooleanFieldTowerConvolutionMachines GroupedProjectorValueMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def operations (n : ℕ) : Operations (List K) (Tower K n) where
  one := embed n 1
  sub := sub n
  neg := neg n
  mul := fun ds => mul (radicands ds) n
  inverse := fun ds => BooleanFieldTowerInverse.inverse (radicands ds) n
  sum := BooleanFieldTowerSumMachines.sum n
  product := fun ds a xs => xs.foldl (mul (radicands ds) n) a

/-- All operations are concrete programs with previously proved polynomial bit
cost. In particular product carries no remaining prefix-height hypothesis. -/
theorem programs (n : ℕ) : Programs (encoding basis n) (numberFieldEncoding basis).list
    (operations (K := K) n) := by
  let e := encoding basis n
  let ed := (numberFieldEncoding basis).list
  refine ⟨?_, ?_, ?_, ?_, BooleanFieldTowerSumMachines.fp_sum basis n,
    BooleanFieldTowerProductMachines.fp_product basis n⟩
  · exact BooleanFieldTowerMachines.fp_sub basis (e.prod e) n _ _ (fp_fst e e) (fp_snd e e)
  · exact BooleanFieldTowerMachines.fp_neg basis e n id (fp_id e)
  · exact BooleanFieldTowerConvolutionMachines.fp_mul basis n
  · have hd := fp_fst ed e
    exact BooleanFieldTowerInverseMachines.fp_inverse basis (ed.prod e) (fun p => radicands p.1)
      (fun i => hd.comp (DependentMonomialMachines.fp_getD (numberFieldEncoding basis) 0 i)) n _ (fp_snd ed e)

/-- Exact monic-quotient evaluation without polynomial coefficient construction. -/
theorem fp_dividedValue (n : ℕ) : FP
    ((numberFieldEncoding basis).list.prod (((encoding basis n).prod (encoding basis n)).prod
      (encoding basis n).list))
    (encoding basis n) (GroupedProjectorValueMachines.dividedValue (operations (K := K) n)) :=
  GroupedProjectorValueMachines.fp_dividedValue _ _ _ (programs basis n)

/-- For each outsider b this inverts only P_group(b), never within-group
node differences. Algebraic correctness of that inverse uses its norm promise. -/
theorem fp_projectorValue (n : ℕ) : FP
    ((numberFieldEncoding basis).list.prod ((encoding basis n).prod
      ((encoding basis n).list.prod (encoding basis n).list)))
    (encoding basis n) (GroupedProjectorValueMachines.projectorValue (operations (K := K) n)) :=
  GroupedProjectorValueMachines.fp_projectorValue _ _ _ (programs basis n)

end PlanarHom.BooleanFieldTowerProjectorMachines
