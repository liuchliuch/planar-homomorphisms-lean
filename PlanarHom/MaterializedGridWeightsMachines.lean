import PlanarHom.MaterializedCoefficientMachines
import PlanarHom.FieldDotProductMachines
import PlanarHom.ListContextFilterMachines
import PlanarHom.SelectedStretchMachines
import PlanarHom.FixedFieldPolynomialMachines

/-! Ordinary Lagrange coefficient-dot-query weights on a materialized base-field
grid. Unlike shifted Lagrange, zero is an allowed grid point. -/
noncomputable section
namespace PlanarHom.MaterializedGridWeightsMachines
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

open Classical in
def others (a : K) (xs : List K) : List K := xs.filter (fun b => decide (b ≠ a))

def weight (p : (List K × List K) × K) : K :=
  let ns := others p.2 p.1.1
  let cs := LagrangeCoefficientMachines.productCoefficients ns
  (List.zipWith (· * ·) cs p.1.2).sum / (ns.map (fun b => p.2-b)).prod

def weights (p : List K × List K) : List K := p.1.map (fun a => weight (p,a))

theorem fp_others : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis).list (fun p => others p.1 p.2) := by
  classical
  have hn : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) BitEncoding.bool
      (fun p : K × K => decide (p.2 ≠ p.1)) :=
    ((FixedFieldArithmetic.fp_equality basis).comp (fp_bool_unary BitEncoding.bool not)).congr
      (fun _ => by simp [eq_comm])
  exact ListContextFilterMachines.fp_filterWithContext _ _ _ hn

theorem fp_weight : FP
    (((numberFieldEncoding basis).list.prod (numberFieldEncoding basis).list).prod (numberFieldEncoding basis))
    (numberFieldEncoding basis) weight := by
  let e := numberFieldEncoding basis
  have hp := fp_fst (e.list.prod e.list) e
  have ha := fp_snd (e.list.prod e.list) e
  have hns := hp.comp (fp_fst e.list e.list)
  have hy := hp.comp (fp_snd e.list e.list)
  have ho := (ha.pair hns).comp (fp_others basis)
  have hcs := ho.comp (MaterializedCoefficientMachines.fp_productCoefficients basis)
  have hdif := (ha.pair ho).comp (ListContextMachines.fp_mapWithContext e e e
    (fun p => p.1-p.2) (FixedFieldArithmetic.fp_subtraction basis))
  have hd := hdif.comp (MaterializedFieldListMachines.fp_product basis)
  have hv := (hcs.pair hy).comp (FieldDotProductMachines.fp_dot basis)
  exact (hv.pair hd).comp (FixedFieldArithmetic.fp_division basis)

theorem fp_weights : FP
    ((numberFieldEncoding basis).list.prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis).list weights :=
  ((fp_id _).pair (fp_fst _ _)).comp
    (ListContextMachines.fp_mapWithContext _ _ _ weight (fp_weight basis))

/-- Ascending grid 0,1,…,d, including both endpoints. -/
def grid (d : ℕ) : List K := (List.range (d+1)).map (fun i : ℕ => (i : K))

theorem fp_grid : FP BitEncoding.unaryNat (numberFieldEncoding basis).list (grid (K := K)) := by
  exact ((UnaryArithmeticMachines.fp_succ.comp UnaryArithmeticMachines.fp_range).comp
    (ListMapMachines.fp_map BitEncoding.nat (numberFieldEncoding basis) _
      (FixedFieldPolynomialMachines.fp_natCast basis))).congr (fun _ => rfl)

end PlanarHom.MaterializedGridWeightsMachines
