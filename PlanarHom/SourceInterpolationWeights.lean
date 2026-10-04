import PlanarHom.SourceExponentRepresentatives
import PlanarHom.MaterializedLagrangeRecoveryMachines

/-! Total fixed-source-field interpolation weights, with exponent payloads retained. -/
namespace PlanarHom.SourceInterpolationWeights
open Complexity PairProjectionMachines
variable {K : Type} [Field K] [DecidableEq K]

def table (rows : List (K × List ℕ)) : List (K × K) := rows.map (fun row => (row.1,1))
def weight (rows : List (K × List ℕ)) (answers : List K) (μ : K) : K :=
  MaterializedLagrangeRecoveryMachines.rowTerm (table rows,answers) (μ,1)
def weightedRows (rows : List (K × List ℕ)) (answers : List K) : List (K × List ℕ) :=
  rows.map (fun row => (weight rows answers row.1,row.2))

variable [Algebra ℚ K] {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
noncomputable def inputEncoding := (SourceExponentRepresentatives.rowEncoding basis).list.prod
  (numberFieldEncoding basis).list

theorem fp_table : FP (SourceExponentRepresentatives.rowEncoding basis).list
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list table :=
  ListMapMachines.fp_map _ _ _ ((fp_fst _ _).pair (fp_const _ _ (1 : K)))

theorem fp_weight : FP ((inputEncoding basis).prod (numberFieldEncoding basis))
    (numberFieldEncoding basis) (fun p => weight p.1.1 p.1.2 p.2) := by
  let e := numberFieldEncoding basis
  have hp := fp_fst (inputEncoding basis) e
  have hr := hp.comp (fp_fst (SourceExponentRepresentatives.rowEncoding basis).list e.list)
  have hy := hp.comp (fp_snd (SourceExponentRepresentatives.rowEncoding basis).list e.list)
  have hm := fp_snd (inputEncoding basis) e
  exact (((hr.comp (fp_table basis)).pair hy).pair
    (hm.pair (fp_const ((inputEncoding basis).prod e) e (1 : K)))).comp
      (MaterializedLagrangeRecoveryMachines.fp_rowTerm basis)

theorem fp_weightedRows : FP (inputEncoding basis) (SourceExponentRepresentatives.rowEncoding basis).list
    (fun p => weightedRows p.1 p.2) := by
  let e := numberFieldEncoding basis
  let er := SourceExponentRepresentatives.rowEncoding basis
  have hp := fp_fst (inputEncoding basis) er
  have hr := fp_snd (inputEncoding basis) er
  have hm := hr.comp (fp_fst e BitEncoding.nat.list)
  have hx := hr.comp (fp_snd e BitEncoding.nat.list)
  have hb := ((hp.pair hm).comp (fp_weight basis)).pair hx
  exact ((fp_id (inputEncoding basis)).pair (fp_fst er.list e.list)).comp
    (ListContextMachines.fp_mapWithContext (inputEncoding basis) er er _ hb)

end PlanarHom.SourceInterpolationWeights
