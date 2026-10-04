import PlanarHom.BooleanFieldTowerProjectorSemantics
import PlanarHom.MaterializedGridWeightsMachines

/-! Complete actual evaluation-grid recovery circuit for grouped radical
projectors. The degree is a literal unary bound; moments are literal base-field
words. No tower Field instance or intermediate height assumption is used. -/
noncomputable section
namespace PlanarHom.BooleanGroupedGridRecoveryMachines
open Complexity PairProjectionMachines BooleanFieldTower BooleanFieldTowerMachines
open BooleanFieldTowerConvolutionMachines BooleanFieldTowerProjectorMachines
open GroupedProjectorValueMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

abbrev Row (K : Type) (n : ℕ) := Tower K n × (List (Tower K n) × List (Tower K n))

def rowEncoding (n : ℕ) : BitEncoding (Row K n) :=
  (encoding basis n).prod ((encoding basis n).list.prod (encoding basis n).list)

def weightedRow (n : ℕ) (p : (List K × Tower K n) × Row K n) : Tower K n :=
  mul (radicands p.1.1) n p.2.1 (projectorValue (operations n) (p.1.1,(p.1.2,p.2.2)))

theorem fp_weightedRow (n : ℕ) : FP
    (((numberFieldEncoding basis).list.prod (encoding basis n)).prod (rowEncoding basis n))
    (encoding basis n) (weightedRow n) := by
  let e := encoding basis n
  let ed := (numberFieldEncoding basis).list
  let er := rowEncoding basis n
  have hc := fp_fst (ed.prod e) er
  have hr := fp_snd (ed.prod e) er
  have hd := hc.comp (fp_fst ed e)
  have hz := hc.comp (fp_snd ed e)
  have heta := hr.comp (fp_fst e (e.list.prod e.list))
  have hns := hr.comp (fp_snd e (e.list.prod e.list))
  have hp := (hd.pair (hz.pair hns)).comp (BooleanFieldTowerProjectorMachines.fp_projectorValue basis n)
  exact (hd.pair (heta.pair hp)).comp (BooleanFieldTowerConvolutionMachines.fp_mul basis n)

def weightedValue (n : ℕ) (p : List K × (Tower K n × List (Row K n))) : Tower K n :=
  BooleanFieldTowerSumMachines.sum n (p.2.2.map (fun r => weightedRow n ((p.1,p.2.1),r)))

theorem fp_weightedValue (n : ℕ) : FP
    ((numberFieldEncoding basis).list.prod ((encoding basis n).prod (rowEncoding basis n).list))
    (encoding basis n) (weightedValue n) := by
  let e := encoding basis n
  let ed := (numberFieldEncoding basis).list
  let er := (rowEncoding basis n).list
  have hd := fp_fst ed (e.prod er)
  have ht := fp_snd ed (e.prod er)
  have hz := ht.comp (fp_fst e er)
  have hrows := ht.comp (fp_snd e er)
  have hm := ((hd.pair hz).pair hrows).comp
    (ListContextMachines.fp_mapWithContext (ed.prod e) (rowEncoding basis n) e _ (fp_weightedRow basis n))
  exact hm.comp (BooleanFieldTowerSumMachines.fp_sum basis n)

def gridValues (n : ℕ) (p : List K × (ℕ × List (Row K n))) : List (Tower K n) :=
  (MaterializedGridWeightsMachines.grid p.2.1).map
    (fun z => weightedValue n (p.1,(embed n z,p.2.2)))

theorem fp_gridValues (n : ℕ) : FP
    ((numberFieldEncoding basis).list.prod (BitEncoding.unaryNat.prod (rowEncoding basis n).list))
    (encoding basis n).list (gridValues n) := by
  let e := encoding basis n
  let ek := numberFieldEncoding basis
  let er := (rowEncoding basis n).list
  let ec := ek.list.prod er
  have hc := fp_fst ec ek
  have hz := fp_snd ec ek
  have hd := hc.comp (fp_fst ek.list er)
  have hr := hc.comp (fp_snd ek.list er)
  have hzt := BooleanFieldTowerMachines.fp_embed basis (ec.prod ek) n _ hz
  have hb := (hd.pair (hzt.pair hr)).comp (fp_weightedValue basis n)
  have hd' := fp_fst ek.list (BitEncoding.unaryNat.prod er)
  have ht := fp_snd ek.list (BitEncoding.unaryNat.prod er)
  have hn := ht.comp (fp_fst BitEncoding.unaryNat er)
  have hrs := ht.comp (fp_snd BitEncoding.unaryNat er)
  have hg := hn.comp (MaterializedGridWeightsMachines.fp_grid basis)
  exact ((hd'.pair hrs).pair hg).comp (ListContextMachines.fp_mapWithContext ec ek e _ hb)

abbrev CoreInput (K : Type) (n : ℕ) := List K × (ℕ × (List (Row K n) × List K))

def coreEncoding (n : ℕ) : BitEncoding (CoreInput K n) :=
  (numberFieldEncoding basis).list.prod
    (BitEncoding.unaryNat.prod ((rowEncoding basis n).list.prod (numberFieldEncoding basis).list))

def recoverTower (n : ℕ) (p : CoreInput K n) : Tower K n :=
  BooleanFieldTowerRecoveryMachines.dot n (p.1,
    (gridValues n (p.1,(p.2.1,p.2.2.1)),
      (MaterializedGridWeightsMachines.weights
        (MaterializedGridWeightsMachines.grid p.2.1,p.2.2.2)).map (embed n)))

theorem fp_recoverTower (n : ℕ) : FP (coreEncoding basis n) (encoding basis n) (recoverTower n) := by
  let e := encoding basis n
  let ek := numberFieldEncoding basis
  let er := (rowEncoding basis n).list
  have hd := fp_fst ek.list (BitEncoding.unaryNat.prod (er.prod ek.list))
  have ht := fp_snd ek.list (BitEncoding.unaryNat.prod (er.prod ek.list))
  have hn := ht.comp (fp_fst BitEncoding.unaryNat (er.prod ek.list))
  have htail := ht.comp (fp_snd BitEncoding.unaryNat (er.prod ek.list))
  have hr := htail.comp (fp_fst er ek.list)
  have hy := htail.comp (fp_snd er ek.list)
  have hv := (hd.pair (hn.pair hr)).comp (fp_gridValues basis n)
  have hg := hn.comp (MaterializedGridWeightsMachines.fp_grid basis)
  have hw := (hg.pair hy).comp (MaterializedGridWeightsMachines.fp_weights basis)
  have he := hw.comp (ListMapMachines.fp_map ek e (embed n)
    (BooleanFieldTowerMachines.fp_embed basis ek n id (fp_id ek)))
  exact (hd.pair (hv.pair he)).comp (BooleanFieldTowerRecoveryMachines.fp_dot basis n)

def recover (n : ℕ) (p : CoreInput K n) : K :=
  BooleanFieldTowerInverse.constantCoeff n (recoverTower n p)

/-- Full literal recovery computer, including invariant coefficient descent. -/
theorem fp_recover (n : ℕ) : FP (coreEncoding basis n) (numberFieldEncoding basis) (recover n) :=
  BooleanFieldTowerInverseMachines.fp_constantCoeff basis _ n _ (fp_recoverTower basis n)

end PlanarHom.BooleanGroupedGridRecoveryMachines
