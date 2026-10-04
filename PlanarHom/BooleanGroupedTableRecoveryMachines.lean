import PlanarHom.BooleanGroupedGridRecoveryMachines
import PlanarHom.NatListSumMachines
import PlanarHom.UnaryPolynomialMachines

/-! Total actual grouped recovery from literal radicands, labeled nodes, target
values, and positive-moment answers. A zero outsider is inserted by the machine,
and the zeroth moment is represented by a literal zero. -/
noncomputable section
namespace PlanarHom.BooleanGroupedTableRecoveryMachines
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
open BooleanFieldTower BooleanFieldTowerMachines BooleanGroupedGridRecoveryMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

abbrev Node (K : Type) (n : ℕ) := ℕ × Tower K n
abbrev Input (K : Type) (n : ℕ) := List K × (List (Node K n) × (List (Tower K n) × List K))

def nodeEncoding (n : ℕ) : BitEncoding (Node K n) := BitEncoding.nat.prod (encoding basis n)

def inputEncoding (n : ℕ) : BitEncoding (Input K n) :=
  (numberFieldEncoding basis).list.prod ((nodeEncoding basis n).list.prod
    ((encoding basis n).list.prod (numberFieldEncoding basis).list))

def selectNodes (same : Bool) (p : ℕ × List (Node K n)) : List (Tower K n) :=
  (p.2.filter (fun q => if same then decide (q.1=p.1) else decide (q.1≠p.1))).map Prod.snd

theorem fp_selectNodes (n : ℕ) (same : Bool) : FP
    (BitEncoding.nat.prod (nodeEncoding basis n).list) (encoding basis n).list
    (selectNodes (n := n) same) := by
  let e := encoding basis n
  let en := nodeEncoding basis n
  have hk := fp_fst BitEncoding.nat en
  have hi := (fp_snd BitEncoding.nat en).comp (fp_fst BitEncoding.nat e)
  have he := (hi.pair hk).comp NatListSumMachines.fp_equal
  have hp : FP (BitEncoding.nat.prod en) BitEncoding.bool
      (fun p : ℕ × Node K n => if same then decide (p.2.1=p.1) else decide (p.2.1≠p.1)) := by
    cases same
    · exact (he.comp (fp_bool_unary BitEncoding.bool not)).congr (fun _ => by simp)
    · exact he
  exact (ListContextFilterMachines.fp_filterWithContext BitEncoding.nat en _ hp).comp
    (ListMapMachines.fp_map en e Prod.snd (fp_snd BitEncoding.nat e))

def makeRow (n : ℕ) (p : List (Node K n) × (Tower K n × ℕ)) : Row K n :=
  (p.2.1,(selectNodes true (p.2.2,p.1), zero n :: selectNodes false (p.2.2,p.1)))

theorem fp_makeRow (n : ℕ) : FP
    ((nodeEncoding basis n).list.prod ((encoding basis n).prod BitEncoding.nat))
    (rowEncoding basis n) (makeRow n) := by
  let e := encoding basis n
  let en := (nodeEncoding basis n).list
  let ei := en.prod (e.prod BitEncoding.nat)
  have hn := fp_fst en (e.prod BitEncoding.nat)
  have hr := fp_snd en (e.prod BitEncoding.nat)
  have heta := hr.comp (fp_fst e BitEncoding.nat)
  have hk := hr.comp (fp_snd e BitEncoding.nat)
  have hin := (hk.pair hn).comp (fp_selectNodes basis n true)
  have hout := (hk.pair hn).comp (fp_selectNodes basis n false)
  have hz := ((fp_const ei e (zero n)).pair hout).comp (ListMutationMachines.fp_cons e)
  exact heta.pair (hin.pair hz)

def rows (n : ℕ) (p : List (Node K n) × List (Tower K n)) : List (Row K n) :=
  p.2.zipIdx.map (fun q => makeRow n (p.1,q))

theorem fp_rows (n : ℕ) : FP
    ((nodeEncoding basis n).list.prod (encoding basis n).list)
    (rowEncoding basis n).list (rows n) := by
  have hn := fp_fst (nodeEncoding basis n).list (encoding basis n).list
  have ht := (fp_snd (nodeEncoding basis n).list (encoding basis n).list).comp
    (ListIndexMachines.fp_zipIdx (encoding basis n))
  exact (hn.pair ht).comp (ListContextMachines.fp_mapWithContext
    (nodeEncoding basis n).list ((encoding basis n).prod BitEncoding.nat)
    (rowEncoding basis n) (makeRow n) (fp_makeRow basis n))

/-- Safe quadratic cap after adjoining the separate zero group. -/
def degreeCap (nodeCount : ℕ) : ℕ := (nodeCount+1)*(nodeCount+2)

def prepare (n : ℕ) (p : Input K n) : CoreInput K n :=
  (p.1,(degreeCap p.2.1.length,(rows n (p.2.1,p.2.2.1),0::p.2.2.2)))

theorem fp_prepare (n : ℕ) : FP (inputEncoding basis n) (coreEncoding basis n) (prepare n) := by
  let e := encoding basis n
  let ek := numberFieldEncoding basis
  let en := (nodeEncoding basis n).list
  let tail := e.list.prod ek.list
  have hd := fp_fst ek.list (en.prod tail)
  have ht := fp_snd ek.list (en.prod tail)
  have hns := ht.comp (fp_fst en tail)
  have hrest := ht.comp (fp_snd en tail)
  have heta := hrest.comp (fp_fst e.list ek.list)
  have hy := hrest.comp (fp_snd e.list ek.list)
  have hr := (hns.pair heta).comp (fp_rows basis n)
  have hy0 := ((fp_const (inputEncoding basis n) ek 0).pair hy).comp (ListMutationMachines.fp_cons ek)
  have hcap : FP (inputEncoding basis n) BitEncoding.unaryNat
      (fun p : Input K n => degreeCap p.2.1.length) := by
    exact ((hns.comp (ListUnaryLengthMachine.fp_length (nodeEncoding basis n))).comp
      (UnaryPolynomialMachines.fp_eval ((Polynomial.X+1)*(Polynomial.X+Polynomial.C 2)))).congr
        (fun _ => by simp [degreeCap])
  exact hd.pair (hcap.pair (hr.pair hy0))

def recoverTower (n : ℕ) (p : Input K n) : Tower K n :=
  BooleanGroupedGridRecoveryMachines.recoverTower n (prepare n p)

def recover (n : ℕ) (p : Input K n) : K :=
  BooleanGroupedGridRecoveryMachines.recover n (prepare n p)

/-- Actual polynomial-time grouped interpolation and coefficient-dot-query
recovery from its complete materialized input, with no additional cost premise. -/
theorem fp_recover (n : ℕ) : FP (inputEncoding basis n) (numberFieldEncoding basis) (recover n) :=
  (fp_prepare basis n).comp (BooleanGroupedGridRecoveryMachines.fp_recover basis n)

theorem fp_recoverTower (n : ℕ) : FP (inputEncoding basis n) (encoding basis n) (recoverTower n) :=
  (fp_prepare basis n).comp (BooleanGroupedGridRecoveryMachines.fp_recoverTower basis n)

end PlanarHom.BooleanGroupedTableRecoveryMachines
