import PlanarHom.BooleanFieldTowerConvolutionMachines
import PlanarHom.BooleanFieldTowerInverseMachines

/-! Exact runtime coefficient-dot-query recovery in the radical algebra. All
materialized products and their sum are compiled with genuine FP programs. -/
noncomputable section
namespace PlanarHom.RuntimeDotProductMachines
open Complexity PairProjectionMachines
variable {A C : Type}

def dot (zero : A) (mul : C → A → A → A) (sum : C → List A → A)
    (p : C × (List A × List A)) : A :=
  sum p.1 (p.2.1.zipIdx.map (fun q => mul p.1 q.1 (p.2.2[q.2]?.getD zero)))

theorem fp_dot (ea : BitEncoding A) (ec : BitEncoding C) (zero : A)
    (mul : C → A → A → A) (sum : C → List A → A)
    (hmul : FP (ec.prod (ea.prod ea)) ea (fun p => mul p.1 p.2.1 p.2.2))
    (hsum : FP (ec.prod ea.list) ea (fun p => sum p.1 p.2)) :
    FP (ec.prod (ea.list.prod ea.list)) ea (dot zero mul sum) := by
  let ect := ec.prod ea.list
  let ei := ea.prod BitEncoding.nat
  have hct := fp_fst ect ei
  have hr := fp_snd ect ei
  have hc := hct.comp (fp_fst ec ea.list)
  have hys := hct.comp (fp_snd ec ea.list)
  have ha := hr.comp (fp_fst ea BitEncoding.nat)
  have hk := hr.comp (fp_snd ea BitEncoding.nat)
  have hzero := fp_const (ect.prod ei) BitEncoding.nat 0
  have ht := ((hc.pair (hys.pair hk)).pair (ha.pair hzero)).comp
    (CoefficientConvolutionMachines.fp_term ea ec zero mul hmul)
  have ht' : FP (ect.prod ei) ea (fun p : (C × List A) × (A × ℕ) =>
      mul p.1.1 p.2.1 (p.1.2[p.2.2]?.getD zero)) :=
    ht.congr (fun _ => by simp [CoefficientConvolutionMachines.term])
  have hc' := fp_fst ec (ea.list.prod ea.list)
  have hls := fp_snd ec (ea.list.prod ea.list)
  have hx := (hls.comp (fp_fst ea.list ea.list)).comp (ListIndexMachines.fp_zipIdx ea)
  have hy := hls.comp (fp_snd ea.list ea.list)
  have hm := ((hc'.pair hy).pair hx).comp
    (ListContextMachines.fp_mapWithContext ect ei ea _ ht')
  exact (hc'.pair hm).comp hsum

variable {R : Type} [CommRing R]

theorem indexed_dot_eq (xs ys : List R) :
    (xs.zipIdx.map (fun q => q.1 * ys[q.2]?.getD 0)).sum =
      (List.zipWith (· * ·) xs ys).sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    cases ys with
    | nil => simp
    | cons b ys =>
      simpa [List.zipIdx_cons, List.zipIdx_succ, List.map_map, Function.comp_def] using
        congrArg (fun z => a*b+z) (ih ys)

end PlanarHom.RuntimeDotProductMachines

namespace PlanarHom.BooleanFieldTowerRecoveryMachines
open Complexity PairProjectionMachines BooleanFieldTower BooleanFieldTowerMachines
open BooleanFieldTowerAlgebra BooleanFieldTowerConvolutionMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def dot (n : ℕ) (p : List K × (List (Tower K n) × List (Tower K n))) : Tower K n :=
  RuntimeDotProductMachines.dot (zero n) (fun ds => mul (radicands ds) n)
    (fun _ => BooleanFieldTowerSumMachines.sum n) p

theorem fp_dot (n : ℕ) : FP
    ((numberFieldEncoding basis).list.prod ((encoding basis n).list.prod (encoding basis n).list))
    (encoding basis n) (dot n) :=
  RuntimeDotProductMachines.fp_dot _ _ (zero n) (fun ds => mul (radicands ds) n)
    (fun _ => BooleanFieldTowerSumMachines.sum n) (BooleanFieldTowerConvolutionMachines.fp_mul basis n)
    ((fp_snd _ _).comp (BooleanFieldTowerSumMachines.fp_sum basis n))

omit [Algebra ℚ K] in
theorem dot_eq (n : ℕ) (p : List K × (List (Tower K n) × List (Tower K n))) :
    dot n p = (List.zipWith (fun a b : Carrier (radicands p.1) n => a*b) p.2.1 p.2.2).sum := by
  rw [← RuntimeDotProductMachines.indexed_dot_eq]
  simp only [dot, RuntimeDotProductMachines.dot, sum_eq, mul_eq, zero_eq]
  rfl

/-- Exact base-coefficient extraction after the polynomial recovery sum.
Its identification with the desired query value is a separate invariance
statement; no single radical branch is assumed injective. -/
theorem fp_recoverConstant (n : ℕ) : FP
    ((numberFieldEncoding basis).list.prod ((encoding basis n).list.prod (encoding basis n).list))
    (numberFieldEncoding basis)
    (fun p => BooleanFieldTowerInverse.constantCoeff n (dot n p)) :=
  BooleanFieldTowerInverseMachines.fp_constantCoeff basis _ n _ (fp_dot basis n)

end PlanarHom.BooleanFieldTowerRecoveryMachines
