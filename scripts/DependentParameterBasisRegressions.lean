import PlanarHom.FinishedDependentMatrixFamilyReduction
import Mathlib.LinearAlgebra.Basis.SMul

open PlanarHom PlanarHom.Complexity
open scoped BigOperators
noncomputable section

private def firstBasis : Module.Basis (Fin 1) ℚ ℚ := Module.Basis.singleton (Fin 1) ℚ
private def secondBasis : Module.Basis (Fin 1) ℚ ℚ :=
  firstBasis.unitsSMul (fun _ => Units.mk0 (2 : ℚ) (by norm_num))
private def changingBasis (x : Bool) : Module.Basis (Fin 1) ℚ ℚ := if x then secondBasis else firstBasis

-- The same field element has different exact canonical coordinates at the two parameters.
example : (changingBasis false).equivFun 2 0 = 2 := by
  simp [changingBasis, firstBasis, Module.Basis.equivFun_apply]
example : (changingBasis true).equivFun 2 0 = 1 := by
  norm_num [changingBasis, secondBasis, firstBasis, Module.Basis.equivFun_apply, Units.smul_def]

example : (numberFieldEncoding (changingBasis false)).encode 2 =
    (BitEncoding.rat.vector 1).encode (fun _ => 2) := by
  change (BitEncoding.rat.vector 1).encode _ = _
  congr 1
  funext i
  simp [changingBasis, firstBasis, Module.Basis.equivFun_apply]
example : (numberFieldEncoding (changingBasis true)).encode 2 =
    (BitEncoding.rat.vector 1).encode (fun _ => 1) := by
  change (BitEncoding.rat.vector 1).encode _ = _
  congr 1
  funext i
  norm_num [changingBasis, secondBasis, firstBasis, Module.Basis.equivFun_apply, Units.smul_def]

-- Both basis choices have one uniform actual inclusion program, using finite Boolean selection.
private theorem inclusion_machine : FP (BitEncoding.bool.prod (numberFieldEncoding firstBasis))
    (DependentFieldCodecs.sigma BitEncoding.bool (fun x => numberFieldEncoding (changingBasis x)))
    (fun p : Bool × ℚ => (⟨p.1,p.2⟩ : Σ _ : Bool, ℚ)) := by
  let ei := BitEncoding.bool.prod (numberFieldEncoding firstBasis)
  let e := fun x => numberFieldEncoding (changingBasis x)
  have branch (b : Bool) : FP ei (DependentFieldCodecs.sigma BitEncoding.bool e)
      (fun p : Bool × ℚ => (⟨b,p.2⟩ : Σ _ : Bool, ℚ)) := by
    have hv := (PairProjectionMachines.fp_snd BitEncoding.bool (numberFieldEncoding firstBasis)).comp
      (FixedFieldEncodingTransport.fp_changeBasis firstBasis (changingBasis b))
    have hw := hv.comp (fp_code_view (e b) BitEncoding.bits (e b).encode (fun _ => rfl))
    exact DependentEncodingMachines.fp_assemble BitEncoding.bool e (fp_const ei BitEncoding.bool b) hw
  have hb : FP ei BitEncoding.bool (fun p : Bool × ℚ => decide (p.1 = true)) :=
    (PairProjectionMachines.fp_fst BitEncoding.bool (numberFieldEncoding firstBasis)).congr (fun p => by simp)
  exact (hb.ite (branch true) (branch false)).congr (fun p => by cases p with | mk b a => cases b <;> rfl)

-- The actual descent compiler handles both parameter-dependent bases and padded rows.
example : FP
    (DependentFieldCodecs.sigma BitEncoding.bool (fun x => numberFieldEncoding (changingBasis x)))
    (numberFieldEncoding firstBasis)
    (DependentFieldOutputDescent.descend firstBasis (fun _ : Bool => ℚ) (fun _ => 1) changingBasis
      (fun _ => RingHom.id ℚ) 3) :=
  DependentFieldOutputDescent.fp_descend firstBasis BitEncoding.bool (fun _ : Bool => ℚ)
    (fun _ => 1) changingBasis (fun _ => RingHom.id ℚ) 3 inclusion_machine

example (x : Bool) (a : ℚ) :
    DependentFieldOutputDescent.descend firstBasis (fun _ : Bool => ℚ) (fun _ => 1) changingBasis
      (fun _ => RingHom.id ℚ) 3 ⟨x,a⟩ = a :=
  DependentFieldOutputDescent.descend_inclusion firstBasis (fun _ : Bool => ℚ)
    (fun _ => 1) changingBasis (fun _ => RingHom.id ℚ) 3 (fun _ => by norm_num) x a

-- A negative target multiplier is retained; source inversion and weights stay in ℚ.
example : DependentTargetAggregation.recover (fun _ : Unit => ℚ) (fun _ => RingHom.id ℚ)
    (fun (_ : Unit) (_ : Fin 1) => (-3 : ℚ)) (((),1),([(2,[1])],[10])) = ⟨(),-15⟩ := by
  norm_num [DependentTargetAggregation.recover, DependentTargetAggregation.aggregate,
    SourceInterpolationWeights.weightedRows, SourceInterpolationWeights.weight, SourceInterpolationWeights.table,
    MaterializedLagrangeRecoveryMachines.rowTerm, MaterializedLagrangeRecoveryMachines.otherNodes,
    LagrangeCoefficientMachines.productCoefficients, MaterializedFieldListMachines.shiftedDenominator,
    Fin.prod_univ_succ]

-- A new zero target multiplier gives zero without any nonzero target promise.
example : DependentTargetAggregation.recover (fun _ : Unit => ℚ) (fun _ => RingHom.id ℚ)
    (fun (_ : Unit) (_ : Fin 1) => (0 : ℚ)) (((),1),([(2,[1])],[10])) = ⟨(),0⟩ := by
  norm_num [DependentTargetAggregation.recover, DependentTargetAggregation.aggregate,
    SourceInterpolationWeights.weightedRows, SourceInterpolationWeights.weight, SourceInterpolationWeights.table,
    MaterializedLagrangeRecoveryMachines.rowTerm, MaterializedLagrangeRecoveryMachines.otherNodes,
    LagrangeCoefficientMachines.productCoefficients, MaterializedFieldListMachines.shiftedDenominator,
    Fin.prod_univ_succ]

-- With m = 0, every target monomial is the empty product, even for zero bases.
example : DependentTargetAggregation.recover (fun _ : Unit => ℚ) (fun _ => RingHom.id ℚ)
    (fun (_ : Unit) (_ : Fin 1) => (0 : ℚ)) (((),0),([(1,[0])],[7])) = ⟨(),7⟩ := by
  norm_num [DependentTargetAggregation.recover, DependentTargetAggregation.aggregate,
    SourceInterpolationWeights.weightedRows, SourceInterpolationWeights.weight, SourceInterpolationWeights.table,
    MaterializedLagrangeRecoveryMachines.rowTerm, MaterializedLagrangeRecoveryMachines.otherNodes,
    LagrangeCoefficientMachines.productCoefficients, MaterializedFieldListMachines.shiftedDenominator,
    Fin.prod_univ_succ]
