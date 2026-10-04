import PlanarHom.PositiveFieldPowerRootMachines

noncomputable section
namespace PlanarHom.FixedRealFieldSignRegression
open Complexity
abbrev basis : Module.Basis (Fin 1) ℚ ℚ := Module.Basis.singleton (Fin 1) ℚ
abbrev embedding : ℚ →+* ℝ := Rat.castHom ℝ

-- The actual ordinary machines instantiate at the canonical rational basis.
example : FP (numberFieldEncoding basis) BitEncoding.bool
    (fun x => decide (0 < embedding x)) := FixedRealFieldSign.fp_positive basis embedding
example : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) BitEncoding.bool
    (fun p : ℚ × ℚ => decide (embedding p.1 < embedding p.2)) :=
  FixedRealFieldSign.fp_less basis embedding
example : FP (numberFieldEncoding basis) (numberFieldEncoding basis)
    (PositiveFieldPowerRootMachines.root basis embedding 2) :=
  PositiveFieldPowerRootMachines.fp_root basis embedding 2

-- Positive, negative, and zero sign semantics use the same integer sign function.
example : FixedRealFieldSign.sign embedding (7/3) = 1 := by
  norm_num [FixedRealFieldSign.sign, embedding, Rat.castHom]
example : FixedRealFieldSign.sign embedding (-7/3) = -1 := by
  norm_num [FixedRealFieldSign.sign, embedding, Rat.castHom]
example : FixedRealFieldSign.sign embedding 0 = 0 := by
  norm_num [FixedRealFieldSign.sign, embedding, Rat.castHom]
example : decide (embedding (-7/3) < embedding (-2)) = true := by
  norm_num [embedding, Rat.castHom]

-- The even-power selector chooses the positive root, including from a negative base.
example : PositiveFieldPowerRootMachines.root basis embedding 2 9 = 3 := by
  convert PositiveFieldPowerRootMachines.root_pow basis embedding 2 (by norm_num) 3 (by norm_num [embedding, Rat.castHom]) using 1
example : PositiveFieldPowerRootMachines.root basis embedding 2 ((-3 : ℚ)^2) = 3 := by
  convert PositiveFieldPowerRootMachines.root_pow basis embedding 2 (by norm_num) 3 (by norm_num [embedding, Rat.castHom]) using 1
example : PositiveFieldPowerRootMachines.root basis embedding 3 8 = 2 := by
  convert PositiveFieldPowerRootMachines.root_pow basis embedding 3 (by norm_num) 2 (by norm_num [embedding, Rat.castHom]) using 1
example : PositiveFieldPowerRootMachines.root basis embedding 2 0 = 0 :=
  PositiveFieldPowerRootMachines.root_zero basis embedding 2 (by norm_num)

-- With no real even root, the total selector emits its zero default.
example : PositiveFieldPowerRootMachines.root basis embedding 2 (-9) = 0 := by
  have hempty : PositiveFieldPowerRootMachines.positiveRoots basis embedding 2 (-9) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z hz
    have hz := ((PositiveFieldPowerRootMachines.mem_positiveRoots_iff basis embedding 2
      (by norm_num) z (-9)).mp hz).1
    nlinarith [sq_nonneg z]
  simp [PositiveFieldPowerRootMachines.root, hempty]
end PlanarHom.FixedRealFieldSignRegression
