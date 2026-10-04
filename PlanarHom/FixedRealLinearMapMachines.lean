import PlanarHom.FixedRealExtensionPresentation

/-! NEW: every fixed linear map between prescribed finite-extension
presentations has an actual dense-code compiler. The table is fixed data;
its semantic correctness does not replace the compiled runtime. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealLinearMap
open Complexity PairProjectionMachines DensePolynomial

structure Table (d e f : ℕ) where
  denominator : DensePolynomial.Code d
  numerator : Fin f → Fin e → DensePolynomial.Code d
  valid : interpret d denominator ≠ 0

def run {d e f : ℕ} (T : Table d e f) (a : FixedRealExtension.Code d e) :
    FixedRealExtension.Code d f :=
  (fun i => fixedSum d e (fun j => DensePolynomial.mul d (a.1 j) (T.numerator i j)),
    DensePolynomial.mul d a.2 T.denominator)

theorem fp_run {d e f : ℕ} (T : Table d e f) :
    FP (FixedRealExtension.encoding d e) (FixedRealExtension.encoding d f) (run T) := by
  let ep := DensePolynomial.encoding d
  let ec := FixedRealExtension.encoding d e
  have hn : FP ec (ep.vector f) (fun a i => fixedSum d e
      (fun j => DensePolynomial.mul d (a.1 j) (T.numerator i j))) := by
    apply FixedVectorMachines.fp_assemble
    intro i
    apply fp_fixedSum
    intro j
    have ha := (fp_fst (ep.vector e) ep).comp (FixedVectorMachines.fp_coordinate ep e j)
    exact (ha.pair (fp_const ec ep (T.numerator i j))).comp (DensePolynomial.fp_mul d)
  have hd := ((fp_snd (ep.vector e) ep).pair (fp_const ec ep T.denominator)).comp
    (DensePolynomial.fp_mul d)
  exact hn.pair hd

theorem run_valid {d e f : ℕ} (T : Table d e f) (a : FixedRealExtension.Code d e)
    (ha : FixedRealExtension.Valid d a) : FixedRealExtension.Valid d (run T a) := by
  change interpret d (DensePolynomial.mul d a.2 T.denominator) ≠ 0
  rw [interpret_mul]
  exact mul_ne_zero ha T.valid

theorem coordinates_run {d e f : ℕ} (T : Table d e f)
    (a : FixedRealExtension.Code d e) (i : Fin f) :
    FixedRealExtension.coordinates d (run T a) i =
      ∑ j, FixedRealExtension.coordinates d a j * fractionValue d (T.numerator i j,T.denominator) := by
  simp only [FixedRealExtension.coordinates, run, fractionValue, interpret_fixedSum,
    interpret_mul, map_sum, map_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

variable {d e f : ℕ} {E F : Type} [Field E] [Field F]
  [Algebra (RationalFunction d) E] [Algebra (RationalFunction d) F]

def Table.Realizes (T : Table d e f)
    (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F)
    (map : E →ₗ[RationalFunction d] F) : Prop :=
  ∀ i j, fractionValue d (T.numerator i j,T.denominator) = output.equivFun (map (input j)) i

theorem exists_table (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F)
    (map : E →ₗ[RationalFunction d] F) : ∃ T : Table d e f, T.Realizes input output map := by
  obtain ⟨q,p,hq,hp⟩ := DensePolynomial.exists_common_denominator d
    (fun v : Fin f × Fin e => output.equivFun (map (input v.2)) v.1)
  exact ⟨⟨q,fun i j => p (i,j),hq⟩,fun i j => hp (i,j)⟩

def table (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F)
    (map : E →ₗ[RationalFunction d] F) : Table d e f :=
  Classical.choose (exists_table input output map)

theorem table_realizes (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F)
    (map : E →ₗ[RationalFunction d] F) : (table input output map).Realizes input output map :=
  Classical.choose_spec (exists_table input output map)

theorem value_run (T : Table d e f)
    (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F)
    (map : E →ₗ[RationalFunction d] F) (hT : T.Realizes input output map)
    (a : FixedRealExtension.Code d e) :
    FixedRealExtension.value output (run T a) = map (FixedRealExtension.value input a) := by
  apply output.equivFun.injective
  change output.equivFun (output.equivFun.symm (FixedRealExtension.coordinates d (run T a))) = _
  rw [output.equivFun.apply_symm_apply]
  funext i
  rw [coordinates_run]
  have hv := input.sum_equivFun (FixedRealExtension.value input a)
  rw [← hv]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [hT]
  simp only [FixedRealExtension.value, input.equivFun.apply_symm_apply]

def problem (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F)
    (map : E →ₗ[RationalFunction d] F) : RepresentedBit.Problem :=
  (FixedRealExtension.presentation output).problem (FixedRealExtension.encoding d e)
    (FixedRealExtension.Valid d) (fun a => map (FixedRealExtension.value input a))

/-- Arbitrary valid input representatives are accepted. The returned code is
in the prescribed output presentation; no canonical field encoding is used. -/
theorem inFP (input : Module.Basis (Fin e) (RationalFunction d) E)
    (output : Module.Basis (Fin f) (RationalFunction d) F)
    (map : E →ₗ[RationalFunction d] F) : (problem input output map).InFP :=
  (FixedRealExtension.presentation output).problem_inFP _ (FixedRealExtension.normalizer d e) _ _
    (run (table input output map)) (fp_run _) (run_valid _)
    (fun a _ => value_run _ input output map (table_realizes input output map) a)

end PlanarHom.FixedRealLinearMap
