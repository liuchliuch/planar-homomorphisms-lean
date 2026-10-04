import PlanarHom.FKTIsingUniformMachines

/-! NEW graph/rational-parameter specialization with literal rational input
and output codecs. Positivity is needed only for semantic interpolation samples;
the same program is total for all encoded graphs and rational parameters. -/
noncomputable section
open Classical
namespace PlanarHom.FKTIsingUniform
open Complexity PairProjectionMachines MachineComposition

def rationalBasis : Module.Basis (Fin 1) ℚ ℚ := Module.Basis.singleton (Fin 1) ℚ

theorem fp_ratEncode : FP BitEncoding.rat (numberFieldEncoding rationalBasis) (id : ℚ→ℚ) :=
  (FixedFieldPolynomialMachines.fp_ratCast rationalBasis).congr (fun x => by simp)

theorem fp_ratDecode : FP (numberFieldEncoding rationalBasis) BitEncoding.rat (id : ℚ→ℚ) :=
  (FixedFieldArithmetic.fp_coordinate rationalBasis 0).congr (fun x => by
    simp [rationalBasis,Module.Basis.equivFun_apply])

/-- Uniform, graph-first rational input and literal rational answer. -/
theorem fp_value_rat : FP (MixedCode.encoding.prod BitEncoding.rat) BitEncoding.rat
    (fun p : MixedCode×ℚ => FKTIsingMachines.value p.2 p.1) := by
  have hg := fp_fst MixedCode.encoding BitEncoding.rat
  have hρ := (fp_snd MixedCode.encoding BitEncoding.rat).comp fp_ratEncode
  have h := ((hg.pair hρ).comp (fp_value rationalBasis)).comp fp_ratDecode
  exact h.congr (fun _ => rfl)

theorem rational_joint_output_bound : ∃p:Polynomial ℕ,∀g:MixedCode,∀ρ:ℚ,
    (BitEncoding.rat.encode (FKTIsingMachines.value ρ g)).length≤
      p.eval (((MixedCode.encoding.prod BitEncoding.rat).encode (g,ρ)).length) := by
  obtain ⟨computer⟩ := fp_value_rat
  exact ⟨outputLengthPolynomial computer,fun g ρ => encoded_output_length_le computer (g,ρ)⟩

theorem value_eq_partition_rat {g : MixedCode} {bt ut : ℕ} (hg : g.PlanarValid bt ut)
    (ρ : ℚ) (hρ : 0<ρ) :
    FKTIsingMachines.value ρ g=(g.toMultiGraph hg.1).partition (FKTIsingMachines.matrix ρ) (fun _=>1) := by
  apply FKTIsingMachines.value_eq_partition rationalBasis (Rat.castHom ℝ) hg ρ
  have hp : (0:ℝ)<(Rat.castHom ℝ) ρ := by
    change (0:ℝ)<(ρ:ℝ)
    exact_mod_cast hρ
  exact ne_of_gt (add_pos zero_lt_one hp)

/-- Explicit total raw extension. Malformed decoding returns the stated empty
word; semantic and joint machine theorems above cover every encoded pair. -/
def rawValue (raw : Bits) : Bits :=
  encodedFunction (MixedCode.encoding.prod BitEncoding.rat) BitEncoding.rat
    (fun p : MixedCode×ℚ => FKTIsingMachines.value p.2 p.1) [] raw

end PlanarHom.FKTIsingUniform
