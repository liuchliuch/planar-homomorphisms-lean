import PlanarHom.ProperColoringPottsReduction
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.SourceSimulationOutputBounds

/-! Actual bit-code extraction for the natural proper-coloring source. -/
noncomputable section
open Classical
namespace PlanarHom.ProperColoringPottsReduction
open Complexity Complexity.MixedCode MachineComposition

/-- Total decoded count; malformed incidence data has an explicit zero fallback. -/
def totalColorings (q : ℕ) (g : MixedCode) : ℕ :=
  if hg : g.Valid 1 0 then properColoringCount (g.toMultiGraph hg) q else 0

/-- The conventional natural-output planar proper-coloring counting problem. -/
def naturalColoringProblem (q : ℕ) : PromiseProblem :=
  ⟨PlanarInput 1 0, encodedFunction encoding BitEncoding.nat (totalColorings q) []⟩

private def rawView (q : ℕ) (raw : Bits) (h : (naturalColoringProblem q).valid raw) :
    BitEncoding.ValidWord encoding :=
  ⟨raw,by obtain ⟨g,hd,_⟩ := h; exact ⟨g,hd⟩⟩

private theorem rawView_property (q : ℕ) (raw : Bits) (h : (naturalColoringProblem q).valid raw) :
    (rawView q raw h).value.PlanarValid 1 0 := by
  obtain ⟨g,hd,hg⟩ := h
  have he := BitEncoding.ValidWord.value_eq (w := rawView q raw ⟨g,hd,hg⟩) hd
  rw [he]
  exact hg

/-- The fixed rational basis can be read by an actual coordinate machine. -/
theorem fp_rationalValue : FP (numberFieldEncoding rationalBasis) BitEncoding.rat id :=
  (FixedFieldArithmetic.fp_coordinate rationalBasis 0).congr (fun x => by
    simp [rationalBasis,Module.Basis.equivFun_apply])

/-- Extraction is a concrete binary numerator/absolute-value circuit. It is
correct on natural answers; the total fallback on other rationals is explicit. -/
theorem fp_extractNatural : FP (numberFieldEncoding rationalBasis) BitEncoding.nat
    (fun x : ℚ => x.num.natAbs) :=
  (fp_rationalValue.comp ArithmeticCircuitPrimitives.fp_rat_num).comp
    ArithmeticCircuitPrimitives.fp_int_natAbs

@[simp] theorem extractNatural_natCast (n : ℕ) : (n:ℚ).num.natAbs=n := by simp

theorem coloringValue_eq_natCast (q : ℕ) (g : MixedCode) (hg : g.Valid 1 0) :
    totalEvaluation (fun _ : Fin 1 => coloringMatrix q) (noUnaries q) (fun _ => 1) g =
      (totalColorings q g : ℚ) := by
  rw [totalEvaluation_valid _ _ _ _ hg]
  change g.evaluate hg (fun _ : Fin 1 => coloringMatrix q)
      (fun u : Fin 0 => u.elim0) (fun _ => 1) = _
  rw [evaluate_homogeneous, partition_eq_properColoringCount]
  simp [totalColorings,hg]

/-- One genuine promised query converts the field-coded count into the original
canonical binary natural code, including every raw encoding of a valid graph. -/
def naturalToColoring (q : ℕ) :
    PromisePolyTimeTuringReduction (naturalColoringProblem q) (coloringProblem rationalBasis q) := by
  let e := numberFieldEncoding rationalBasis
  let prepare := fun g : MixedCode => (([] : Bits),[g])
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare := by
    have hl : FP encoding encoding.list (fun g : MixedCode => [g]) :=
      ((fp_id encoding).pair (fp_const encoding encoding.list [])).comp
        (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  let recover := fun z : Bits × List ℚ => z.2.prod.num.natAbs
  have hr : FP (BitEncoding.bits.prod e.list) BitEncoding.nat recover :=
    ((PairProjectionMachines.fp_snd BitEncoding.bits e.list).comp
      (MaterializedFieldListMachines.fp_product rationalBasis)).comp fp_extractNatural
  let pre := composeComputers normalizer (Classical.choice hp)
  let bound := evaluationProblem_output_bound rationalBasis
    (fun _ : Fin 1 => coloringMatrix q) (noUnaries q) (fun _ => 1)
  let p := Classical.choose bound
  have hbound := Classical.choose_spec bound
  apply nonadaptiveReduction (p := p) (BitEncoding.ValidWord.encoding encoding) BitEncoding.bits encoding
    e BitEncoding.nat (naturalColoringProblem q) (coloringProblem rationalBasis q)
    (prepare ∘ BitEncoding.ValidWord.value)
    (totalEvaluation (fun _ : Fin 1 => coloringMatrix q) (noUnaries q) (fun _ => 1)) recover
    pre (Classical.choice hr) (rawView q) (fun _ _ => rfl)
  · intro raw h query hquery
    have hg := rawView_property q raw h
    have he : query=(rawView q raw h).value := by simpa [prepare,Function.comp_def] using hquery
    subst query
    exact ⟨_,encoding.decode_encode _,hg⟩
  · intro query hquery
    obtain ⟨g,hd,hg⟩ := hquery
    rw [encoding.decode_encode] at hd
    cases Option.some.inj hd
    rw [coloringProblem, evaluationProblem]
    change evaluationValue rationalBasis (fun _ : Fin 1 => coloringMatrix q) (noUnaries q) (fun _ => 1)
      (encoding.encode query) = _
    rw [evaluationValue_encode _ _ _ _ _ hg.1, totalEvaluation_valid _ _ _ _ hg.1]
  · intro raw h
    have hg := rawView_property q raw h
    change BitEncoding.nat.encode
      (([totalEvaluation (fun _ : Fin 1 => coloringMatrix q) (noUnaries q) (fun _ => 1)
        (rawView q raw h).value]).prod.num.natAbs) = _
    simp only [List.prod_cons,List.prod_nil,mul_one]
    rw [coloringValue_eq_natCast q _ hg.1, extractNatural_natCast]
    have hd : encoding.decode raw = some (rawView q raw h).value :=
      BitEncoding.ValidWord.decode_raw (rawView q raw h)
    simp [naturalColoringProblem, encodedFunction, hd]
  · exact hbound

/-- Complete natural-output proper-coloring to positive Potts compiler. -/
def naturalToPotts (q : ℕ) :
    PromisePolyTimeTuringReduction (naturalColoringProblem q) (pottsProblem rationalBasis q) :=
  (naturalToColoring q).trans (reduction rationalBasis q)

/-- Concrete three-state source gate with conventional natural count outputs. -/
def threeStateNaturalReduction :
    PromisePolyTimeTuringReduction (naturalColoringProblem 3) (pottsProblem rationalBasis 3) :=
  naturalToPotts 3

end PlanarHom.ProperColoringPottsReduction
