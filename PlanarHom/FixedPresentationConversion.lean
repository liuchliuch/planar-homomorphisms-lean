import PlanarHom.FixedGeneratorHomSemantics
import PlanarHom.FixedExtensionInverseRepresented

/-! NEW: explicit fixed-generator changes of represented field presentations.
Every source numerator and denominator is evaluated by the actual dense
substitution machine, then actual inversion and basis-coordinate sums are used.
All generator/basis images are fixed constants of the problem. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedPresentationConversion
open DensePolynomial FixedGeneratorEvaluation Complexity PairProjectionMachines
variable {d e m s : ℕ} {E S : Type} [Field E] [Field S]
  [Algebra (RationalFunction d) E] [Algebra (RationalFunction m) S]
variable (target : Module.Basis (Fin e) (RationalFunction d) E)

def fraction (map : RationalFunction m →+* E) (a : FractionCode m) : FixedRealExtension.Code d e :=
  let f := map.comp (algebraMap (Poly m) (RationalFunction m))
  let x := fun i => f (variablePoly m i)
  FixedRealExtension.divide (FixedRealExtension.multiplicationTable target) (FixedRealExtension.oneCode target)
    (evaluate target m x a.1) (evaluate target m x a.2)

theorem fp_fraction (map : RationalFunction m →+* E) :
    FP (fractionEncoding m) (FixedRealExtension.encoding d e) (fraction target map) := by
  let f := map.comp (algebraMap (Poly m) (RationalFunction m))
  have he := fp_evaluate target m (fun i => f (variablePoly m i))
  exact (((fp_fst (encoding m) (encoding m)).comp he).pair
    ((fp_snd (encoding m) (encoding m)).comp he)).comp
      (FixedRealExtension.fp_divide (FixedRealExtension.multiplicationTable target) (FixedRealExtension.oneCode target))

theorem fraction_valid (map : RationalFunction m →+* E) (a : FractionCode m) :
    FixedRealExtension.Valid d (fraction target map a) :=
  FixedRealExtension.divide_valid target _ (FixedRealExtension.multiplicationTable_realizes target) _ _ _
    (FixedRealExtension.oneCode_valid target) (evaluate_valid target _ _ _) (evaluate_valid target _ _ _)

theorem fraction_value (map : RationalFunction m →+* E) (a : FractionCode m) :
    FixedRealExtension.value target (fraction target map a) = map (fractionValue m a) := by
  unfold fraction
  rw [FixedRealExtension.divide_value target _ (FixedRealExtension.multiplicationTable_realizes target) _ _ _
    (FixedRealExtension.oneCode_valid target) (FixedRealExtension.oneCode_value target)
    (evaluate_valid target _ _ _), evaluate_hom, evaluate_hom]
  simp only [RingHom.comp_apply, fractionValue, map_div₀]

variable (source : Module.Basis (Fin s) (RationalFunction m) S) (embed : S →+* E)

def basisImage (i : Fin s) : FixedRealExtension.Code d e :=
  Classical.choose (FixedRealExtension.value_complete target (embed (source i)))

theorem basisImage_valid (i : Fin s) : FixedRealExtension.Valid d (basisImage target source embed i) :=
  (Classical.choose_spec (FixedRealExtension.value_complete target (embed (source i)))).1

theorem basisImage_value (i : Fin s) :
    FixedRealExtension.value target (basisImage target source embed i) = embed (source i) :=
  (Classical.choose_spec (FixedRealExtension.value_complete target (embed (source i)))).2

def run (a : FixedRealExtension.Code m s) : FixedRealExtension.Code d e :=
  FixedRealExtension.sumList d e (List.ofFn (fun i =>
    FixedRealExtension.mul (FixedRealExtension.multiplicationTable target)
      (fraction target (embed.comp (algebraMap (RationalFunction m) S)) (a.1 i,a.2))
      (basisImage target source embed i)))

theorem fp_run : FP (FixedRealExtension.encoding m s) (FixedRealExtension.encoding d e)
    (run target source embed) := by
  let ep := encoding m
  let ei := FixedRealExtension.encoding m s
  let eo := FixedRealExtension.encoding d e
  have hs : FP ei (eo.vector s) (fun a i =>
      FixedRealExtension.mul (FixedRealExtension.multiplicationTable target)
        (fraction target (embed.comp (algebraMap (RationalFunction m) S)) (a.1 i,a.2))
        (basisImage target source embed i)) := by
    apply FixedVectorMachines.fp_assemble
    intro i
    have hn := (fp_fst (ep.vector s) ep).comp (FixedVectorMachines.fp_coordinate ep s i)
    have hd := fp_snd (ep.vector s) ep
    have hv := (hn.pair hd).comp (fp_fraction target (embed.comp (algebraMap (RationalFunction m) S)))
    exact (hv.pair (fp_const ei eo (basisImage target source embed i))).comp
      (FixedRealExtension.fp_mul d e (FixedRealExtension.multiplicationTable target))
  have hl : FP ei eo.list (fun a => List.ofFn (fun i =>
      FixedRealExtension.mul (FixedRealExtension.multiplicationTable target)
        (fraction target (embed.comp (algebraMap (RationalFunction m) S)) (a.1 i,a.2))
        (basisImage target source embed i))) := hs.transportOutput (fun _ => rfl)
  exact hl.comp (FixedRealExtension.fp_sumList d e)

theorem run_valid (a : FixedRealExtension.Code m s) : FixedRealExtension.Valid d (run target source embed a) := by
  apply FixedRealExtension.sumList_valid
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  exact FixedRealExtension.mul_valid _ _ _ (fraction_valid target _ _) (basisImage_valid target source embed i)

theorem run_value (a : FixedRealExtension.Code m s) :
    FixedRealExtension.value target (run target source embed a) = embed (FixedRealExtension.value source a) := by
  rw [run,FixedRealExtension.value_sumList _ _ (by
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact FixedRealExtension.mul_valid _ _ _ (fraction_valid target _ _) (basisImage_valid target source embed i))]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
  have hx := source.sum_equivFun (FixedRealExtension.value source a)
  have hv : source.equivFun (FixedRealExtension.value source a) = FixedRealExtension.coordinates m a :=
    source.equivFun.apply_symm_apply _
  conv_rhs => rw [← hx]
  simp only [map_sum,Algebra.smul_def,map_mul,hv]
  apply Finset.sum_congr rfl
  intro i _
  rw [FixedRealExtension.value_mul _ target (FixedRealExtension.multiplicationTable_realizes target),
    fraction_value,basisImage_value]
  rfl

end PlanarHom.FixedPresentationConversion
