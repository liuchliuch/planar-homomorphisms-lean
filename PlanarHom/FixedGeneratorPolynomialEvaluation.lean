import PlanarHom.FixedRealListSum
import PlanarHom.FixedRealRationalScaling
import PlanarHom.FixedRealAlphabetPresentation
import PlanarHom.ListPrefixMachines

/-! NEW: actual polynomial substitution at fixed extension-field generators.
Dense degrees and rational coefficients vary with the input. Each generator
power is an actual bounded-prefix fixed-alphabet computation; every coefficient
product and dynamic sum uses the proved shared-denominator code machines. -/
noncomputable section
open Classical
namespace PlanarHom.FixedGeneratorEvaluation
open DensePolynomial Complexity PairProjectionMachines
variable {d e : ℕ} {E : Type} [Field E] [Algebra (RationalFunction d) E]
variable (basis : Module.Basis (Fin e) (RationalFunction d) E)

def unitCode : FixedRealExtension.Code d e :=
  Classical.choose (FixedRealExtension.value_complete basis 1)

theorem unitCode_valid : FixedRealExtension.Valid d (unitCode basis) :=
  (Classical.choose_spec (FixedRealExtension.value_complete basis 1)).1
theorem unitCode_value : FixedRealExtension.value basis (unitCode basis) = 1 :=
  (Classical.choose_spec (FixedRealExtension.value_complete basis 1)).2

def evaluate : (m : ℕ) → (Fin m → E) → DensePolynomial.Code m → FixedRealExtension.Code d e
  | 0,_,c => FixedRealExtension.rationalScale d c (unitCode basis)
  | m+1,x,p => FixedRealExtension.sumList d e (p.zipIdx.map (fun q =>
      FixedRealExtension.mul (FixedRealExtension.multiplicationTable basis)
        (evaluate m (fun i => x i.succ) q.1)
        (FixedRealAlphabet.word (FixedRealAlphabet.data basis (fun _ : Fin 1 => x 0))
          ((p.take q.2).map (fun _ => (0 : Fin 1))))))

theorem evaluate_valid (m : ℕ) (x : Fin m → E) (p : DensePolynomial.Code m) :
    FixedRealExtension.Valid d (evaluate basis m x p) := by
  induction m with
  | zero => exact FixedRealExtension.rationalScale_valid _ _ (unitCode_valid basis)
  | succ m ih =>
    apply FixedRealExtension.sumList_valid
    intro a ha
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    exact FixedRealExtension.mul_valid _ _ _ (ih _ _) (FixedRealAlphabet.word_valid _ _)

/-- The variable count and substituted generators are fixed source data;
the algorithm is uniform in all dense polynomial degrees and bit lengths. -/
theorem fp_evaluate (m : ℕ) (x : Fin m → E) :
    FP (encoding m) (FixedRealExtension.encoding d e) (evaluate basis m x) := by
  induction m with
  | zero =>
    exact ((fp_id rationalCode).pair (fp_const rationalCode
      (FixedRealExtension.encoding d e) (unitCode basis))).comp
        (FixedRealExtension.fp_rationalScale d e)
  | succ m ih =>
    let ep := encoding m
    let eq := ep.prod BitEncoding.nat
    let ec := FixedRealExtension.encoding d e
    let es := FixedRealAlphabet.symbolEncoding 1
    have hp := fp_fst ep.list eq
    have hq := fp_snd ep.list eq
    have hx := (hq.comp (fp_fst ep BitEncoding.nat)).comp (ih (fun i => x i.succ))
    have hk := hq.comp (fp_snd ep BitEncoding.nat)
    have hword := ((hp.pair hk).comp (ListPrefixMachines.fp_take ep)).comp
      (ListMapMachines.fp_map ep es (fun _ => (0 : Fin 1)) (fp_const ep es 0))
    have hpow := hword.comp
      (FixedRealAlphabet.fp_word (FixedRealAlphabet.data basis (fun _ : Fin 1 => x 0)))
    have hterm := (hx.pair hpow).comp
      (FixedRealExtension.fp_mul d e (FixedRealExtension.multiplicationTable basis))
    have hterms := ((fp_id ep.list).pair (ListIndexMachines.fp_zipIdx ep)).comp
      (ListContextMachines.fp_mapWithContext ep.list eq ec _ hterm)
    exact hterms.comp (FixedRealExtension.fp_sumList d e)

def evalHom : (m : ℕ) → (Fin m → E) → Poly m →+* E
  | 0,_ => (algebraMap (RationalFunction d) E).comp
      ((algebraMap (Poly d) (RationalFunction d)).comp (qHom d))
  | m+1,x => Polynomial.eval₂RingHom (evalHom m (fun i => x i.succ)) (x 0)

private theorem eval_polynomial {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (x : S) (p : List R) :
    (Polynomial.eval₂RingHom f x) (CoefficientListAlgebra.polynomial p) =
      CoefficientListAlgebra.evaluate x (p.map f) := by
  induction p with
  | nil => simp [CoefficientListAlgebra.polynomial, CoefficientListAlgebra.evaluate]
  | cons a p ih =>
    simp only [CoefficientListAlgebra.polynomial, map_add, map_mul,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
      List.map_cons, CoefficientListAlgebra.evaluate_cons]
    rw [← ih]
    rfl

private theorem zipIdx_map {A B : Type} (f : A → B) (p : List A) (k : ℕ) :
    (p.map f).zipIdx k = (p.zipIdx k).map (fun q => (f q.1,q.2)) := by
  induction p generalizing k with
  | nil => rfl
  | cons a p ih => simp [List.zipIdx_cons, ih]

theorem evaluate_value (m : ℕ) (x : Fin m → E) (p : DensePolynomial.Code m) :
    FixedRealExtension.value basis (evaluate basis m x p) = evalHom (d := d) m x (interpret m p) := by
  induction m with
  | zero =>
    rw [evaluate,FixedRealExtension.rationalScale_value,unitCode_value,mul_one]
    exact (eq_ratCast _ p).symm
  | succ m ih =>
    rw [evaluate,FixedRealExtension.value_sumList _ _ (by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
      exact FixedRealExtension.mul_valid _ _ _ (evaluate_valid basis _ _ _) (FixedRealAlphabet.word_valid _ _))]
    change _ = (Polynomial.eval₂RingHom (evalHom (d := d) m (fun i => x i.succ)) (x 0))
      (CoefficientListAlgebra.polynomial (p.map (interpret m)))
    rw [eval_polynomial]
    simp only [CoefficientListAlgebra.evaluate, List.map_map, zipIdx_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    rw [FixedRealExtension.value_mul _ basis (FixedRealExtension.multiplicationTable_realizes basis),
      ih, FixedRealAlphabet.word_value]
    have hk : q.2 < p.length := by simpa only [Nat.zero_add] using List.snd_lt_add_of_mem_zipIdx hq
    simp only [List.map_map, Function.comp_def, List.map_const', List.length_take,
      Nat.min_eq_left hk.le, List.prod_replicate, List.length_replicate]

end PlanarHom.FixedGeneratorEvaluation
