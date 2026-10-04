import PlanarHom.FixedRealListSum
import PlanarHom.FixedRealRationalScaling

/-! Genuine polynomial-bit evaluation of a dynamic rational coefficient list at
one fixed extension element. Powers use the bounded fixed-alphabet machine;
all rational multiples are combined through one shared-denominator list sum. -/
noncomputable section
namespace PlanarHom.FixedRealCoefficientEvaluation
open DensePolynomial Complexity PairProjectionMachines FixedRealExtension
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

def power (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) (k:ℕ) : FixedRealExtension.Code n e :=
  FixedRealAlphabet.word (FixedRealAlphabet.data basis (fun _:Fin 1=>ρ)) (List.replicate k 0)

theorem power_valid (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) (k:ℕ) :
    FixedRealExtension.Valid n (power basis ρ k) := FixedRealAlphabet.word_valid _ _

theorem power_value (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) (k:ℕ) :
    FixedRealExtension.value basis (power basis ρ k)=ρ^k := by
  rw [power,FixedRealAlphabet.word_value]
  simp

theorem fp_power (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) :
    FP BitEncoding.unaryNat (FixedRealExtension.encoding n e) (power basis ρ) := by
  let es:=FixedRealAlphabet.symbolEncoding 1
  have hr:=((fp_id BitEncoding.unaryNat).pair (fp_const BitEncoding.unaryNat es (0:Fin 1))).comp
    (RuntimePolynomialEvaluationMachines.fp_replicate es)
  exact hr.comp (FixedRealAlphabet.fp_word (FixedRealAlphabet.data basis (fun _:Fin 1=>ρ)))

def evaluate (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) (cs:List ℚ) : FixedRealExtension.Code n e :=
  sumList n e (cs.zipIdx.map (fun q=>rationalScale n q.1 (power basis ρ q.2)))

def cappedTerm (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) (p:ℕ×(ℚ×ℕ)) : FixedRealExtension.Code n e :=
  rationalScale n p.2.1 (power basis ρ (min p.1 p.2.2))

theorem fp_cappedTerm (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) :
    FP (BitEncoding.unaryNat.prod (rationalCode.prod BitEncoding.nat)) (FixedRealExtension.encoding n e)
      (cappedTerm basis ρ) := by
  let ei:=BitEncoding.unaryNat.prod (rationalCode.prod BitEncoding.nat)
  have hp:=fp_snd BitEncoding.unaryNat (rationalCode.prod BitEncoding.nat)
  have hq:=hp.comp (fp_fst rationalCode BitEncoding.nat)
  have hk:=hp.comp (fp_snd rationalCode BitEncoding.nat)
  have hm:=((fp_fst BitEncoding.unaryNat (rationalCode.prod BitEncoding.nat)).pair hk).comp
    (show FP (BitEncoding.unaryNat.prod BitEncoding.nat) BitEncoding.unaryNat
      (fun p=>min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
  exact (hq.pair (hm.comp (fp_power basis ρ))).comp (fp_rationalScale n e)

theorem fp_evaluate (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) :
    FP rationalCode.list (FixedRealExtension.encoding n e) (evaluate basis ρ) := by
  have hn:=ListUnaryLengthMachine.fp_length rationalCode
  have hz:=ListIndexMachines.fp_zipIdx rationalCode
  have hm:=(hn.pair hz).comp (ListContextMachines.fp_mapWithContext BitEncoding.unaryNat
    (rationalCode.prod BitEncoding.nat) (FixedRealExtension.encoding n e) _ (fp_cappedTerm basis ρ))
  apply (hm.comp (fp_sumList n e)).congr
  intro cs
  change sumList n e (cs.zipIdx.map (fun q=>cappedTerm basis ρ (cs.length,q)))=evaluate basis ρ cs
  unfold evaluate
  congr 1
  apply List.map_congr_left
  intro q hq
  have hi:q.2<cs.length:=by simpa using List.snd_lt_of_mem_zipIdx hq
  simp only [cappedTerm,min_eq_right (Nat.le_of_lt hi)]

theorem evaluate_valid (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) (cs:List ℚ) :
    FixedRealExtension.Valid n (evaluate basis ρ cs) := by
  apply sumList_valid
  intro a ha
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp ha
  exact rationalScale_valid _ _ (power_valid basis ρ q.2)

theorem evaluate_value (basis:Module.Basis (Fin e) (RationalFunction n) K) (ρ:K) (cs:List ℚ) :
    FixedRealExtension.value basis (evaluate basis ρ cs)=
      (cs.zipIdx.map (fun q=>(q.1:K)*ρ^q.2)).sum := by
  rw [evaluate,value_sumList]
  · simp only [List.map_map,Function.comp_def,rationalScale_value,power_value]
  · intro a ha
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp ha
    exact rationalScale_valid _ _ (power_valid basis ρ q.2)

/-- Compatibility with any prescribed rational embedding. No numerical
approximation or sign information is needed at evaluation time. -/
theorem evaluate_coefficients (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (f:ℚ→+*K) (ρ:K) (cs:List ℚ) :
    FixedRealExtension.value basis (evaluate basis ρ cs)=
      CoefficientListAlgebra.evaluate ρ (cs.map f) := by
  rw [evaluate_value]
  simp only [CoefficientListAlgebra.evaluate,List.zipIdx_map,List.map_map,Function.comp_def,Prod.map_fst,Prod.map_snd,id_eq,eq_ratCast]

theorem evaluate_inFP (basis:Module.Basis (Fin e) (RationalFunction n) K) (f:ℚ→+*K) (ρ:K) :
    ((FixedRealExtension.presentation basis).problem rationalCode.list (fun _=>True)
      (fun cs=>CoefficientListAlgebra.evaluate ρ (cs.map f))).InFP :=
  RepresentedBit.Presentation.problem_inFP _ _
    (BitEncoding.listNormalizer (DensePolynomial.normalizer 0)) _ _
    (evaluate basis ρ) (fp_evaluate basis ρ) (fun cs _=>evaluate_valid basis ρ cs)
    (fun cs _=>evaluate_coefficients basis f ρ cs)

end PlanarHom.FixedRealCoefficientEvaluation
