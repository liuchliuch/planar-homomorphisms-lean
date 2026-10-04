import PlanarHom.SurfaceCharacterSemantics

/-! NEW exact list-to-Fourier identity for the total evaluator, with an
explicit bound on its two families of Pfaffian calls. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceFKT
open SurfaceBooleanRows SurfaceBooleanGauss
variable {K : Type} [Field K] [DecidableEq K]

theorem reciprocalDimension_eq (p : Prepared K) :
    reciprocalDimension p=((2:K)^p.quotient.2.length)⁻¹ := by
  simp [reciprocalDimension,List.map_const',List.prod_replicate,inv_pow]

theorem walsh_calibrationTable (ambient : ℕ) (p : Prepared K)
    (hbound : p.quotient.2.length≤2*ambient) (u : Bits p.quotient.2.length) :
    walsh (calibrationTable ambient p) (List.ofFn u)=
      SurfaceBooleanGauss.walsh (fun x => calibration p (List.ofFn x)) u := by
  unfold walsh calibrationTable characters
  rw [List.map_map,sum_boundedWords (2*ambient) p.quotient.2.length hbound]
  unfold SurfaceBooleanGauss.walsh
  apply Finset.sum_congr rfl
  intro x _
  simp only [Function.comp_apply,characterValue_ofFn_ofFn]

theorem matchingValue_eq_fourier (ambient : ℕ) (p : Prepared K)
    (hbound : p.quotient.2.length≤2*ambient) :
    matchingValue ambient p=((2:K)^p.quotient.2.length)⁻¹*
      ∑u:Bits p.quotient.2.length,
        SurfaceBooleanGauss.walsh (fun x => calibration p (List.ofFn x)) u*
          twistedEvaluation p (List.ofFn u) := by
  rw [matchingValue,reciprocalDimension_eq]
  congr 1
  simp only [calibrationTable,List.map_map,Function.comp_apply]
  change ((characters ambient p).map (fun x =>
    walsh (calibrationTable ambient p) x*twistedEvaluation p x)).sum=_
  rw [characters,sum_boundedWords (2*ambient) p.quotient.2.length hbound]
  apply Finset.sum_congr rfl
  intro u _
  rw [walsh_calibrationTable ambient p hbound]

theorem matchingValue_invalid_rank (ambient : ℕ) (p : Prepared K)
    (hbound : ¬p.quotient.2.length≤2*ambient) : matchingValue ambient p=0 := by
  simp [matchingValue,calibrationTable,characters,boundedWords_eq,hbound]

theorem calibrationTable_length_le (ambient : ℕ) (p : Prepared K) :
    (calibrationTable ambient p).length≤4^ambient := by
  have h := boundedWords_size (2*ambient) p.quotient.2.length
  simpa [calibrationTable,characters,pow_mul] using h

theorem totalPfaffianCalls_le (ambient : ℕ) (p : Prepared K) :
    (calibrationTable ambient p).length+(calibrationTable ambient p).length≤2*4^ambient := by
  have h := calibrationTable_length_le ambient p
  omega

end PlanarHom.SurfaceFKT
