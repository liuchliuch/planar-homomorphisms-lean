import PlanarHom.FixedExtensionSystemRepresented
import PlanarHom.FixedRealExtensionPresentation
import PlanarHom.FiniteRationalCircuits
import PlanarHom.ConditionalMachines

/-! NEW reconstruction: total inversion in a prescribed fixed extension of Q(X).
The nonzero branch executes the genuine one-by-one linear-system machine;
the zero branch returns a valid representation of zero. -/
noncomputable section
namespace PlanarHom.FixedRealExtension
open DensePolynomial Complexity PairProjectionMachines
variable {n e : ℕ}

def isZero (n e : ℕ) (a : Code n e) : Bool :=
  decide (∀i : Fin e, DensePolynomial.isZero n (a.1 i) = true)

theorem fp_isZero (n e : ℕ) : FP (encoding n e) BitEncoding.bool (isZero n e) := by
  have h (i : Fin e) : FP (encoding n e) BitEncoding.bool
      (fun a => DensePolynomial.isZero n (a.1 i)) :=
    ((fp_fst ((DensePolynomial.encoding n).vector e) (DensePolynomial.encoding n)).comp
      (FixedVectorMachines.fp_coordinate (DensePolynomial.encoding n) e i)).comp
        (DensePolynomial.fp_isZero n)
  exact (FiniteRationalCircuits.fp_all (encoding n e) Finset.univ _ h).congr
    (fun a => by simp [isZero])

def inverseSystem (oneCode a : Code n e) : System n e := ([[a]], [oneCode])

def inverse (T : MultiplicationTable n e) (oneCode a : Code n e) : Code n e :=
  if isZero n e a then zeroCode n e
  else (solve T (inverseSystem oneCode a))[0]?.getD (zeroCode n e)

theorem fp_inverse (T : MultiplicationTable n e) (oneCode : Code n e) :
    FP (encoding n e) (encoding n e) (inverse T oneCode) := by
  let ec := encoding n e
  have hs : FP ec ec.list (fun a : Code n e => [a]) :=
    ((fp_id ec).pair (fp_const ec ec.list [])).comp (ListMutationMachines.fp_cons ec)
  have hss : FP ec ec.list.list (fun a : Code n e => [[a]]) :=
    (hs.pair (fp_const ec ec.list.list [])).comp (ListMutationMachines.fp_cons ec.list)
  have hp : FP ec (systemEncoding n e) (inverseSystem oneCode) :=
    hss.pair (fp_const ec ec.list [oneCode])
  have hh := ((fp_const ec BitEncoding.nat 0).pair (hp.comp (fp_solve T))).comp
    (fp_codeLookup ec (zeroCode n e))
  exact ((fp_isZero n e).pair ((fp_const ec ec (zeroCode n e)).pair hh)).comp
    (ConditionalMachines.fp_select ec)

variable {K : Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

theorem isZero_iff (a : Code n e) (ha : Valid n a) :
    isZero n e a = true ↔ value basis a = 0 := by
  have hd : algebraMap (Poly n) (RationalFunction n) (interpret n a.2) ≠ 0 :=
    fun h => ha ((IsFractionRing.to_map_eq_zero_iff).mp h)
  have hc : value basis a = 0 ↔ coordinates n a = 0 := by
    rw [value, LinearEquiv.map_eq_zero_iff]
  rw [hc]
  simp only [isZero, decide_eq_true_eq, DensePolynomial.isZero_iff, funext_iff,
    coordinates, Pi.zero_apply, fractionValue, div_eq_zero_iff, hd, or_false,
    IsFractionRing.to_map_eq_zero_iff]

theorem inverseSystem_valid (oneCode a : Code n e) (h1 : Valid n oneCode)
    (ha : Valid n a) : SystemValid n e (inverseSystem oneCode a) := by
  constructor
  · intro row hr a' ha'
    have hr' : row = [a] := by simpa [inverseSystem] using hr
    subst row
    have he : a' = a := by simpa using ha'
    simpa [he] using ha
  · intro b hb
    have he : b = oneCode := by simpa [inverseSystem] using hb
    simpa [he] using h1

theorem inverseSystem_det (oneCode a : Code n e) :
    (systemMatrix basis (inverseSystem oneCode a)).det = value basis a := by
  rw [Matrix.det_fin_one]
  rfl

theorem inverse_eq_zero (T : MultiplicationTable n e) (oneCode a : Code n e)
    (ha : Valid n a) (hz : value basis a = 0) : inverse T oneCode a = zeroCode n e := by
  simp [inverse, (isZero_iff basis a ha).mpr hz]

theorem inverse_valid (T : MultiplicationTable n e) (hT : T.Realizes basis)
    (oneCode a : Code n e) (h1 : Valid n oneCode) (ha : Valid n a) :
    Valid n (inverse T oneCode a) := by
  by_cases hz : value basis a = 0
  · rw [inverse_eq_zero basis T oneCode a ha hz]
    exact zeroCode_valid n e
  · have hs : isZero n e a ≠ true := fun h => hz ((isZero_iff basis a ha).mp h)
    simp only [inverse, hs, Bool.false_eq_true, ↓reduceIte]
    exact solve_output_valid basis T hT (inverseSystem oneCode a)
      (inverseSystem_valid oneCode a h1 ha)
      (by rwa [inverseSystem_det]) ⟨0, by simp [inverseSystem]⟩

theorem inverse_value (T : MultiplicationTable n e) (hT : T.Realizes basis)
    (oneCode a : Code n e) (h1 : Valid n oneCode) (hv1 : value basis oneCode = 1)
    (ha : Valid n a) : value basis (inverse T oneCode a) = (value basis a)⁻¹ := by
  by_cases hz : value basis a = 0
  · rw [inverse_eq_zero basis T oneCode a ha hz, zeroCode_value, hz, inv_zero]
  · have hs : isZero n e a ≠ true := fun h => hz ((isZero_iff basis a ha).mp h)
    have hh := congrFun (solve_correct basis T hT (inverseSystem oneCode a)
      (inverseSystem_valid oneCode a h1 ha) (by rwa [inverseSystem_det]))
      (⟨0, by simp [inverseSystem]⟩ : Fin (inverseSystem oneCode a).1.length)
    have hh' : value basis a * value basis ((solve T (inverseSystem oneCode a))[0]?.getD
        (zeroCode n e)) = 1 := by
      simpa [Matrix.mulVec, dotProduct, systemMatrix, systemVector, inverseSystem,
        systemEntry, systemRhs, hv1] using hh
    simp only [inverse, hs, Bool.false_eq_true, ↓reduceIte]
    exact mul_left_cancel₀ hz (hh'.trans (mul_inv_cancel₀ hz).symm)

end PlanarHom.FixedRealExtension
