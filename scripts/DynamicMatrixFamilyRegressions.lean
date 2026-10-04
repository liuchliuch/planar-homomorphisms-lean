import PlanarHom.DynamicMatrixFamilyReduction

open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases

-- Bounds are computed in unary by actual machines, including mixed degrees.
example : FP BitEncoding.unaryNat BitEncoding.unaryNat
    (fun n => (3 : ℕ) * (n+1)^4 + 7) := by
  exact (UnaryPolynomialMachines.fp_eval
    (Polynomial.C 3 * (Polynomial.X + 1)^4 + Polynomial.C 7)).congr (fun n => by simp)

-- The source simulation alone yields the required uniform raw answer-size bound.
example {source base : PromiseProblem} (r : PromisePolyTimeTuringReduction source base)
    (raw : Bits) (h : source.valid raw) :
    (source.value raw).length ≤ r.outputPolynomial.eval raw.length := r.output_length_bound raw h

-- Every successful alternate decoding retains the exact field output presentation.
example {K : Type} [Field K] [Algebra ℚ K] {dimension q bt ut : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (raw : Bits) (p : ℕ × MixedCode)
    (h : DynamicMatrixFamilySource.queryEncoding.decode raw = some p) :
    (DynamicMatrixFamilySource.problem basis M U w F).value raw =
      (numberFieldEncoding basis).encode (DynamicMatrixFamilySource.answer M U w F p) := by
  simp [DynamicMatrixFamilySource.problem, encodedFunction, h]

-- Full caller interface: fixed field, actual evaluator, finite compatibility at
-- every current length (including zero), and one original source simulation.
example {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
    {dimension q bt ut : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (B : Matrix (Fin q) (Fin q) K)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (c : Polynomial ℕ)
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ m, ∃ j < c.eval m,
      ExponentProductTables.CompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet B) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (DynamicMatrixFamilySource.problem basis M U w F) base) :
    Nonempty (PromisePolyTimeTuringReduction (evaluationProblem basis (appendOne M B) U w) base) :=
  ⟨DynamicMatrixFamilyReduction.reduction basis M U w F B n₀ hn₀ c hF hNonzero hSample base simulation⟩
