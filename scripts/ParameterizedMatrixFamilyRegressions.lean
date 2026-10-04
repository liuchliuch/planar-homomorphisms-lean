import PlanarHom.ParameterizedMatrixFamilyReduction

open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases

-- Any original successful raw graph word is accepted with its exact parameter word.
example {X K : Type} [Field K] [Algebra ℚ K] {dimension q bt ut : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (B : X → Matrix (Fin q) (Fin q) K) (allowed : X → Prop)
    (x : X) (hx : allowed x) (rawGraph : Bits) (g : MixedCode)
    (hd : MixedCode.encoding.decode rawGraph = some g) (hg : g.PlanarValid (bt+1) ut) :
    (ParameterizedMatrixEvaluation.problem basis ex M U w B allowed).valid
      (BitEncoding.frame (ex.encode x) ++ rawGraph) :=
  (ParameterizedMatrixEvaluation.valid_iff_rawGraph basis ex M U w B allowed _).mpr
    ⟨x,rawGraph,rfl,hx,g,hd,hg⟩

-- Optional normalization changes only the parameter representation.
example {X : Type} (ex : BitEncoding X) (h : BitEncoding.Normalizer ex) :
    FP ((BitEncoding.ValidWord.encoding ex).prod (BitEncoding.ValidWord.encoding MixedCode.encoding))
      (ParameterizedMatrixEvaluation.inputEncoding ex) (fun p => (p.1.value,p.2)) :=
  ParameterizedMatrixEvaluation.fp_normalize_parameter ex h

-- No parameter normalizer premise is required by the uniform fixed-field endpoint.
example {X K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
    {dimension q bt ut : ℕ} (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (B : X → Matrix (Fin q) (Fin q) K) (allowed : X → Prop)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (c : Polynomial ℕ)
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hB : FP ex ((numberFieldEncoding basis).vector (q*q)) (fun x => binaryAlphabet (B x)))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ x, allowed x → ∀ m, ∃ j < c.eval m,
      ExponentProductTables.CompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet (B x)) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (DynamicMatrixFamilySource.problem basis M U w F) base) :
    Nonempty (PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ex M U w B allowed) base) :=
  ⟨ParameterizedMatrixFamilyReduction.reduction basis ex M U w F B allowed n₀ hn₀ c hF hB
    hNonzero hSample base simulation⟩
