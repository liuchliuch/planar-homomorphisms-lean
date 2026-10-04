import PlanarHom.FinishedDependentMatrixFamilyReduction
import PlanarHom.VariableDomainEffectiveTransfer

open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.PrescribedDomains

-- Every source value round-trips for every bounded-degree target field.
example {L X : Type} [Field L] [Algebra ℚ L]
    {d : ℕ} (bL : Module.Basis (Fin d) ℚ L)
    (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
    (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
    (inclusion : ∀ x, L →+* K x) (c : ℕ) (hc : ∀ x, dimension x ≤ c) (x : X) (a : L) :
    DependentFieldOutputDescent.descend bL K dimension basis inclusion c ⟨x,inclusion x a⟩ = a :=
  DependentFieldOutputDescent.descend_inclusion bL K dimension basis inclusion c hc x a

-- The only machine premise is the inclusion already supplied by source (b).
-- No arithmetic, height, presentation, matrix inverse, or conversion oracle is added.
example {L X : Type} [Field L] [Algebra ℚ L]
    {d : ℕ} (bL : Module.Basis (Fin d) ℚ L) (ex : BitEncoding X)
    (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
    (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
    (inclusion : ∀ x, L →+* K x) (c : ℕ)
    (hinclusion : FP (ex.prod (numberFieldEncoding bL))
      (DependentFieldCodecs.sigma ex (fun x => numberFieldEncoding (basis x)))
      (fun p => ⟨p.1,inclusion p.1 p.2⟩)) :
    FP (DependentFieldCodecs.sigma ex (fun x => numberFieldEncoding (basis x)))
      (numberFieldEncoding bL) (DependentFieldOutputDescent.descend bL K dimension basis inclusion c) :=
  DependentFieldOutputDescent.fp_descend bL ex K dimension basis inclusion c hinclusion

-- Exact encoded domain records are admitted under their original raw graph words.
example {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
    (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)] [∀ x, DecidableEq (K x)]
    (ex : BitEncoding X) (dimension : X → ℕ)
    (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x)) (inclusion : ∀ x, L →+* K x)
    {q bt ut dt : ℕ}
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (D : Fin dt → Set (Fin q)) (policy : Fin (bt+1) → Fin dt → Fin dt → Prop)
    (typing : Fin ut → Fin dt → Prop)
    (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop)
    (x : X) (hx : allowed x) (raw : Bits) (hraw : EncodedInput policy typing raw) :
    (DependentDomainMatrixFamilyReduction.targetProblem K ex dimension basis inclusion M U w D policy typing B allowed).valid
      (BitEncoding.frame (ex.encode x) ++ raw) :=
  (DependentDomainMatrixFamilyReduction.valid_iff_rawGraph K ex dimension basis inclusion M U w D policy typing B allowed _).mpr
    ⟨x,raw,rfl,hx,hraw⟩

-- Mapping the field retains the exact intrinsic 0/1 indicator for every original domain.
example {L R : Type} [Field L] [Field R] (φ : L →+* R) {q : ℕ} (D : Set (Fin q)) (i : Fin q) :
    φ (indicator (R := L) D i) = indicator (R := R) D i := map_indicator φ D i

-- The full descended caller has no output-codec, finish-machine, or descent-oracle premise.
example {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
    (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)] [∀ x, DecidableEq (K x)]
    {sourceDimension q bt ut : ℕ}
    (sourceBasis : Module.Basis (Fin sourceDimension) ℚ L) (ex : BitEncoding X)
    (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
    (inclusion : ∀ x, L →+* K x)
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (F : ℕ → Matrix (Fin q) (Fin q) L) (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop)
    (H : MixedCode → Prop) (hvalid : ∀ g, H g → g.Valid (bt+1) ut)
    (hparallel : ∀ g, H g → ∀ s, H (g.parallelLabel bt s))
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (candidates : Polynomial ℕ)
    (degreeBound : ℕ) (degree_le : ∀ x, dimension x ≤ degreeBound)
    (hpresentation : FP ex BitEncoding.rat.list
      (fun x => UniformFieldPresentationHeights.presentationList (basis x)))
    (hmul : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩))
    (hadd : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1+s.2.2⟩))
    (hinclusion : FP (ex.prod (numberFieldEncoding sourceBasis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun p => ⟨p.1,inclusion p.1 p.2⟩))
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding sourceBasis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hB : FP ex (DependentFieldCodecs.sigma ex
      (fun x => (DependentFieldListMachines.fieldEncoding K dimension basis x).vector (q*q)))
      (fun x => ⟨x,binaryAlphabet (B x)⟩))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ x, allowed x → ∀ m, ∃ j < candidates.eval m,
      SourceExponentRepresentatives.CrossCompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet (B x)) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (RestrictedMatrixFamilyReduction.sourceProblem sourceBasis M U w F H) base) :
    Nonempty (PromisePolyTimeTuringReduction
      (FinishedDependentMatrixFamilyReduction.targetProblem K sourceBasis ex
        (DependentFieldOutputDescent.descend sourceBasis K dimension basis inclusion degreeBound)
        inclusion M U w B allowed H) base) :=
  ⟨FinishedDependentMatrixFamilyReduction.descendedReduction K sourceBasis ex dimension basis inclusion
    M U w F B allowed H hvalid hparallel n₀ hn₀ candidates degreeBound degree_le
    hpresentation hmul hadd hinclusion hF hB hNonzero hSample base simulation⟩
