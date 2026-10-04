import PlanarHom.DependentMatrixFamilyReduction

open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases

-- The empty-product row is retained, so marked length zero is handled by the same program.
example : SourceExponentRepresentatives.representatives (fun _ : Fin 1 => (2 : ℚ)) 0 = [(1,[0])] := by
  norm_num [SourceExponentRepresentatives.representatives, SourceExponentRepresentatives.nonzeroProducts,
    SourceExponentRepresentatives.products, ExponentVectors.weak, ExponentVectors.box, List.range_succ, List.range_zero,
    ExponentProductSemantics.value, ListDedupMachines.dedupByFirst, ListDedupMachines.dedup,
    ListDedupMachines.step, Fin.prod_univ_succ, CrossFieldCollisionMachines.test,
    ContextPairTestMachines.anyPair, CrossFieldCollisionMachines.bad]

-- A numerical collision keeps the first original exponent list.
example : SourceExponentRepresentatives.representatives (fun _ : Fin 2 => (2 : ℚ)) 1 = [(2,[1,0])] := by
  norm_num [SourceExponentRepresentatives.representatives, SourceExponentRepresentatives.nonzeroProducts,
    SourceExponentRepresentatives.products, ExponentVectors.weak, ExponentVectors.box, List.range_succ, List.range_zero,
    ExponentProductSemantics.value, ListDedupMachines.dedupByFirst, ListDedupMachines.dedup,
    ListDedupMachines.step, Fin.prod_univ_succ, CrossFieldCollisionMachines.test,
    ContextPairTestMachines.anyPair, CrossFieldCollisionMachines.bad]

-- Zero source products are discarded before selecting source-key representatives.
example : SourceExponentRepresentatives.representatives (fun _ : Fin 1 => (0 : ℚ)) 1 = [] := by
  norm_num [SourceExponentRepresentatives.representatives, SourceExponentRepresentatives.nonzeroProducts,
    SourceExponentRepresentatives.products, ExponentVectors.weak, ExponentVectors.box, List.range_succ, List.range_zero,
    ExponentProductSemantics.value, ListDedupMachines.dedupByFirst, ListDedupMachines.dedup,
    ListDedupMachines.step, Fin.prod_univ_succ, CrossFieldCollisionMachines.test,
    ContextPairTestMachines.anyPair, CrossFieldCollisionMachines.bad]

-- A conflicting target assignment is rejected by the actual finite all-pairs test.
example : CrossFieldCollisionMachines.test (fun _ : Unit => ℚ)
    (fun _ => ![(3 : ℚ),4]) (((),1),fun _ : Fin 2 => (2 : ℚ)) = false := by
  norm_num [SourceExponentRepresentatives.representatives, SourceExponentRepresentatives.nonzeroProducts,
    SourceExponentRepresentatives.products, ExponentVectors.weak, ExponentVectors.box, List.range_succ, List.range_zero,
    ExponentProductSemantics.value, ListDedupMachines.dedupByFirst, ListDedupMachines.dedup,
    ListDedupMachines.step, Fin.prod_univ_succ, CrossFieldCollisionMachines.test,
    ContextPairTestMachines.anyPair, CrossFieldCollisionMachines.bad]

-- Total recovery agrees with the exact cross-field semantics on every honest table.
example {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
    (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
    (φ : ∀ x, L →+* K x) {t : ℕ} (B : ∀ x, Fin t → K x)
    (x : X) (m : ℕ) (A : Fin t → L) (answers : List L) :
    DependentTargetAggregation.recover K φ B ((x,m),(SourceExponentRepresentatives.representatives A m,answers)) =
      ⟨x,CrossFieldInterpolationSemantics.aggregate (φ x) (B x)
        (SourceExponentRepresentatives.representatives A m) answers⟩ :=
  DependentTargetAggregation.recover_representatives K φ B x m A answers

-- Raw graph representations remain valid, while the runtime parameter uses its exact code.
example {L X : Type} [Field L] (K : X → Type) [∀ x, Field (K x)]
    (ex : BitEncoding X) (out : ∀ x, BitEncoding (K x)) (φ : ∀ x, L →+* K x)
    {q bt ut : ℕ} (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop)
    (x : X) (hx : allowed x) (raw : Bits) (g : MixedCode)
    (hd : MixedCode.encoding.decode raw = some g) (hg : g.PlanarValid (bt+1) ut) :
    (DependentMatrixEvaluation.problem K ex out φ M U w B allowed).valid (BitEncoding.frame (ex.encode x) ++ raw) :=
  (DependentMatrixEvaluation.valid_iff_rawGraph K ex out φ M U w B allowed _).mpr
    ⟨x,raw,rfl,hx,g,hd,hg⟩

-- Canonical target output conversion is an actual framing projection, with no extra advice.
example {X : Type} (ex : BitEncoding X) (K : X → Type)
    [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
    (d : X → ℕ) (b : ∀ x, Module.Basis (Fin (d x)) ℚ (K x)) :
    FP (DependentFieldCodecs.sigma ex (fun x => numberFieldEncoding (b x))) BitEncoding.bits
      (fun s : Σ x, K x => (numberFieldEncoding (b s.1)).encode s.2) :=
  DependentEncodingMachines.fp_payload ex (fun x => numberFieldEncoding (b x))

-- The complete varying-field endpoint has no target output-conversion or height advice premise.
example {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
    (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)] [∀ x, DecidableEq (K x)]
    {sourceDimension q bt ut : ℕ}
    (sourceBasis : Module.Basis (Fin sourceDimension) ℚ L) (ex : BitEncoding X)
    (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
    (inclusion : ∀ x, L →+* K x)
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (F : ℕ → Matrix (Fin q) (Fin q) L) (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop)
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
    (simulation : PromisePolyTimeTuringReduction (DynamicMatrixFamilySource.problem sourceBasis M U w F) base) :
    Nonempty (PromisePolyTimeTuringReduction
      (DependentMatrixEvaluation.problem K ex (fun x => numberFieldEncoding (basis x)) inclusion M U w B allowed) base) :=
  ⟨DependentMatrixFamilyReduction.canonicalReduction K sourceBasis ex dimension basis inclusion M U w F B allowed
    n₀ hn₀ candidates degreeBound degree_le hpresentation hmul hadd hinclusion hF hB hNonzero hSample base simulation⟩
