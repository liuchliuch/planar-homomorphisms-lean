import Audit.ReviewedStatements

/-! Fixed official Comparator challenge. Placeholders specify goals and are
excluded from the proof library and its axiom audit. -/
noncomputable section
open scoped BigOperators Classical
open PlanarHom.AlgebraicProductInterpolation PlanarHom.Complexity PlanarHom.Structures
open PlanarHom.DomainDoublingClassification
universe u_1 u_2
namespace PlanarHomAudit.Comparator

theorem theorem11 :
  (∀ {q : ℕ} (L : RealLanguage q 1 0),
    (∀ i, L.weights i = 1) →
    (∀ i j, L.matrices 0 i j = L.matrices 0 j i) →
    (∀ i j, 0 ≤ L.matrices 0 i j) →
    (NonnegativeClass (L.matrices 0) → L.problem.InFP) ∧
    (¬NonnegativeClass (L.matrices 0) → PromisedSharpPHard L.problem)) := by
  sorry

theorem theorem13 :
  (∀ {q : ℕ} (L : RealLanguage q 1 0)
    (hs : ∀ i j, L.matrices 0 i j = L.matrices 0 j i),
    (∀ i j, 0 ≤ L.matrices 0 i j) → (∀ i, 0 < L.weights i) →
    (PositiveVertexWeightClass (L.matrices 0) L.weights hs → L.problem.InFP) ∧
    (¬PositiveVertexWeightClass (L.matrices 0) L.weights hs → PromisedSharpPHard L.problem)) := by
  sorry

theorem corollary122_rectangular :
  (∀ {x y : ℕ} (V : Matrix (Fin x) (Fin y) ℝ)
    (μ : Fin x → ℝ) (ν : Fin y → ℝ)
    (hV : ∀ i j, IsAlgebraic ℚ (V i j))
    (hμ : ∀ i, IsAlgebraic ℚ (μ i)) (hν : ∀ i, IsAlgebraic ℚ (ν i)),
    (∀ i j, 0 ≤ V i j) → (∀ i, 0 < μ i) → (∀ i, 0 < ν i) →
    let L := rectangularLanguage V μ ν hV hμ hν
    (PositiveVertexWeightClass (rectangularMatrix V) L.weights (rectangular_symm V) →
      (prescribedProblem L rectangularSide).InFP) ∧
    (¬PositiveVertexWeightClass (rectangularMatrix V) L.weights (rectangular_symm V) →
      PromisedSharpPHard (prescribedProblem L rectangularSide))) := by
  sorry

/-- Paper item 1.1. -/
noncomputable def item_1_1_1 :
  (∀ {q : ℕ} (L : RealLanguage q 1 0),
    (∀ i, L.weights i = 1) →
    (∀ i j, L.matrices 0 i j = L.matrices 0 j i) →
    (∀ i j, 0 ≤ L.matrices 0 i j) →
    (NonnegativeClass (L.matrices 0) → L.problem.InFP) ∧
    (¬NonnegativeClass (L.matrices 0) → PromisedSharpPHard L.problem)) :=
  sorry

/-- Paper item 1.3. -/
noncomputable def item_1_3_1 :
  (∀ {q : ℕ} (L : RealLanguage q 1 0)
    (hs : ∀ i j, L.matrices 0 i j = L.matrices 0 j i),
    (∀ i j, 0 ≤ L.matrices 0 i j) → (∀ i, 0 < L.weights i) →
    (PositiveVertexWeightClass (L.matrices 0) L.weights hs → L.problem.InFP) ∧
    (¬PositiveVertexWeightClass (L.matrices 0) L.weights hs → PromisedSharpPHard L.problem)) :=
  sorry

/-- Paper item 2.2. -/
noncomputable def item_2_2_1 :
  (∀ (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage 2 1 0),
    (∀ (i : Fin 2), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      (∀ (i j : Fin 2),
          Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
        (∀ (i j : Fin 2), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
          And
            (Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 0 0)
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 1 1) →
              PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
            (IsUnit.{0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) →
              Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 0 0)
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 1 1) →
                PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))) :=
  sorry

/-- Paper item 2.2. -/
noncomputable def item_2_2_2 :
  (∀ (q : Nat),
    LE.le.{0} 3 q →
      PlanarHom.Complexity.PromisedSharpPHard
        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.pottsRationalProblem q)) :=
  sorry

/-- Paper item 2.3. -/
noncomputable def item_2_3_1 :
  (∀ {n e : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin 3) (Fin 3) K),
    (∀ (i j : Fin 3), Eq.{1} (M i j) (M j i)) →
      And
        ((PlanarHom.SignedThreeState.ThreeStateEasy fun (i j : Fin 3) => φ (M i j)) →
          PlanarHom.RepresentedBit.Problem.InFP
            (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
              (fun (l : Fin 0) => Fin.elim0.{1} l) fun (x : Fin 3) => 1))
        (Not (PlanarHom.SignedThreeState.ThreeStateEasy fun (i j : Fin 3) => φ (M i j)) →
          PlanarHom.RepresentedBit.SharpPHard
            (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
              (fun (l : Fin 0) => Fin.elim0.{1} l) fun (x : Fin 3) => 1))) :=
  sorry

/-- Paper item 2.4. -/
noncomputable def item_2_4_1 :
  (∀ {n e : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin 4) (Fin 4) K),
    (∀ (i j : Fin 4), Eq.{1} (M i j) (M j i)) →
      (∀ (i j : Fin 4), LE.le.{0} 0 (φ (M i j))) →
        Eq.{1} (Matrix.rank.{0, 0, 0} fun (i j : Fin 4) => φ (M i j)) 4 →
          And
            ((PlanarHom.RankFour.FourStateClass fun (i j : Fin 4) => φ (M i j)) →
              PlanarHom.RepresentedBit.Problem.InFP
                (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                  (fun (l : Fin 0) => Fin.elim0.{1} l) fun (x : Fin 4) => 1))
            (Not (PlanarHom.RankFour.FourStateClass fun (i j : Fin 4) => φ (M i j)) →
              PlanarHom.RepresentedBit.SharpPHard
                (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                  (fun (l : Fin 0) => Fin.elim0.{1} l) fun (x : Fin 4) => 1))) :=
  sorry

/-- Paper item 2.4. -/
noncomputable def item_2_4_2 :
  (∀ {n e : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin 4) (Fin 4) K),
    (∀ (i j : Fin 4), Eq.{1} (M i j) (M j i)) →
      (∀ (i j : Fin 4), LT.lt.{0} 0 (φ (M i j))) →
        Eq.{1} (Matrix.rank.{0, 0, 0} fun (i j : Fin 4) => φ (M i j)) 4 →
          And
            ((PlanarHom.RankFour.PositiveFourTensor fun (i j : Fin 4) => φ (M i j)) →
              PlanarHom.RepresentedBit.Problem.InFP
                (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                  (fun (l : Fin 0) => Fin.elim0.{1} l) fun (x : Fin 4) => 1))
            (Not (PlanarHom.RankFour.PositiveFourTensor fun (i j : Fin 4) => φ (M i j)) →
              PlanarHom.RepresentedBit.SharpPHard
                (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                  (fun (l : Fin 0) => Fin.elim0.{1} l) fun (x : Fin 4) => 1))) :=
  sorry

/-- Paper item 2.5. -/
noncomputable def item_2_5_1 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0),
    (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      ∀
        (hs :
          ∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)),
        (∀ (i j : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
          And
            ((∀ (i j : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
              (Function.Injective.{1, 1} fun (i : Fin q) =>
                  PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i i) →
                And
                  (Eq.{1} (Matrix.rank.{0, 0, 0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)) 1 →
                    PlanarHom.Complexity.PromiseProblem.InFP
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
                  (LT.lt.{0} 1
                      (Matrix.rank.{0, 0, 0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)) →
                    PlanarHom.Complexity.PromisedSharpPHard
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)))
            (PlanarHom.GadgetDiagonalSeparation.Separates
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) →
              And
                (PlanarHom.GadgetDiagonalSeparation.SupportRankCondition
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) hs →
                  PlanarHom.Complexity.PromiseProblem.InFP
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
                (Not
                    (PlanarHom.GadgetDiagonalSeparation.SupportRankCondition
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) hs) →
                  PlanarHom.Complexity.PromisedSharpPHard
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)))) :=
  sorry

/-- Paper item 2.6. -/
noncomputable def item_2_6_1 :
  (∀ {q r : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0),
    (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      (∀ (i j : Fin q),
          Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
        ∀ (block : Fin q → Fin r),
          (∀ (i j : Fin q),
              Ne.{1} (block i) (block j) →
                Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 0) →
            (∀ (b : Fin r),
                PlanarHom.TractableBlockComposition.Form fun (i j : Subtype.{1} fun (i : Fin q) => Eq.{1} (block i) b) =>
                  PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 ↑i ↑j) →
              PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)) :=
  sorry

/-- Paper item 3.1. -/
noncomputable def item_3_1_1 :
  ({q bt ut : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut) →
      (N : Matrix.{0, 0, 0} (Fin q) (Fin q) Real) →
        (hN : ∀ (i j : Fin q), IsAlgebraic.{0, 0} Rat (N i j)) →
          (old : Fin bt) →
            (∀ (i j : Fin q),
                Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i j) 0 → Eq.{1} (N i j) 0) →
              (PlanarHom.ProductCompatibility.HasProductMaps
                  (fun (p : Prod.{0, 0} (Fin q) (Fin q)) =>
                    PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old p.1 p.2)
                  fun (p : Prod.{0, 0} (Fin q) (Fin q)) => N p.1 p.2) →
                (base : PlanarHom.Complexity.PromiseProblem) →
                  PlanarHom.Complexity.PromisePolyTimeTuringReduction
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) base →
                    PlanarHom.Complexity.PromisePolyTimeTuringReduction
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.binaryTargetProblem L N hN) base) :=
  sorry

/-- Paper item 3.1. -/
noncomputable def item_3_1_2 :
  ({q bt ut : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut) →
      (N : Fin q → Real) →
        (hN : ∀ (i : Fin q), IsAlgebraic.{0, 0} Rat (N i)) →
          (old : Fin ut) →
            (∀ (i : Fin q),
                Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unaries L old i) 0 → Eq.{1} (N i) 0) →
              PlanarHom.ProductCompatibility.HasProductMaps
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unaries L old) N →
                (base : PlanarHom.Complexity.PromiseProblem) →
                  PlanarHom.Complexity.PromisePolyTimeTuringReduction
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) base →
                    PlanarHom.Complexity.PromisePolyTimeTuringReduction
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unaryTargetProblem L N hN) base) :=
  sorry

/-- Paper item 3.1. -/
noncomputable def item_3_1_3 :
  ({q bt ut dt : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut) →
      (D : Fin dt → Set.{0} (Fin q)) →
        (B : Fin bt → Fin dt → Fin dt → Prop) →
          (T : Fin ut → Fin dt → Prop) →
            (N : Matrix.{0, 0, 0} (Fin q) (Fin q) Real) →
              (hN : ∀ (i j : Fin q), IsAlgebraic.{0, 0} Rat (N i j)) →
                (old : Fin bt) →
                  (∀ (i j : Fin q),
                      Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i j) 0 →
                        Eq.{1} (N i j) 0) →
                    (PlanarHom.ProductCompatibility.HasProductMaps
                        (fun (p : Prod.{0, 0} (Fin q) (Fin q)) =>
                          PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old p.1 p.2)
                        fun (p : Prod.{0, 0} (Fin q) (Fin q)) => N p.1 p.2) →
                      (base : PlanarHom.Complexity.PromiseProblem) →
                        PlanarHom.Complexity.PromisePolyTimeTuringReduction
                            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.domainProblem L D B T) base →
                          PlanarHom.Complexity.PromisePolyTimeTuringReduction
                            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.domainBinaryTargetProblem L D B T N hN
                              old)
                            base) :=
  sorry

/-- Paper item 3.1. -/
noncomputable def item_3_1_4 :
  ({q bt ut dt : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut) →
      (D : Fin dt → Set.{0} (Fin q)) →
        (B : Fin bt → Fin dt → Fin dt → Prop) →
          (T : Fin ut → Fin dt → Prop) →
            (N : Fin q → Real) →
              (hN : ∀ (i : Fin q), IsAlgebraic.{0, 0} Rat (N i)) →
                (old : Fin ut) →
                  (∀ (i : Fin q),
                      Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unaries L old i) 0 → Eq.{1} (N i) 0) →
                    PlanarHom.ProductCompatibility.HasProductMaps
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unaries L old) N →
                      (base : PlanarHom.Complexity.PromiseProblem) →
                        PlanarHom.Complexity.PromisePolyTimeTuringReduction
                            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.domainProblem L D B T) base →
                          PlanarHom.Complexity.PromisePolyTimeTuringReduction
                            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.domainUnaryTargetProblem L D B T N hN
                              old)
                            base) :=
  sorry

/-- Paper item 3.2. -/
noncomputable def item_3_2_1 :
  (∀ {q u : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 u),
    And
      (Nonempty.{2}
        (PlanarHom.Complexity.PromisePolyTimeTuringReduction (PlanarHom.Corollary32.supportProblem L)
          (PlanarHom.Corollary32.squareProblem L)))
      (And
        (Nonempty.{2}
          (PlanarHom.Complexity.PromisePolyTimeTuringReduction (PlanarHom.Corollary32.squareProblem L)
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)))
        (And
          (Nonempty.{2}
            (PlanarHom.Complexity.PromisePolyTimeTuringReduction (PlanarHom.Corollary32.supportProblem L)
              (PlanarHom.Corollary32.magnitudeProblem L)))
          (Nonempty.{2}
            (PlanarHom.Complexity.PromisePolyTimeTuringReduction (PlanarHom.Corollary32.magnitudeProblem L)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)))))) :=
  sorry

/-- Paper item 3.2. -/
noncomputable def item_3_2_2 :
  (∀ {q u : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 u),
    And
      (Nonempty.{2}
        (PlanarHom.Complexity.PromisePolyTimeTuringReduction
          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) (PlanarHom.Corollary32.mixedProblem L)))
      (Nonempty.{2}
        (PlanarHom.Complexity.PromisePolyTimeTuringReduction (PlanarHom.Corollary32.mixedProblem L)
          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)))) :=
  sorry

/-- Paper item 3.2. -/
noncomputable def item_3_2_3 :
  (∀ {q u : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 u),
    Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) 0 →
      ∃ (a : Real) (b : Real),
        And (LT.lt.{0} 0 a)
          (And (LT.lt.{0} 0 b)
            (And
              (∃ (i : Fin q) (j : Fin q),
                Eq.{1} (abs.{0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) a)
              (And
                (∃ (i : Fin q) (j : Fin q),
                  Eq.{1} (abs.{0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) b)
                (And
                  (∀ (i j : Fin q),
                    Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 0 →
                      LE.le.{0} a (abs.{0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)))
                  (And
                    (∀ (i j : Fin q),
                      LE.le.{0} (abs.{0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) b)
                    (Nonempty.{2}
                      (PlanarHom.Complexity.PromisePolyTimeTuringReduction
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.mixedFiniteTargetProblem L
                          (PlanarHom.SupportTransformAvailability.fiveTransforms
                            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) a b)
                          (fun (i : Fin 0) => Fin.elim0.{1} i)
                          (PlanarHom.SupportTransformAvailability.fiveTransforms_algebraic
                            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) a b
                            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices_algebraic L 0))
                          fun (i : Fin 0) => Fin.elim0.{0} i)
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))))))))) :=
  sorry

/-- Paper item 3.3. -/
noncomputable def item_3_3_1 :
  ({q bt ut : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut) →
      (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
        (old : Fin bt) →
          (hC : Matrix.PosSemidef.{0, 0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old)) →
            (base : PlanarHom.Complexity.PromiseProblem) →
              PlanarHom.Complexity.PromisePolyTimeTuringReduction
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) base →
                PlanarHom.Complexity.PromisePolyTimeTuringReduction
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.rangeTargetProblem L old hC) base) :=
  sorry

/-- Paper item 3.3. -/
noncomputable def item_3_3_2 :
  ({q bt ut : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut) →
      (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
        (old : Fin bt) →
          (hC : Matrix.PosDef.{0, 0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old)) →
            (r : Rat) →
              (base : PlanarHom.Complexity.PromiseProblem) →
                PlanarHom.Complexity.PromisePolyTimeTuringReduction
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) base →
                  PlanarHom.Complexity.PromisePolyTimeTuringReduction
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.rationalPowerTargetProblem L old hC r) base) :=
  sorry

/-- Paper item 3.5. -/
noncomputable def item_3_5_1 :
  ({q : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0) →
      (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
        (X : Set.{0} (Fin q)) →
          PlanarHom.Complexity.PromisePolyTimeTuringReduction
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.singleRootProblem L X)
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)) :=
  sorry

/-- Paper item 3.5. -/
noncomputable def item_3_5_2 :
  ({q : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0) →
      (hs :
          ∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
        (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
          (c :
              SimpleGraph.ConnectedComponent.{0}
                (PlanarHom.RootedRestriction.colorSupport
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) hs)) →
            PlanarHom.Complexity.PromisePolyTimeTuringReduction
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.supportRestrictionProblem L
                (SimpleGraph.ConnectedComponent.supp.{0} c))
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)) :=
  sorry

/-- Paper item 3.5. -/
noncomputable def item_3_5_3 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0)
    (hs :
      ∀ (i j : Fin q),
        Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)),
    (∀
        (c :
          SimpleGraph.ConnectedComponent.{0}
            (PlanarHom.RootedRestriction.colorSupport (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)
              hs)),
        PlanarHom.Complexity.PromiseProblem.InFP
          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.supportRestrictionProblem L
            (SimpleGraph.ConnectedComponent.supp.{0} c))) →
      PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)) :=
  sorry

/-- Paper item 3.6. -/
noncomputable def item_3_6_1 :
  (∀ {n r : Nat} (v : Fin r → Fin n → Real),
    (∀ (i : Fin r), Ne.{1} (v i) 0) →
      (∀ (i j : Fin r), Ne.{1} i j → ∀ (c : Real), Ne.{1} (v i) (HSMul.hSMul.{0, 0, 0} c (v j))) →
        LinearIndependent.{0, 0, 0} Real fun (i : Fin r) =>
          (PiTensorProduct.tprod.{0, 0, 0} Real) fun (x : Fin (Max.max.{0} 1 (HSub.hSub.{0, 0, 0} r 1))) => v i) :=
  sorry

/-- Paper item 3.6. -/
noncomputable def item_3_6_2 :
  (∀ {n r : Nat} (B : Matrix.{0, 0, 0} (Fin r) (Fin n) Real) (d : Fin n → Real),
    (∀ (k : Fin n), LT.lt.{0} 0 (d k)) →
      (∀ (i : Fin r), Ne.{1} (B i) 0) →
        (∀ (i j : Fin r), Ne.{1} i j → ∀ (t : Real), Ne.{1} (B i) (HSMul.hSMul.{0, 0, 0} t (B j))) →
          Matrix.PosDef.{0, 0} fun (i j : Fin r) =>
            HPow.hPow.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} B (Matrix.diagonal.{0, 0} d)) (Matrix.transpose.{0, 0, 0} B) i j)
              (Max.max.{0} 1 (HSub.hSub.{0, 0, 0} r 1))) :=
  sorry

/-- Paper item 3.7. -/
noncomputable def item_3_7_1 :
  ({q bt ut : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut) →
      (old : Fin bt) →
        (∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old j i)) →
          (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
            (∀ (i : Fin q), Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i) 0) →
              (∀ (i j : Fin q),
                  Ne.{1} i j →
                    ∀ (t : Real),
                      Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i)
                        (HSMul.hSMul.{0, 0, 0} t
                          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old j))) →
                (base : PlanarHom.Complexity.PromiseProblem) →
                  PlanarHom.Complexity.PromisePolyTimeTuringReduction
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) base →
                    PlanarHom.Complexity.PromisePolyTimeTuringReduction
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.inverseWeightProblem L) base) :=
  sorry

/-- Paper item 3.7. -/
noncomputable def item_3_7_2 :
  ({q bt ut : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut) →
      (old : Fin bt) →
        (∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old j i)) →
          (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
            (∀ (i : Fin q), Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i) 0) →
              (∀ (i j : Fin q),
                  Ne.{1} i j →
                    ∀ (t : Real),
                      Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i)
                        (HSMul.hSMul.{0, 0, 0} t
                          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old j))) →
                (base : PlanarHom.Complexity.PromiseProblem) →
                  PlanarHom.Complexity.PromisePolyTimeTuringReduction
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) base →
                    PlanarHom.Complexity.PromisePolyTimeTuringReduction
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unitWeightProblem L) base) :=
  sorry

/-- Paper item 3.7. -/
noncomputable def item_3_7_3 :
  ({q bt ut : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut) →
      (old : Fin bt) →
        (∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old j i)) →
          (hw : ∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
            (∀ (i : Fin q), Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i) 0) →
              (∀ (i j : Fin q),
                  Ne.{1} i j →
                    ∀ (t : Real),
                      Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i)
                        (HSMul.hSMul.{0, 0, 0} t
                          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old j))) →
                (r : Rat) →
                  (base : PlanarHom.Complexity.PromiseProblem) →
                    PlanarHom.Complexity.PromisePolyTimeTuringReduction
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) base →
                      PlanarHom.Complexity.PromisePolyTimeTuringReduction
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.rationalWeightProblem L hw r) base) :=
  sorry

/-- Paper item 3.7. -/
noncomputable def item_3_7_4 :
  ({q bt ut n : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut) →
      (old : Fin bt) →
        (∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old j i)) →
          (hw : ∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
            (∀ (i : Fin q), Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i) 0) →
              (∀ (i j : Fin q),
                  Ne.{1} i j →
                    ∀ (t : Real),
                      Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i)
                        (HSMul.hSMul.{0, 0, 0} t
                          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old j))) →
                (rs : Fin n → Rat) →
                  (base : PlanarHom.Complexity.PromiseProblem) →
                    PlanarHom.Complexity.PromisePolyTimeTuringReduction
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) base →
                      PlanarHom.Complexity.PromisePolyTimeTuringReduction
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.finiteWeightPowerProblem L hw rs) base) :=
  sorry

/-- Paper item 3.8. -/
noncomputable def item_3_8_1 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0) {V E : Type}
    [inst : Fintype.{0} V] [inst_1 : Fintype.{0} E] (G : PlanarHom.MultiGraph.{0, 0} V E)
    (hs :
      ∀ (i j : Fin q),
        Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)),
    Eq.{1}
      (PlanarHom.MultiGraph.partition.{0, 0, 0, 0} G (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)
        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L))
      (PlanarHom.MultiGraph.partition.{0, 0, 0, 0} G
        (PlanarHom.Twins.quotientMatrix.{0, 0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) hs)
        (PlanarHom.Twins.quotientWeight.{0, 0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)
          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L)))) :=
  sorry

/-- Paper item 3.8. -/
noncomputable def item_3_8_2 :
  ({q : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0) →
      (hs :
          ∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
        (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
          (∀
              (i j :
                Fin
                  (PlanarHom.ActualTwins.reducedCount (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matricesK L 0)
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.actualTwin_symmetryK L hs))),
              Ne.{1} i j →
                ∀ (t : Real),
                  Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.actualTwinMatrix L hs i)
                    (HSMul.hSMul.{0, 0, 0} t
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.actualTwinMatrix L hs j))) →
            PlanarHom.Complexity.PromisePolyTimeTuringReduction
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.actualTwinProblem L hs)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)) :=
  sorry

/-- Paper item 3.8. -/
noncomputable def item_3_8_3 :
  ({q : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0) →
      (hs :
          ∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
        (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
          (∀ (i j : Fin q),
              Or (Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 0)
                (Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 1)) →
            PlanarHom.Complexity.PromisePolyTimeTuringReduction
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.actualTwinProblem L hs)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)) :=
  sorry

/-- Paper item 3.8. -/
noncomputable def item_3_8_4 :
  ({q : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0) →
      (hs :
          ∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
        (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
          (∀ (i j : Fin q),
              Or (Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 0)
                (Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 1)) →
            (P : PlanarHom.Complexity.PromiseProblem) →
              PlanarHom.Complexity.PromisePolyTimeTuringReduction P
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.actualTwinProblem L hs) →
                PlanarHom.Complexity.PromisePolyTimeTuringReduction P
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)) :=
  sorry

/-- Paper item 3.9. -/
noncomputable def item_3_9_1 :
  (∀ {n : Nat} (μ c : Fin n → Real),
    (∀ (i : Fin n), LT.lt.{0} 0 (μ i)) →
      StrictMono.{0, 0} μ →
        Ne.{1} c 0 →
          LE.le.{0}
            (Set.encard.{0}
              (setOf.{0} fun (t : Real) =>
                Eq.{1} (∑ i : Fin n, HMul.hMul.{0, 0, 0} (c i) (HPow.hPow.{0, 0, 0} (μ i) t)) 0))
            ↑(HSub.hSub.{0, 0, 0} n 1)) :=
  sorry

/-- Paper item 3.10. -/
noncomputable def item_3_10_1 :
  ({K₀ : IntermediateField.{0, 0} Rat Real} →
    {sourceDimension q bt ut : Nat} →
      (sourceBasis : Module.Basis.{0, 0, 0} (Fin sourceDimension) Rat ↥K₀) →
        (X : Set.{0} Rat) →
          (fields :
              PlanarHom.EffectiveProductTransfer.PresentedExtensions sourceBasis
                (PlanarHom.EffectiveProductTransfer.rationalParameters X)) →
            (M : Fin bt → Matrix.{0, 0, 0} (Fin q) (Fin q) ↥K₀) →
              (U : Fin ut → Fin q → ↥K₀) →
                (F : Matrix.{0, 0, 0} (Fin q) (Fin q) (Polynomial.{0} ↥K₀)) →
                  (B :
                      (x : ↑X) →
                        Matrix.{0, 0, 0} (Fin q) (Fin q)
                          ↥(PlanarHom.EffectiveProductTransfer.PresentedExtensions.fields fields x)) →
                    (d n₀ : Nat) →
                      LE.le.{0} 1 n₀ →
                        (∀ (i j : Fin q), LE.le.{0} (Polynomial.natDegree.{0} (F i j)) d) →
                          (∀ (x : Real) (i j : Fin q),
                              Eq.{1} (PlanarHom.EffectiveProductTransfer.polynomialRealFamily F x i j)
                                (PlanarHom.EffectiveProductTransfer.polynomialRealFamily F x j i)) →
                            (∀ (x : ↑X) (i j : Fin q), Eq.{1} (B x i j) (B x j i)) →
                              (PlanarHom.Complexity.FP (PlanarHom.EffectiveProductTransfer.rationalParameters X)
                                  (PlanarHom.DependentFieldCodecs.sigma
                                    (PlanarHom.EffectiveProductTransfer.rationalParameters X) fun (x : ↑X) =>
                                    PlanarHom.Complexity.BitEncoding.vector
                                      (PlanarHom.Complexity.numberFieldEncoding
                                        (PlanarHom.EffectiveProductTransfer.PresentedExtensions.basis fields x))
                                      (HMul.hMul.{0, 0, 0} q q))
                                  fun (x : ↑X) =>
                                  Sigma.mk.{0, 0} x (PlanarHom.Complexity.MixedCode.binaryAlphabet (B x))) →
                                (∀ (n : Nat),
                                    LE.le.{0} n₀ n →
                                      ∀ (i j : Fin q),
                                        LT.lt.{0} 0
                                          (PlanarHom.EffectiveProductTransfer.polynomialRealFamily F (↑n) i j)) →
                                  (∀ (x : ↑X),
                                      PlanarHom.EffectiveProductTransfer.ProductIdentities
                                        (PlanarHom.EffectiveProductTransfer.polynomialRealFamily F) fun (i j : Fin q) =>
                                        ↑(B x i j)) →
                                    (base : PlanarHom.Complexity.PromiseProblem) →
                                      PlanarHom.Complexity.PromisePolyTimeTuringReduction
                                          (PlanarHom.DynamicMatrixFamilySource.problem sourceBasis M U
                                            (fun (x : Fin q) => 1)
                                            (PlanarHom.EffectiveProductTransfer.polynomialFamily F))
                                          base →
                                        PlanarHom.Complexity.PromisePolyTimeTuringReduction
                                          (PlanarHom.EffectiveProductTransfer.variableTargetProblem sourceBasis
                                            (PlanarHom.EffectiveProductTransfer.rationalParameters X) fields M U B)
                                          base) :=
  sorry

/-- Paper item 3.10. -/
noncomputable def item_3_10_2 :
  ({K₀ : IntermediateField.{0, 0} Rat Real} →
    [FiniteDimensional.{0, 0} Rat ↥K₀] →
      {sourceDimension q bt ut : Nat} →
        (sourceBasis : Module.Basis.{0, 0, 0} (Fin sourceDimension) Rat ↥K₀) →
          (X : Set.{0} Rat) →
            (fields :
                PlanarHom.EffectiveProductTransfer.PresentedExtensions sourceBasis
                  (PlanarHom.EffectiveProductTransfer.rationalParameters X)) →
              (M : Fin bt → Matrix.{0, 0, 0} (Fin q) (Fin q) ↥K₀) →
                (U : Fin ut → Fin q → ↥K₀) →
                  (A : Matrix.{0, 0, 0} (Fin q) (Fin q) ↥K₀) →
                    (B :
                        (x : ↑X) →
                          Matrix.{0, 0, 0} (Fin q) (Fin q)
                            ↥(PlanarHom.EffectiveProductTransfer.PresentedExtensions.fields fields x)) →
                      Matrix.PosDef.{0, 0} (PlanarHom.SpectralFieldPresentation.realMatrix A) →
                        (∀ (x : ↑X) (i j : Fin q), Eq.{1} (B x i j) (B x j i)) →
                          (PlanarHom.Complexity.FP (PlanarHom.EffectiveProductTransfer.rationalParameters X)
                              (PlanarHom.DependentFieldCodecs.sigma
                                (PlanarHom.EffectiveProductTransfer.rationalParameters X) fun (x : ↑X) =>
                                PlanarHom.Complexity.BitEncoding.vector
                                  (PlanarHom.Complexity.numberFieldEncoding
                                    (PlanarHom.EffectiveProductTransfer.PresentedExtensions.basis fields x))
                                  (HMul.hMul.{0, 0, 0} q q))
                              fun (x : ↑X) => Sigma.mk.{0, 0} x (PlanarHom.Complexity.MixedCode.binaryAlphabet (B x))) →
                            (n₀ : Nat) →
                              LE.le.{0} 1 n₀ →
                                (∀ (n : Nat),
                                    LE.le.{0} n₀ n →
                                      ∀ (i j : Fin q),
                                        LT.lt.{0} 0
                                          (PlanarHom.EffectiveProductTransfer.matrixPowerRealFamily A (↑n) i j)) →
                                  (∀ (x : ↑X),
                                      PlanarHom.EffectiveProductTransfer.ProductIdentities
                                        (PlanarHom.EffectiveProductTransfer.matrixPowerRealFamily A) fun (i j : Fin q) =>
                                        ↑(B x i j)) →
                                    (base : PlanarHom.Complexity.PromiseProblem) →
                                      PlanarHom.Complexity.PromisePolyTimeTuringReduction
                                          (PlanarHom.DynamicMatrixFamilySource.problem sourceBasis M U
                                            (fun (x : Fin q) => 1) fun (n : Nat) => HPow.hPow.{0, 0, 0} A n)
                                          base →
                                        PlanarHom.Complexity.PromisePolyTimeTuringReduction
                                          (PlanarHom.EffectiveProductTransfer.variableTargetProblem sourceBasis
                                            (PlanarHom.EffectiveProductTransfer.rationalParameters X) fields M U B)
                                          base) :=
  sorry

/-- Paper item 3.10. -/
noncomputable def item_3_10_3 :
  ({K₀ : IntermediateField.{0, 0} Rat Real} →
    {sourceDimension q bt ut dt : Nat} →
      (sourceBasis : Module.Basis.{0, 0, 0} (Fin sourceDimension) Rat ↥K₀) →
        (X : Set.{0} Rat) →
          (fields :
              PlanarHom.EffectiveProductTransfer.PresentedExtensions sourceBasis
                (PlanarHom.EffectiveProductTransfer.rationalParameters X)) →
            (M : Fin bt → Matrix.{0, 0, 0} (Fin q) (Fin q) ↥K₀) →
              (U : Fin ut → Fin q → ↥K₀) →
                (D : Fin dt → Set.{0} (Fin q)) →
                  (policy : Fin (HAdd.hAdd.{0, 0, 0} bt 1) → Fin dt → Fin dt → Prop) →
                    (typing : Fin ut → Fin dt → Prop) →
                      (F : Matrix.{0, 0, 0} (Fin q) (Fin q) (Polynomial.{0} ↥K₀)) →
                        (B :
                            (x : ↑X) →
                              Matrix.{0, 0, 0} (Fin q) (Fin q)
                                ↥(PlanarHom.EffectiveProductTransfer.PresentedExtensions.fields fields x)) →
                          (d n₀ : Nat) →
                            LE.le.{0} 1 n₀ →
                              (∀ (i j : Fin q), LE.le.{0} (Polynomial.natDegree.{0} (F i j)) d) →
                                (∀ (x : Real) (i j : Fin q),
                                    Eq.{1} (PlanarHom.EffectiveProductTransfer.polynomialRealFamily F x i j)
                                      (PlanarHom.EffectiveProductTransfer.polynomialRealFamily F x j i)) →
                                  (∀ (x : ↑X) (i j : Fin q), Eq.{1} (B x i j) (B x j i)) →
                                    (PlanarHom.Complexity.FP (PlanarHom.EffectiveProductTransfer.rationalParameters X)
                                        (PlanarHom.DependentFieldCodecs.sigma
                                          (PlanarHom.EffectiveProductTransfer.rationalParameters X) fun (x : ↑X) =>
                                          PlanarHom.Complexity.BitEncoding.vector
                                            (PlanarHom.Complexity.numberFieldEncoding
                                              (PlanarHom.EffectiveProductTransfer.PresentedExtensions.basis fields x))
                                            (HMul.hMul.{0, 0, 0} q q))
                                        fun (x : ↑X) =>
                                        Sigma.mk.{0, 0} x (PlanarHom.Complexity.MixedCode.binaryAlphabet (B x))) →
                                      (∀ (n : Nat),
                                          LE.le.{0} n₀ n →
                                            ∀ (i j : Fin q),
                                              LT.lt.{0} 0
                                                (PlanarHom.EffectiveProductTransfer.polynomialRealFamily F (↑n) i j)) →
                                        (∀ (x : ↑X),
                                            PlanarHom.EffectiveProductTransfer.ProductIdentities
                                              (PlanarHom.EffectiveProductTransfer.polynomialRealFamily F)
                                              fun (i j : Fin q) => ↑(B x i j)) →
                                          (base : PlanarHom.Complexity.PromiseProblem) →
                                            PlanarHom.Complexity.PromisePolyTimeTuringReduction
                                                (PlanarHom.RestrictedMatrixFamilyReduction.sourceProblem sourceBasis M
                                                  (PlanarHom.PrescribedDomains.extendedUnaries U D) (fun (x : Fin q) => 1)
                                                  (PlanarHom.EffectiveProductTransfer.polynomialFamily F)
                                                  (PlanarHom.PrescribedDomains.EncodedGraph policy typing))
                                                base →
                                              PlanarHom.Complexity.PromisePolyTimeTuringReduction
                                                (PlanarHom.EffectiveProductTransfer.variableDomainTargetProblem
                                                  sourceBasis (PlanarHom.EffectiveProductTransfer.rationalParameters X)
                                                  fields M U D policy typing B)
                                                base) :=
  sorry

/-- Paper item 3.10. -/
noncomputable def item_3_10_4 :
  ({K₀ : IntermediateField.{0, 0} Rat Real} →
    [FiniteDimensional.{0, 0} Rat ↥K₀] →
      {sourceDimension q bt ut dt : Nat} →
        (sourceBasis : Module.Basis.{0, 0, 0} (Fin sourceDimension) Rat ↥K₀) →
          (X : Set.{0} Rat) →
            (fields :
                PlanarHom.EffectiveProductTransfer.PresentedExtensions sourceBasis
                  (PlanarHom.EffectiveProductTransfer.rationalParameters X)) →
              (M : Fin bt → Matrix.{0, 0, 0} (Fin q) (Fin q) ↥K₀) →
                (U : Fin ut → Fin q → ↥K₀) →
                  (D : Fin dt → Set.{0} (Fin q)) →
                    (policy : Fin (HAdd.hAdd.{0, 0, 0} bt 1) → Fin dt → Fin dt → Prop) →
                      (typing : Fin ut → Fin dt → Prop) →
                        (A : Matrix.{0, 0, 0} (Fin q) (Fin q) ↥K₀) →
                          (B :
                              (x : ↑X) →
                                Matrix.{0, 0, 0} (Fin q) (Fin q)
                                  ↥(PlanarHom.EffectiveProductTransfer.PresentedExtensions.fields fields x)) →
                            Matrix.PosDef.{0, 0} (PlanarHom.SpectralFieldPresentation.realMatrix A) →
                              (∀ (x : ↑X) (i j : Fin q), Eq.{1} (B x i j) (B x j i)) →
                                (PlanarHom.Complexity.FP (PlanarHom.EffectiveProductTransfer.rationalParameters X)
                                    (PlanarHom.DependentFieldCodecs.sigma
                                      (PlanarHom.EffectiveProductTransfer.rationalParameters X) fun (x : ↑X) =>
                                      PlanarHom.Complexity.BitEncoding.vector
                                        (PlanarHom.Complexity.numberFieldEncoding
                                          (PlanarHom.EffectiveProductTransfer.PresentedExtensions.basis fields x))
                                        (HMul.hMul.{0, 0, 0} q q))
                                    fun (x : ↑X) =>
                                    Sigma.mk.{0, 0} x (PlanarHom.Complexity.MixedCode.binaryAlphabet (B x))) →
                                  (n₀ : Nat) →
                                    LE.le.{0} 1 n₀ →
                                      (∀ (n : Nat),
                                          LE.le.{0} n₀ n →
                                            ∀ (i j : Fin q),
                                              LT.lt.{0} 0
                                                (PlanarHom.EffectiveProductTransfer.matrixPowerRealFamily A (↑n) i j)) →
                                        (∀ (x : ↑X),
                                            PlanarHom.EffectiveProductTransfer.ProductIdentities
                                              (PlanarHom.EffectiveProductTransfer.matrixPowerRealFamily A)
                                              fun (i j : Fin q) => ↑(B x i j)) →
                                          (base : PlanarHom.Complexity.PromiseProblem) →
                                            PlanarHom.Complexity.PromisePolyTimeTuringReduction
                                                (PlanarHom.RestrictedMatrixFamilyReduction.sourceProblem sourceBasis M
                                                  (PlanarHom.PrescribedDomains.extendedUnaries U D) (fun (x : Fin q) => 1)
                                                  (fun (n : Nat) => HPow.hPow.{0, 0, 0} A n)
                                                  (PlanarHom.PrescribedDomains.EncodedGraph policy typing))
                                                base →
                                              PlanarHom.Complexity.PromisePolyTimeTuringReduction
                                                (PlanarHom.EffectiveProductTransfer.variableDomainTargetProblem
                                                  sourceBasis (PlanarHom.EffectiveProductTransfer.rationalParameters X)
                                                  fields M U D policy typing B)
                                                base) :=
  sorry

/-- Paper item 3.11. -/
noncomputable def item_3_11_1 :
  (∀ {q bt ut : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut),
    (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      ∀ (old : Fin bt),
        LE.le.{0} 3 q →
          ∀ (hpd : Matrix.PosDef.{0, 0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old)),
            (∀ (i j : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i j)) →
              SimpleGraph.Connected.{0}
                  (PlanarHom.LogarithmicSupport.offDiagonalSupport.{0}
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old) (And.left hpd)) →
                (∀ (i j : Fin q),
                    Ne.{1} i j →
                      Ne.{1}
                        (PlanarHom.EntropyCompletion.matrixLog.{0}
                          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old) i j)
                        0) →
                  PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)) :=
  sorry

/-- Paper item 3.11. -/
noncomputable def item_3_11_2 :
  (∀ {q bt ut : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut),
    (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      ∀ (old : Fin bt),
        LE.le.{0} 3 q →
          ∀ (hpd : Matrix.PosDef.{0, 0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old)),
            (∀ (i j : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old i j)) →
              SimpleGraph.Connected.{0}
                  (PlanarHom.LogarithmicSupport.offDiagonalSupport.{0}
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old) (And.left hpd)) →
                (∀ (i j : Fin q),
                    Ne.{1} i j →
                      Ne.{1}
                        (PlanarHom.EntropyCompletion.matrixLog.{0}
                          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old) i j)
                        0) →
                  ∀ (P : PlanarHom.Complexity.PromiseProblem)
                    (available :
                      PlanarHom.Complexity.PromisePolyTimeTuringReduction
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) P),
                    PlanarHom.Complexity.PromisedSharpPHard P) :=
  sorry

/-- Paper item 4.1. -/
noncomputable def item_4_1_1 :
  (∀ {V : Type} [inst : Fintype.{0} V] [inst_1 : DecidableEq.{1} V] (A : Set.{0} (Matrix.{0, 0, 0} V V Real)),
    PlanarHom.ClosedMatrixFamily.AlgebraicSourceClosed A →
      (∃ (H : Matrix.{0, 0, 0} V V Real), PlanarHom.ClosedMatrixFamily.Admissible A H) →
        ∃ (M : Matrix.{0, 0, 0} V V Real),
          And (PlanarHom.ClosedMatrixFamily.Admissible A M)
            (And (PlanarHom.ClosedMatrixFamily.IsMaximum A M)
              (And (SimpleGraph.Connected.{0} (PlanarHom.LogarithmicSupport.logSupport.{0} M))
                (∀ (i j : V),
                  SimpleGraph.Adj.{0} (PlanarHom.LogarithmicSupport.logSupport.{0} M) i j →
                    LT.lt.{0} 0 (PlanarHom.EntropyCompletion.matrixLog.{0} M i j))))) :=
  sorry

/-- Paper item 4.2. -/
noncomputable def item_4_2_1 :
  ({q bt ut : Nat} →
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q bt ut) →
      (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
        (old : Fin bt) →
          Matrix.PosDef.{0, 0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old) →
            SimpleGraph.Connected.{0}
                (PlanarHom.LogarithmicSupport.logSupport.{0}
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old)) →
              (∀ (i j : Fin q),
                  SimpleGraph.Adj.{0}
                      (PlanarHom.LogarithmicSupport.logSupport.{0}
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old))
                      i j →
                    LT.lt.{0} 0
                      (PlanarHom.EntropyCompletion.matrixLog.{0}
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L old) i j)) →
                (base : PlanarHom.Complexity.PromiseProblem) →
                  PlanarHom.Complexity.PromisePolyTimeTuringReduction
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) base →
                    PlanarHom.Complexity.PromisePolyTimeTuringReduction
                      (PlanarHom.AlgebraicProductInterpolation.RealLanguage.distanceKernelTargetProblem L old) base) :=
  sorry

/-- Paper item 4.2. -/
noncomputable def item_4_2_2 :
  (∀ {q : Nat} (A : Set.{0} (Matrix.{0, 0, 0} (Fin q) (Fin q) Real)),
    PlanarHom.ClosedMatrixFamily.AlgebraicSourceClosed A →
      PlanarHom.ClosedMatrixFamily.EffectiveSpectralClosed A →
        ∀ (M : Matrix.{0, 0, 0} (Fin q) (Fin q) Real),
          PlanarHom.ClosedMatrixFamily.Admissible A M →
            PlanarHom.ClosedMatrixFamily.IsMaximum A M →
              (∀ (i j : Fin q),
                  SimpleGraph.Adj.{0} (PlanarHom.LogarithmicSupport.logSupport.{0} M) i j →
                    LT.lt.{0} 0 (PlanarHom.EntropyCompletion.matrixLog.{0} M i j)) →
                And
                  (∀ (x : Rat),
                    LT.lt.{0} 0 x →
                      Membership.mem.{0, 0} A
                        (PlanarHom.EntropyCompletion.distanceKernel.{0} (PlanarHom.LogarithmicSupport.logSupport.{0} M)
                          ↑x))
                  (∃ (ε : Real),
                    And (LT.lt.{0} 0 ε)
                      (∀ (x : Real),
                        LT.lt.{0} 0 x →
                          LT.lt.{0} x ε →
                            And
                              (Matrix.PosDef.{0, 0}
                                (PlanarHom.EntropyCompletion.distanceKernel.{0}
                                  (PlanarHom.LogarithmicSupport.logSupport.{0} M) x))
                              (PlanarHom.EntropyCompletion.logVanishesOnNonedges.{0}
                                (PlanarHom.LogarithmicSupport.logSupport.{0} M)
                                (PlanarHom.EntropyCompletion.distanceKernel.{0}
                                  (PlanarHom.LogarithmicSupport.logSupport.{0} M) x))))) :=
  sorry

/-- Paper item 4.3. -/
noncomputable def item_4_3_1 :
  (∀ {V : Type} [inst : Fintype.{0} V] [inst_1 : DecidableEq.{1} V] (A : Set.{0} (Matrix.{0, 0, 0} V V Real)),
    PlanarHom.ClosedMatrixFamily.AlgebraicSourceClosed A →
      ∀ (M N : Matrix.{0, 0, 0} V V Real),
        PlanarHom.ClosedMatrixFamily.Admissible A M →
          PlanarHom.ClosedMatrixFamily.IsMaximum A M →
            Membership.mem.{0, 0} A N →
              Matrix.PosDef.{0, 0} N →
                Eq.{1} (PlanarHom.LogarithmicSupport.logSupport.{0} N) (PlanarHom.LogarithmicSupport.logSupport.{0} M) →
                  (∀ (i j : V),
                      SimpleGraph.Adj.{0} (PlanarHom.LogarithmicSupport.logSupport.{0} M) i j →
                        LT.lt.{0} 0 (PlanarHom.EntropyCompletion.matrixLog.{0} N i j)) →
                    ∀ (i j : V),
                      PlanarHom.ClosedMatrixFamily.PathRigidity (PlanarHom.LogarithmicSupport.logSupport.{0} M)
                        (PlanarHom.EntropyCompletion.matrixLog.{0} N) i j) :=
  sorry

/-- Paper item 4.4. -/
noncomputable def item_4_4_1 :
  (∀ {q : Nat} (A : Set.{0} (Matrix.{0, 0, 0} (Fin q) (Fin q) Real)),
    PlanarHom.ClosedMatrixFamily.AlgebraicSourceClosed A →
      PlanarHom.ClosedMatrixFamily.EffectiveSpectralClosed A →
        PlanarHom.ClosedMatrixFamily.PlanarGadgetClosed A →
          ∀ (M : Matrix.{0, 0, 0} (Fin q) (Fin q) Real),
            PlanarHom.ClosedMatrixFamily.Admissible A M →
              PlanarHom.ClosedMatrixFamily.IsMaximum A M →
                (∀ (i j : Fin q),
                    SimpleGraph.Adj.{0} (PlanarHom.LogarithmicSupport.logSupport.{0} M) i j →
                      LT.lt.{0} 0 (PlanarHom.EntropyCompletion.matrixLog.{0} M i j)) →
                  And (PlanarHom.CartesianGeometry.TwoCommonNeighbors.{0} (PlanarHom.LogarithmicSupport.logSupport.{0} M))
                    (PlanarHom.CartesianGeometry.NeighborhoodCliques.{0} (PlanarHom.LogarithmicSupport.logSupport.{0} M))) :=
  sorry

/-- Paper item 4.5. -/
noncomputable def item_4_5_1.{u_1} :
  (∀ {V : Type u_1} [inst : Fintype.{u_1} V] [inst_1 : DecidableEq.{u_1 + 1} V] (G : SimpleGraph.{u_1} V),
    SimpleGraph.Connected.{u_1} G →
      PlanarHom.EntropyCompletion.initiallyLogSparse.{u_1} G →
        ∀ {x : Real},
          LT.lt.{0} 0 x → LT.lt.{0} x 1 → Matrix.PosDef.{u_1, 0} (PlanarHom.EntropyCompletion.distanceKernel.{u_1} G x)) :=
  sorry

/-- Paper item 4.6. -/
noncomputable def item_4_6_1.{u_1} :
  (∀ {V : Type u_1} [inst : Fintype.{u_1} V] [DecidableEq.{u_1 + 1} V] (G : SimpleGraph.{u_1} V),
    SimpleGraph.Connected.{u_1} G →
      (∀ (x : Real),
          LT.lt.{0} 0 x →
            LT.lt.{0} x 1 → Matrix.PosSemidef.{u_1, 0} (PlanarHom.EntropyCompletion.distanceKernel.{u_1} G x)) →
        PlanarHom.CartesianGeometry.NeighborhoodCliques.{u_1} G →
          PlanarHom.CartesianGeometry.TwoCommonNeighbors.{u_1} G →
            ∃ (d : Nat) (s : Fin d → Nat),
              And (∀ (i : Fin d), LE.le.{0} 2 (s i))
                (Nonempty.{max 1 (u_1 + 1)}
                  (SimpleGraph.Iso.{u_1, 0} G
                    (PlanarHom.CartesianGeometry.hammingGraph.{0, 0} fun (i : Fin d) => Fin (s i))))) :=
  sorry

/-- Paper item 4.7. -/
noncomputable def item_4_7_1 :
  (∀ {q : Nat} (A : Set.{0} (Matrix.{0, 0, 0} (Fin q) (Fin q) Real)),
    PlanarHom.ClosedMatrixFamily.AlgebraicSourceClosed A →
      PlanarHom.ClosedMatrixFamily.EffectiveSpectralClosed A →
        PlanarHom.ClosedMatrixFamily.PlanarGadgetClosed A →
          ∀ (M : Matrix.{0, 0, 0} (Fin q) (Fin q) Real),
            PlanarHom.ClosedMatrixFamily.Admissible A M →
              PlanarHom.ClosedMatrixFamily.IsMaximum A M →
                ∃ (d : Nat) (s : Fin d → Nat),
                  And (∀ (i : Fin d), LE.le.{0} 2 (s i))
                    (Nonempty.{1}
                      (SimpleGraph.Iso.{0, 0} (PlanarHom.LogarithmicSupport.logSupport.{0} M)
                        (PlanarHom.CartesianGeometry.hammingGraph.{0, 0} fun (i : Fin d) => Fin (s i))))) :=
  sorry

/-- Paper item 4.8. -/
noncomputable def item_4_8_1 :
  (∀ {q d : Nat} (A : Set.{0} (Matrix.{0, 0, 0} (Fin q) (Fin q) Real)),
    PlanarHom.ClosedMatrixFamily.AlgebraicSourceClosed A →
      PlanarHom.ClosedMatrixFamily.EffectiveSpectralClosed A →
        PlanarHom.ClosedMatrixFamily.MixedPlanarGadgetClosed A →
          ∀ (M : Matrix.{0, 0, 0} (Fin q) (Fin q) Real),
            PlanarHom.ClosedMatrixFamily.Admissible A M →
              PlanarHom.ClosedMatrixFamily.IsMaximum A M →
                ∀
                  (e :
                    SimpleGraph.Iso.{0, 0} (PlanarHom.LogarithmicSupport.logSupport.{0} M)
                      (PlanarHom.Boolean.cubeGraph d))
                  (N : Matrix.{0, 0, 0} (Fin q) (Fin q) Real),
                  Membership.mem.{0, 0} A N →
                    ∀ (hNpd : Matrix.PosDef.{0, 0} N),
                      (∀ (i j : Fin q), LE.le.{0} 0 (N i j)) →
                        And
                          (∀ (i j : Fin q),
                            Eq.{1} (N i j)
                              (HMul.hMul.{0, 0, 0}
                                (N ((SimpleGraph.Iso.symm.{0, 0} e) PlanarHom.CubeTensorExponential.zeroColor.{0})
                                  ((SimpleGraph.Iso.symm.{0, 0} e) PlanarHom.CubeTensorExponential.zeroColor.{0}))
                                (∏ r : Fin d,
                                  PlanarHom.CubeTensorExponential.factorInCoordinates.{0} (RelIso.toEquiv.{0, 0} e) N r
                                    (e i r) (e j r))))
                          (And
                            (LT.lt.{0} 0
                              (N ((SimpleGraph.Iso.symm.{0, 0} e) PlanarHom.CubeTensorExponential.zeroColor.{0})
                                ((SimpleGraph.Iso.symm.{0, 0} e) PlanarHom.CubeTensorExponential.zeroColor.{0})))
                            (And
                              (IsAlgebraic.{0, 0} Rat
                                (N ((SimpleGraph.Iso.symm.{0, 0} e) PlanarHom.CubeTensorExponential.zeroColor.{0})
                                  ((SimpleGraph.Iso.symm.{0, 0} e) PlanarHom.CubeTensorExponential.zeroColor.{0})))
                              (And
                                (∀ (r : Fin d),
                                  And
                                    (Matrix.PosDef.{0, 0}
                                      (PlanarHom.CubeTensorExponential.factorInCoordinates.{0} (RelIso.toEquiv.{0, 0} e) N
                                        r))
                                    (And
                                      (∀ (a b : Bool),
                                        LE.le.{0} 0
                                          (PlanarHom.CubeTensorExponential.factorInCoordinates.{0}
                                            (RelIso.toEquiv.{0, 0} e) N r a b))
                                      (And
                                        (∀ (a b : Bool),
                                          IsAlgebraic.{0, 0} Rat
                                            (PlanarHom.CubeTensorExponential.factorInCoordinates.{0}
                                              (RelIso.toEquiv.{0, 0} e) N r a b))
                                        (Eq.{1}
                                          (PlanarHom.CubeTensorExponential.factorInCoordinates.{0}
                                            (RelIso.toEquiv.{0, 0} e) N r Bool.false Bool.false)
                                          1))))
                                (Iff
                                  (SimpleGraph.Connected.{0}
                                    (PlanarHom.LogarithmicSupport.offDiagonalSupport.{0} N (And.left hNpd)))
                                  (∀ (r : Fin d) (a b : Bool),
                                    LT.lt.{0} 0
                                      (PlanarHom.CubeTensorExponential.factorInCoordinates.{0} (RelIso.toEquiv.{0, 0} e) N
                                        r a b))))))) :=
  sorry

/-- Paper item 5.1. -/
noncomputable def item_5_1_1 :
  (∀ {d : Nat} (F : Fin d → Matrix.{0, 0, 0} Bool Bool Real),
    (∀ (r : Fin d), Matrix.PosDef.{0, 0} (F r)) →
      (∀ (r : Fin d) (i j : Bool), LT.lt.{0} 0 (F r i j)) →
        ∀ (halg : ∀ (r : Fin d) (i j : Bool), IsAlgebraic.{0, 0} Rat (F r i j)),
          And
            ((∀ (r : Fin d), Eq.{1} (F r Bool.false Bool.false) (F r Bool.true Bool.true)) →
              PlanarHom.Complexity.PromiseProblem.InFP
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem
                  (PlanarHom.BooleanTensorDichotomy.tensorLanguage F halg)))
            ((∃ (r : Fin d), Ne.{1} (F r Bool.false Bool.false) (F r Bool.true Bool.true)) →
              PlanarHom.Complexity.PromisedSharpPHard
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem
                  (PlanarHom.BooleanTensorDichotomy.tensorLanguage F halg)))) :=
  sorry

/-- Paper item 6.1. -/
noncomputable def item_6_1_1 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0),
    (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      ∀ (hpd : Matrix.PosDef.{0, 0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)),
        (∀ (i j : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
          SimpleGraph.Connected.{0}
              (PlanarHom.LogarithmicSupport.offDiagonalSupport.{0}
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) (And.left hpd)) →
            And
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.DisplayedPositiveDefiniteForm
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) →
                PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
              (Not
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.DisplayedPositiveDefiniteForm
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)) →
                PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))) :=
  sorry

/-- Paper item 6.2. -/
noncomputable def item_6_2_1 :
  (∀ {q : Nat} (S : Set.{0} (Matrix.{0, 0, 0} (Fin q) (Fin q) Real))
    (hA : PlanarHom.ClosedMatrixFamily.AlgebraicSourceClosed S),
    PlanarHom.ClosedMatrixFamily.EffectiveSpectralClosed S →
      PlanarHom.ClosedMatrixFamily.MixedPlanarGadgetClosed S →
        ∀ (P : PlanarHom.Complexity.PromiseProblem),
          (∀ (N : Matrix.{0, 0, 0} (Fin q) (Fin q) Real) (hN : Membership.mem.{0, 0} S N),
              Nonempty.{2}
                (PlanarHom.Complexity.PromisePolyTimeTuringReduction
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unitLanguage (fun (x : Fin 1) => N)
                      fun (x : Fin 1) => PlanarHom.ClosedMatrixFamily.AlgebraicSourceClosed.algebraic hA N hN))
                  P)) →
            (∃ (H : Matrix.{0, 0, 0} (Fin q) (Fin q) Real), PlanarHom.ClosedMatrixFamily.Admissible S H) →
              Not (PlanarHom.Complexity.PromisedSharpPHard P) →
                ∃ (W : PlanarHom.ClosedMatrixFamily.CommonCubeChart S),
                  And (Eq.{1} q (HPow.hPow.{0, 0, 0} 2 (PlanarHom.ClosedMatrixFamily.CommonCubeChart.dimension W)))
                    (And
                      (∀ (N : Matrix.{0, 0, 0} (Fin q) (Fin q) Real),
                        Membership.mem.{0, 0} S N →
                          Matrix.PosDef.{0, 0} N →
                            (∀ (i j : Fin q), LE.le.{0} 0 (N i j)) →
                              ∃ (γ : Real) (A :
                                Fin (PlanarHom.ClosedMatrixFamily.CommonCubeChart.dimension W) →
                                  Matrix.{0, 0, 0} Bool Bool Real),
                                And (LT.lt.{0} 0 γ)
                                  (And
                                    (∀ (r : Fin (PlanarHom.ClosedMatrixFamily.CommonCubeChart.dimension W)),
                                      And (Matrix.PosDef.{0, 0} (A r)) (∀ (i j : Bool), LE.le.{0} 0 (A r i j)))
                                    (Eq.{1}
                                      ((Matrix.reindex.{0, 0, 0, 0, 0}
                                          (RelIso.toEquiv.{0, 0}
                                            (PlanarHom.ClosedMatrixFamily.CommonCubeChart.graphIso W))
                                          (RelIso.toEquiv.{0, 0}
                                            (PlanarHom.ClosedMatrixFamily.CommonCubeChart.graphIso W)))
                                        N)
                                      (HSMul.hSMul.{0, 0, 0} γ (PlanarHom.CubeTensorExponential.tensor.{0} A)))))
                      (And
                        (∀ (N : Matrix.{0, 0, 0} (Fin q) (Fin q) Real),
                          PlanarHom.ClosedMatrixFamily.Admissible S N →
                            ∃ (γ : Real) (ρ : Fin (PlanarHom.ClosedMatrixFamily.CommonCubeChart.dimension W) → Real),
                              And (LT.lt.{0} 0 γ)
                                (And
                                  (∀ (r : Fin (PlanarHom.ClosedMatrixFamily.CommonCubeChart.dimension W)),
                                    And (LT.lt.{0} 0 (ρ r)) (LT.lt.{0} (ρ r) 1))
                                  (Eq.{1}
                                    ((Matrix.reindex.{0, 0, 0, 0, 0}
                                        (RelIso.toEquiv.{0, 0} (PlanarHom.ClosedMatrixFamily.CommonCubeChart.graphIso W))
                                        (RelIso.toEquiv.{0, 0} (PlanarHom.ClosedMatrixFamily.CommonCubeChart.graphIso W)))
                                      N)
                                    (HSMul.hSMul.{0, 0, 0} γ (PlanarHom.Boolean.tensor ρ)))))
                        (∀ (N : Matrix.{0, 0, 0} (Fin q) (Fin q) Real),
                          Membership.mem.{0, 0} S N →
                            (∀ (i j : Fin q), LT.lt.{0} 0 (N i j)) →
                              ∃ (γ : Real) (ρ : Fin (PlanarHom.ClosedMatrixFamily.CommonCubeChart.dimension W) → Real),
                                And (LT.lt.{0} 0 γ)
                                  (And
                                    (∀ (r : Fin (PlanarHom.ClosedMatrixFamily.CommonCubeChart.dimension W)),
                                      LT.lt.{0} 0 (ρ r))
                                    (Eq.{1}
                                      ((Matrix.reindex.{0, 0, 0, 0, 0}
                                          (RelIso.toEquiv.{0, 0}
                                            (PlanarHom.ClosedMatrixFamily.CommonCubeChart.graphIso W))
                                          (RelIso.toEquiv.{0, 0}
                                            (PlanarHom.ClosedMatrixFamily.CommonCubeChart.graphIso W)))
                                        N)
                                      (HSMul.hSMul.{0, 0, 0} γ (PlanarHom.Boolean.tensor ρ)))))))) :=
  sorry

/-- Paper item 7.1. -/
noncomputable def item_7_1_1 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0),
    (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
      ∀
        (hs :
          ∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)),
        (∀ (i j : Fin q),
            Or (Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 0)
              (Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 1)) →
          And
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.BasicZeroOneSupport L hs →
              PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
            (Not (PlanarHom.AlgebraicProductInterpolation.RealLanguage.BasicZeroOneSupport L hs) →
              PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))) :=
  sorry

/-- Paper item 7.1. -/
noncomputable def item_7_1_2 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0),
    (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      ∀
        (hs :
          ∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)),
        (∀ (i j : Fin q),
            Or (Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 0)
              (Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 1)) →
          And
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.BasicZeroOneSupport L hs →
              PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
            (And
              (Not (PlanarHom.AlgebraicProductInterpolation.RealLanguage.BasicZeroOneSupport L hs) →
                PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
              (∃ (f : PlanarHom.Complexity.Bits → Nat),
                And (PlanarHom.Complexity.SharpP f)
                  (∀ (raw : PlanarHom.Complexity.Bits),
                    PlanarHom.Complexity.PromiseProblem.valid
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) raw →
                      Eq.{1}
                        (PlanarHom.Complexity.PromiseProblem.value
                          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L) raw)
                        (PlanarHom.Complexity.BitEncoding.encode
                          (PlanarHom.Complexity.numberFieldEncoding
                            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.basis L))
                          ↑(f raw)))))) :=
  sorry

/-- Paper item 8.1. -/
noncomputable def item_8_1_1 :
  (∀ {q : Nat} [Nonempty.{1} (Fin q)] (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0),
    (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      (∀ (i j : Fin q),
          Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
        (∀ (i j : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
          And
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.PositiveTensorForm
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) →
              PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
            (Not
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.PositiveTensorForm
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)) →
              PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))) :=
  sorry

/-- Paper item 8.2. -/
noncomputable def item_8_2_1 :
  (∀ {q : Nat} [Nonempty.{1} (Fin q)] (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0),
    (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      (∀ (i j : Fin q),
          Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
        (∀ (i j : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
          (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i i) 1) →
            Function.Injective.{1, 1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) →
              Or
                (PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
                (∃ (d : Nat) (e : Equiv.{1, 1} (Fin q) (PlanarHom.Boolean.Cube d)) (ρ : Fin d → Real),
                  And (∀ (r : Fin d), And (LT.lt.{0} 0 (ρ r)) (Ne.{1} (ρ r) 1))
                    (And
                      (Eq.{1}
                        ((Matrix.reindex.{0, 0, 0, 0, 0} e e)
                          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0))
                        (PlanarHom.Boolean.tensor ρ))
                      (IsUnit.{0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0))))) :=
  sorry

/-- Paper item 8.3. -/
noncomputable def item_8_3_1 :
  (∀ {q d : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0)
    (e : Equiv.{1, 1} (Fin q) (PlanarHom.Boolean.Cube d)) (ρ : Fin d → Real),
    (∀ (r : Fin d), LT.lt.{0} 0 (ρ r)) →
      (∀ (r : Fin d), Ne.{1} (ρ r) 1) →
        (∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
              (PlanarHom.Boolean.tensor ρ (e i) (e j))) →
          (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
            And
              ((∀ (i j : Fin q),
                  Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L j)) →
                PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
              ((∃ (i : Fin q) (j : Fin q),
                  Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L j)) →
                PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))) :=
  sorry

/-- Paper item 9.1. -/
noncomputable def item_9_1_1 :
  (∀ {p s : Nat} [Nonempty.{1} (Fin p)] [Nonempty.{1} (Fin s)]
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage (HAdd.hAdd.{0, 0, 0} p s) 1 0)
    (V : Matrix.{0, 0, 0} (Fin p) (Fin s) Real),
    (∀ (i : Fin p) (j : Fin s), LT.lt.{0} 0 (V i j)) →
      Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)
          (PlanarHom.RectangularSourceNormSimulation.block.{0} V) →
        (∀ (i : Fin (HAdd.hAdd.{0, 0, 0} p s)),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
          And
            (PlanarHom.RectangularUnweightedSourceForms.RectangularTensorForm V →
              PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
            (Not (PlanarHom.RectangularUnweightedSourceForms.RectangularTensorForm V) →
              PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))) :=
  sorry

/-- Paper item 9.2. -/
noncomputable def item_9_2_1 :
  (∀ {x y : Nat} [Nonempty.{1} (Fin x)] [Nonempty.{1} (Fin y)]
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage (HAdd.hAdd.{0, 0, 0} x y) 1 0),
    (∀ (i : Fin (HAdd.hAdd.{0, 0, 0} x y)), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      ∀ (B : Matrix.{0, 0, 0} (Fin x) (Fin y) Real),
        (∀ (i : Fin x) (j : Fin y), LT.lt.{0} 0 (B i j)) →
          Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)
              (PlanarHom.RectangularSourceNormSimulation.block.{0} B) →
            (∀ (i j : Fin x), Ne.{1} i j → ∀ (t : Real), Ne.{1} (B i) (HSMul.hSMul.{0, 0, 0} t (B j))) →
              (∀ (i j : Fin y),
                  Ne.{1} i j →
                    ∀ (t : Real),
                      Ne.{1} (Matrix.transpose.{0, 0, 0} B i)
                        (HSMul.hSMul.{0, 0, 0} t (Matrix.transpose.{0, 0, 0} B j))) →
                Or
                  (PlanarHom.Complexity.PromisedSharpPHard
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
                  (∃ (d : Nat),
                    And (Eq.{1} x (HPow.hPow.{0, 0, 0} 2 d))
                      (And (Eq.{1} y (HPow.hPow.{0, 0, 0} 2 d))
                        (∃ (eX : Equiv.{1, 1} (Fin x) (PlanarHom.Boolean.Cube d)) (eY :
                          Equiv.{1, 1} (Fin y) (PlanarHom.Boolean.Cube d)) (γ : Real) (ρ : Fin d → Real),
                          And (LT.lt.{0} 0 γ)
                            (And (∀ (i : Fin d), And (LT.lt.{0} 0 (ρ i)) (LT.lt.{0} (ρ i) 1))
                              (∀ (i : Fin x) (j : Fin y),
                                Eq.{1} (B i j) (HMul.hMul.{0, 0, 0} γ (PlanarHom.Boolean.tensor ρ (eX i) (eY j))))))))) :=
  sorry

/-- Paper item 9.3. -/
noncomputable def item_9_3_1 :
  (∀ {q d : Nat} (e : Equiv.{1, 1} (Fin q) (Sum.{0, 0} (PlanarHom.Boolean.Cube d) (PlanarHom.Boolean.Cube d)))
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0) (c : Real),
    LT.lt.{0} 0 c →
      ∀ (ρ : Fin d → Real),
        (∀ (r : Fin d), LT.lt.{0} 0 (ρ r)) →
          (∀ (r : Fin d), Ne.{1} (ρ r) 1) →
            ∀ (μ ν : PlanarHom.Boolean.Cube d → Real),
              (∀ (i : PlanarHom.Boolean.Cube d), LT.lt.{0} 0 (μ i)) →
                (∀ (i : PlanarHom.Boolean.Cube d), LT.lt.{0} 0 (ν i)) →
                  (∀ (i j : Fin q),
                      Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
                        (PlanarHom.PositiveRealCore.doubleMatrix (PlanarHom.PositiveRealCore.scaledTensor c ρ) (e i)
                          (e j))) →
                    (∀ (i : Fin q),
                        Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)
                          (Sum.elim.{0, 0, 1} μ ν (e i))) →
                      And
                        (PlanarHom.PrescribedTensorWeight.SideConstant μ ν →
                          PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.PrescribedTensorWeight.problem e L))
                        (Not (PlanarHom.PrescribedTensorWeight.SideConstant μ ν) →
                          PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.PrescribedTensorWeight.problem e L))) :=
  sorry

/-- Paper item 11.1. -/
noncomputable def item_11_1_1 :
  (∀ {q : Nat} [Nonempty.{1} (Fin q)] (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0),
    (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      (∀ (i j : Fin q),
          Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
        (∀ (i j : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
          (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i i) 1) →
            Function.Injective.{1, 1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) →
              Or
                (PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
                (∃ (d : Nat) (e : Equiv.{1, 1} (Fin q) (PlanarHom.Boolean.Cube d)) (ρ : Fin d → Real),
                  And (∀ (r : Fin d), And (LT.lt.{0} 0 (ρ r)) (Ne.{1} (ρ r) 1))
                    (Eq.{1}
                      ((Matrix.reindex.{0, 0, 0, 0, 0} e e)
                        (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0))
                      (PlanarHom.Boolean.tensor ρ)))) :=
  sorry

/-- Paper item 11.1. -/
noncomputable def item_11_1_2 :
  (∀ {x y : Nat} [Nonempty.{1} (Fin x)] [Nonempty.{1} (Fin y)]
    (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage (HAdd.hAdd.{0, 0, 0} x y) 1 0),
    (∀ (i : Fin (HAdd.hAdd.{0, 0, 0} x y)), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      ∀ (B : Matrix.{0, 0, 0} (Fin x) (Fin y) Real),
        (∀ (i : Fin x) (j : Fin y), LT.lt.{0} 0 (B i j)) →
          Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)
              (PlanarHom.RectangularSourceNormSimulation.block.{0} B) →
            (∀ (i j : Fin x), Ne.{1} i j → ∀ (t : Real), Ne.{1} (B i) (HSMul.hSMul.{0, 0, 0} t (B j))) →
              (∀ (i j : Fin y),
                  Ne.{1} i j →
                    ∀ (t : Real),
                      Ne.{1} (Matrix.transpose.{0, 0, 0} B i)
                        (HSMul.hSMul.{0, 0, 0} t (Matrix.transpose.{0, 0, 0} B j))) →
                Or
                  (PlanarHom.Complexity.PromisedSharpPHard
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
                  (∃ (d : Nat) (eX : Equiv.{1, 1} (Fin x) (PlanarHom.Boolean.Cube d)) (eY :
                    Equiv.{1, 1} (Fin y) (PlanarHom.Boolean.Cube d)) (γ : Real) (ρ : Fin d → Real),
                    And (LT.lt.{0} 0 γ)
                      (And (∀ (i : Fin d), And (LT.lt.{0} 0 (ρ i)) (Ne.{1} (ρ i) 1))
                        (∀ (i : Fin x) (j : Fin y),
                          Eq.{1} (B i j) (HMul.hMul.{0, 0, 0} γ (PlanarHom.Boolean.tensor ρ (eX i) (eY j))))))) :=
  sorry

/-- Paper item 11.1. -/
noncomputable def item_11_1_3 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0),
    (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      Matrix.PosDef.{0, 0} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) →
        (∀ (i j : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
          (∃ (i : Fin q) (j : Fin q),
              Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i i)
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j j)) →
            PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)) :=
  sorry

/-- Paper item 11.2. -/
noncomputable def item_11_2_1 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0)
    (hs :
      ∀ (i j : Fin q),
        Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)),
    (∀ (i j : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
      (∀ (i : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
        And
          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.SurvivingWeightedClass L hs →
            PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))
          (Not (PlanarHom.AlgebraicProductInterpolation.RealLanguage.SurvivingWeightedClass L hs) →
            PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L))) :=
  sorry

/-- Paper item 11.2. -/
noncomputable def item_11_2_2 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0),
    (∀ (i : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
      (∀ (i : Fin q), Not (LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i))) →
        ∀ (g : PlanarHom.Complexity.MixedCode) (hg : PlanarHom.Complexity.MixedCode.Valid 1 0 g),
          Eq.{1}
            (PlanarHom.Complexity.MixedCode.evaluate g hg
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matricesK L)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unariesK L)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weightsK L))
            (ite.{1} (Eq.{1} (PlanarHom.Complexity.MixedCode.vertices g) 0) 1 0)) :=
  sorry

/-- Paper item 12.1. -/
noncomputable def item_12_1_1 :
  (∀ {q : Nat} (H : PlanarHom.TargetGraphDichotomy.Target q),
    And
      (PlanarHom.TargetGraphDichotomy.Target.Basic H →
        And (PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.TargetGraphDichotomy.Target.planarProblem H))
          (PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.TargetGraphDichotomy.Target.generalProblem H)))
      (Not (PlanarHom.TargetGraphDichotomy.Target.Basic H) →
        And (PlanarHom.TargetGraphDichotomy.CountingComplete (PlanarHom.TargetGraphDichotomy.Target.planarProblem H))
          (PlanarHom.TargetGraphDichotomy.CountingComplete (PlanarHom.TargetGraphDichotomy.Target.generalProblem H)))) :=
  sorry

/-- Paper item 12.2. -/
noncomputable def item_12_2_1 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0)
    (hs :
      ∀ (i j : Fin q),
        Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)),
    (∀ (i j : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
      (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
        And
          (PlanarHom.Structures.PositiveVertexWeightClass.{0}
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices
                (PlanarHom.DomainDoublingClassification.doubledLanguage L) 0)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights
                (PlanarHom.DomainDoublingClassification.doubledLanguage L))
              (PlanarHom.DomainDoublingClassification.doubled_symm L hs) →
            PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.DomainDoublingClassification.bipartiteProblem L))
          (Not
              (PlanarHom.Structures.PositiveVertexWeightClass.{0}
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices
                  (PlanarHom.DomainDoublingClassification.doubledLanguage L) 0)
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights
                  (PlanarHom.DomainDoublingClassification.doubledLanguage L))
                (PlanarHom.DomainDoublingClassification.doubled_symm L hs)) →
            PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.DomainDoublingClassification.bipartiteProblem L))) :=
  sorry

/-- Paper item 12.2. -/
noncomputable def item_12_2_2 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0) (side : Fin q → Bool),
    (∀ (i j : Fin q),
        Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 0 → Ne.{1} (side i) (side j)) →
      ∀
        (hs :
          ∀ (i j : Fin q),
            Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)),
        (∀ (i j : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
          (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
            And
              (PlanarHom.Structures.PositiveVertexWeightClass.{0}
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L) hs →
                PlanarHom.Complexity.PromiseProblem.InFP
                  (PlanarHom.DomainDoublingClassification.prescribedProblem L side))
              (Not
                  (PlanarHom.Structures.PositiveVertexWeightClass.{0}
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L) hs) →
                PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.DomainDoublingClassification.prescribedProblem L side))) :=
  sorry

/-- Paper item 12.2. -/
noncomputable def item_12_2_3 :
  (∀ {x y : ℕ} (V : Matrix (Fin x) (Fin y) ℝ)
    (μ : Fin x → ℝ) (ν : Fin y → ℝ)
    (hV : ∀ i j, IsAlgebraic ℚ (V i j))
    (hμ : ∀ i, IsAlgebraic ℚ (μ i)) (hν : ∀ i, IsAlgebraic ℚ (ν i)),
    (∀ i j, 0 ≤ V i j) → (∀ i, 0 < μ i) → (∀ i, 0 < ν i) →
    let L := rectangularLanguage V μ ν hV hμ hν
    (PositiveVertexWeightClass (rectangularMatrix V) L.weights (rectangular_symm V) →
      (prescribedProblem L rectangularSide).InFP) ∧
    (¬PositiveVertexWeightClass (rectangularMatrix V) L.weights (rectangular_symm V) →
      PromisedSharpPHard (prescribedProblem L rectangularSide))) :=
  sorry

/-- Paper item 12.2. -/
noncomputable def item_12_2_4 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0),
    (∀ (i j : Fin q),
        Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
      (∀ (i j : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
        (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
          And
            (PlanarHom.Structures.NonnegativeClass.{0}
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices
                  (PlanarHom.DomainDoublingClassification.doubledLanguage L) 0) →
              PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.DomainDoublingClassification.bipartiteProblem L))
            (Not
                (PlanarHom.Structures.NonnegativeClass.{0}
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices
                    (PlanarHom.DomainDoublingClassification.doubledLanguage L) 0)) →
              PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.DomainDoublingClassification.bipartiteProblem L))) :=
  sorry

/-- Paper item 12.2. -/
noncomputable def item_12_2_5 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0) (side : Fin q → Bool),
    (∀ (i j : Fin q),
        Ne.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j) 0 → Ne.{1} (side i) (side j)) →
      (∀ (i j : Fin q),
          Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
        (∀ (i j : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
          (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
            And
              (PlanarHom.Structures.NonnegativeClass.{0}
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) →
                PlanarHom.Complexity.PromiseProblem.InFP
                  (PlanarHom.DomainDoublingClassification.prescribedProblem L side))
              (Not
                  (PlanarHom.Structures.NonnegativeClass.{0}
                    (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)) →
                PlanarHom.Complexity.PromisedSharpPHard (PlanarHom.DomainDoublingClassification.prescribedProblem L side))) :=
  sorry

/-- Paper item 12.4. -/
noncomputable def item_12_4_1 :
  (∀ {q : Nat} [Nonempty.{1} (Fin q)] (M : Matrix.{0, 0, 0} (Fin q) (Fin q) Real) (w : Fin q → Real)
    (hs : ∀ (i j : Fin q), Eq.{1} (M i j) (M j i)),
    (∀ (i j : Fin q), LT.lt.{0} 0 (M i j)) →
      (∀ (i j : Fin q), Eq.{1} (M i i) (M j j)) →
        Function.Injective.{1, 1} M →
          (∀ (i : Fin q), LT.lt.{0} 0 (w i)) →
            PlanarHom.Structures.PositiveVertexWeightClass.{0} M w hs →
              ∃ (d : Nat) (e : Equiv.{1, 1} (Fin q) (PlanarHom.Boolean.Cube d)) (γ : Real) (μ : Real) (ρ : Fin d → Real),
                And (Eq.{1} q (HPow.hPow.{0, 0, 0} 2 d))
                  (And (LT.lt.{0} 0 γ)
                    (And (LT.lt.{0} 0 μ)
                      (And (∀ (r : Fin d), And (LT.lt.{0} 0 (ρ r)) (Ne.{1} (ρ r) 1))
                        (And
                          (∀ (i j : Fin q),
                            Eq.{1} (M i j) (HMul.hMul.{0, 0, 0} γ (PlanarHom.Boolean.tensor ρ (e i) (e j))))
                          (And (∀ (i : Fin q), Eq.{1} (w i) μ)
                            (Eq.{1}
                              (Matrix.rank.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0} (PlanarHom.CenteredLogTensorExpansion.sourceCentering q)
                                    (PlanarHom.CenteredLogTensorExpansion.entrywiseLog M))
                                  (PlanarHom.CenteredLogTensorExpansion.sourceCentering q)))
                              d))))))) :=
  sorry

/-- Paper item 12.4. -/
noncomputable def item_12_4_2 :
  (∀ {q d : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0)
    (e : Equiv.{1, 1} (Fin q) (PlanarHom.Boolean.Cube d)) (γ μ : Real),
    LT.lt.{0} 0 γ →
      LT.lt.{0} 0 μ →
        ∀ (ρ : Fin d → Real),
          (∀ (r : Fin d), And (LT.lt.{0} 0 (ρ r)) (Ne.{1} (ρ r) 1)) →
            (∀ (i j : Fin q),
                Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
                  (HMul.hMul.{0, 0, 0} γ (PlanarHom.Boolean.tensor ρ (e i) (e j)))) →
              (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) μ) →
                PlanarHom.Complexity.PromiseProblem.InFP (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem L)) :=
  sorry

/-- Paper item 12.5. -/
noncomputable def item_12_5_1 :
  (∀ {d e q : Nat} {F : Type} [inst : Field.{0} F]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction d) F]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction d) F) (φ : RingHom.{0, 0} F Real),
    LE.le.{0} 2 q →
      ∀ (K : Real) (M : Matrix.{0, 0, 0} (Fin q) (Fin q) F) (w : Fin q → F),
        (∀ (i j : Fin q), Eq.{1} (φ (M i j)) (PlanarHom.ClockModel.interaction q K i j)) →
          (∀ (i : Fin q), LT.lt.{0} 0 (φ (w i))) →
            And (Eq.{1} K 0 → PlanarHom.RepresentedBit.Problem.InFP (PlanarHom.FixedRealPhysicalModels.problem basis M w))
              (Ne.{1} K 0 →
                And
                  (And (Or (Eq.{1} q 2) (Eq.{1} q 4))
                      (∃ (μ : Real), And (LT.lt.{0} 0 μ) (∀ (i : Fin q), Eq.{1} (φ (w i)) μ)) →
                    PlanarHom.RepresentedBit.Problem.InFP (PlanarHom.FixedRealPhysicalModels.problem basis M w))
                  (Not
                      (And (Or (Eq.{1} q 2) (Eq.{1} q 4))
                        (∃ (μ : Real), And (LT.lt.{0} 0 μ) (∀ (i : Fin q), Eq.{1} (φ (w i)) μ))) →
                    PlanarHom.RepresentedBit.SharpPHard (PlanarHom.FixedRealPhysicalModels.problem basis M w)))) :=
  sorry

/-- Paper item 12.6. -/
noncomputable def item_12_6_1 :
  (∀ {d e n : Nat} {F : Type} [inst : Field.{0} F]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction d) F]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction d) F) (φ : RingHom.{0, 0} F Real)
    (A : Finset.{0} (PlanarHom.BinaryCharacters.Space n)),
    0 ∉ A →
      ∀ (J : PlanarHom.BinaryCharacters.Space n → Real),
        (∀ (a : PlanarHom.BinaryCharacters.Space n), Membership.mem.{0, 0} A a → Ne.{1} (J a) 0) →
          ∀ (M : Matrix.{0, 0, 0} (PlanarHom.BinaryCharacters.Space n) (PlanarHom.BinaryCharacters.Space n) F)
            (w : PlanarHom.BinaryCharacters.Space n → F),
            (∀ (x y : PlanarHom.BinaryCharacters.Space n),
                Eq.{1} (φ (M x y))
                  (PlanarHom.CoupledIsing.interaction (PlanarHom.CoupledIsing.setLabels A)
                    (PlanarHom.CoupledIsing.setCouplings A J) x y)) →
              (∀ (x : PlanarHom.BinaryCharacters.Space n), LT.lt.{0} 0 (φ (w x))) →
                And
                  (And
                      (LinearIndependent.{0, 0, 0} PlanarHom.BinaryCharacters.F₂
                        fun (a : Subtype.{1} fun (x : PlanarHom.BinaryCharacters.Space n) => Membership.mem.{0, 0} A x) =>
                        (a.val : PlanarHom.BinaryCharacters.Space n))
                      (∃ (μ : Real),
                        And (LT.lt.{0} 0 μ)
                          (∀ (z : ↥(PlanarHom.CoupledIsing.ImageSpace (PlanarHom.CoupledIsing.setLabels A))),
                            Eq.{1}
                              (PlanarHom.CoupledIsing.aggregatedWeight (PlanarHom.CoupledIsing.setLabels A)
                                (fun (x : PlanarHom.BinaryCharacters.Space n) => φ (w x)) z)
                              μ)) →
                    PlanarHom.RepresentedBit.Problem.InFP (PlanarHom.FixedRealPhysicalModels.problem basis M w))
                  (Not
                      (And
                        (LinearIndependent.{0, 0, 0} PlanarHom.BinaryCharacters.F₂
                          fun
                            (a : Subtype.{1} fun (x : PlanarHom.BinaryCharacters.Space n) => Membership.mem.{0, 0} A x) =>
                          (a.val : PlanarHom.BinaryCharacters.Space n))
                        (∃ (μ : Real),
                          And (LT.lt.{0} 0 μ)
                            (∀ (z : ↥(PlanarHom.CoupledIsing.ImageSpace (PlanarHom.CoupledIsing.setLabels A))),
                              Eq.{1}
                                (PlanarHom.CoupledIsing.aggregatedWeight (PlanarHom.CoupledIsing.setLabels A)
                                  (fun (x : PlanarHom.BinaryCharacters.Space n) => φ (w x)) z)
                                μ))) →
                    PlanarHom.RepresentedBit.SharpPHard (PlanarHom.FixedRealPhysicalModels.problem basis M w))) :=
  sorry

/-- Paper item 12.6. -/
noncomputable def item_12_6_2 :
  (∀ {d e n : Nat} {F : Type} [inst : Field.{0} F]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction d) F]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction d) F) (φ : RingHom.{0, 0} F Real)
    (a : Fin 0 → PlanarHom.BinaryCharacters.Space n) (J : Fin 0 → Real)
    (M : Matrix.{0, 0, 0} (PlanarHom.BinaryCharacters.Space n) (PlanarHom.BinaryCharacters.Space n) F)
    (w : PlanarHom.BinaryCharacters.Space n → F),
    (∀ (x y : PlanarHom.BinaryCharacters.Space n), Eq.{1} (φ (M x y)) (PlanarHom.CoupledIsing.interaction a J x y)) →
      PlanarHom.RepresentedBit.Problem.InFP (PlanarHom.FixedRealPhysicalModels.problem basis M w)) :=
  sorry

/-- Paper item 12.7. -/
noncomputable def item_12_7_1 :
  (∀ {d e : Nat} {F : Type} [inst : Field.{0} F]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction d) F]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction d) F) (φ : RingHom.{0, 0} F Real)
    (K D H : Real) (M : Matrix.{0, 0, 0} (Fin 3) (Fin 3) F) (w : Fin 3 → F),
    (∀ (i j : Fin 3), Eq.{1} (φ (M i j)) (PlanarHom.BlumeCapel.interaction K i j)) →
      (∀ (i : Fin 3), Eq.{1} (φ (w i)) (PlanarHom.BlumeCapel.weight D H i)) →
        And (Eq.{1} K 0 → PlanarHom.RepresentedBit.Problem.InFP (PlanarHom.FixedRealPhysicalModels.problem basis M w))
          (Ne.{1} K 0 → PlanarHom.RepresentedBit.SharpPHard (PlanarHom.FixedRealPhysicalModels.problem basis M w))) :=
  sorry

/-- Paper item 12.8. -/
noncomputable def item_12_8_1 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0) (ambient : Nat),
    (∀ (i : Fin q), Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i) 1) →
      (∀ (i j : Fin q),
          Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
            (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)) →
        (∀ (i j : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
          And
            (PlanarHom.Structures.NonnegativeClass.{0}
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0) →
              PlanarHom.Complexity.PromiseProblem.InFP
                (PlanarHom.SurfaceRawEmbedding.evaluationProblem ambient
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.basis L)
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matricesK L)
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unariesK L)
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weightsK L)))
            (Not
                (PlanarHom.Structures.NonnegativeClass.{0}
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)) →
              PlanarHom.Complexity.PromisedSharpPHard
                (PlanarHom.SurfaceRawEmbedding.evaluationProblem ambient
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.basis L)
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matricesK L)
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unariesK L)
                  (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weightsK L)))) :=
  sorry

/-- Paper item 12.8. -/
noncomputable def item_12_8_2 :
  (∀ {q : Nat} (L : PlanarHom.AlgebraicProductInterpolation.RealLanguage q 1 0) (ambient : Nat)
    (hs :
      ∀ (i j : Fin q),
        Eq.{1} (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)
          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 j i)),
    (∀ (i j : Fin q), LE.le.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0 i j)) →
      (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L i)) →
        And
          (PlanarHom.Structures.PositiveVertexWeightClass.{0}
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)
              (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L) hs →
            PlanarHom.Complexity.PromiseProblem.InFP
              (PlanarHom.SurfaceRawEmbedding.evaluationProblem ambient
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.basis L)
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matricesK L)
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unariesK L)
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weightsK L)))
          (Not
              (PlanarHom.Structures.PositiveVertexWeightClass.{0}
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matrices L 0)
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weights L) hs) →
            PlanarHom.Complexity.PromisedSharpPHard
              (PlanarHom.SurfaceRawEmbedding.evaluationProblem ambient
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.basis L)
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.matricesK L)
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.unariesK L)
                (PlanarHom.AlgebraicProductInterpolation.RealLanguage.weightsK L)))) :=
  sorry

/-- Paper item A.1. -/
noncomputable def item_A_1_1 :
  (∀ {d e : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction d) K]
    (basis : PlanarHom.FixedRealLemmaA1.PresentationBasis d e K), PlanarHom.FixedRealLemmaA1.LemmaA1Statement basis) :=
  sorry

/-- Paper item A.2. -/
noncomputable def item_A_2_1 :
  ({d e c f s z b u : Nat} →
    {K F S C : Type} →
      [inst : Field.{0} K] →
        [inst_1 : Field.{0} F] →
          [inst_2 : Field.{0} S] →
            [inst_3 : Fintype.{0} C] →
              [inst_4 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction d) K] →
                [inst_5 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction c) F] →
                  [inst_6 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction s) S] →
                    [inst_7 : LinearOrder.{0} K] →
                      [IsStrictOrderedRing.{0} K] →
                        Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction d) K →
                          (targetBasis :
                              Module.Basis.{0, 0, 0} (Fin f) (PlanarHom.DensePolynomial.RationalFunction c) F) →
                            (targetEmbed : RingHom.{0, 0} F K) →
                              (sourceBasis :
                                  Module.Basis.{0, 0, 0} (Fin z) (PlanarHom.DensePolynomial.RationalFunction s) S) →
                                (sourceEmbed : RingHom.{0, 0} S K) →
                                  (MS : Fin b → Matrix.{0, 0, 0} C C S) →
                                    (US : Fin u → C → S) →
                                      (wS : C → S) →
                                        (MT : Fin b → Matrix.{0, 0, 0} C C F) →
                                          (UT : Fin u → C → F) →
                                            (wT : C → F) →
                                              (Eq.{1} (fun (l : Fin b) (i j : C) => targetEmbed (MT l i j))
                                                  fun (l : Fin b) (i j : C) => sourceEmbed (MS l i j)) →
                                                (Eq.{1} (fun (l : Fin u) (i : C) => targetEmbed (UT l i))
                                                    fun (l : Fin u) (i : C) => sourceEmbed (US l i)) →
                                                  (Eq.{1} (fun (i : C) => targetEmbed (wT i)) fun (i : C) =>
                                                      sourceEmbed (wS i)) →
                                                    (∀ (i : C), LT.lt.{0} 0 (sourceEmbed (wS i))) →
                                                      (X : Set.{0} C) →
                                                        PlanarHom.RepresentedBit.Reduction
                                                          (PlanarHom.FixedRealMixedRootRestriction.rootProblem targetBasis
                                                            MT UT wT X)
                                                          (PlanarHom.FixedRealComponents.problem sourceBasis MS US wS)) :=
  sorry

/-- Paper item A.2. -/
noncomputable def item_A_2_2 :
  ({d e c f s z b u : Nat} →
    {K F S C : Type} →
      [inst : Field.{0} K] →
        [inst_1 : Field.{0} F] →
          [inst_2 : Field.{0} S] →
            [inst_3 : Fintype.{0} C] →
              [inst_4 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction d) K] →
                [inst_5 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction c) F] →
                  [inst_6 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction s) S] →
                    [inst_7 : LinearOrder.{0} K] →
                      [IsStrictOrderedRing.{0} K] →
                        Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction d) K →
                          (targetBasis :
                              Module.Basis.{0, 0, 0} (Fin f) (PlanarHom.DensePolynomial.RationalFunction c) F) →
                            (targetEmbed : RingHom.{0, 0} F K) →
                              (sourceBasis :
                                  Module.Basis.{0, 0, 0} (Fin z) (PlanarHom.DensePolynomial.RationalFunction s) S) →
                                (sourceEmbed : RingHom.{0, 0} S K) →
                                  (MS : Fin b → Matrix.{0, 0, 0} C C S) →
                                    (US : Fin u → C → S) →
                                      (wS : C → S) →
                                        (MT : Fin b → Matrix.{0, 0, 0} C C F) →
                                          (UT : Fin u → C → F) →
                                            (wT : C → F) →
                                              (Eq.{1} (fun (l : Fin b) (i j : C) => targetEmbed (MT l i j))
                                                  fun (l : Fin b) (i j : C) => sourceEmbed (MS l i j)) →
                                                (Eq.{1} (fun (l : Fin u) (i : C) => targetEmbed (UT l i))
                                                    fun (l : Fin u) (i : C) => sourceEmbed (US l i)) →
                                                  (Eq.{1} (fun (i : C) => targetEmbed (wT i)) fun (i : C) =>
                                                      sourceEmbed (wS i)) →
                                                    (∀ (i : C), LT.lt.{0} 0 (sourceEmbed (wS i))) →
                                                      (∀ (l : Fin b) (i j : C),
                                                          Eq.{1} (sourceEmbed (MS l i j)) (sourceEmbed (MS l j i))) →
                                                        (X : Set.{0} C) →
                                                          PlanarHom.MixedRootedRestriction.CommonClosed
                                                              (fun (l : Fin b) (i j : C) => sourceEmbed (MS l i j)) X →
                                                            PlanarHom.RepresentedBit.Reduction
                                                              (PlanarHom.FixedRealComponents.problem targetBasis
                                                                (fun (l : Fin b) (i j : ↑X) => MT l ↑i ↑j)
                                                                (fun (l : Fin u) (i : ↑X) => UT l ↑i) fun (i : ↑X) =>
                                                                wT ↑i)
                                                              (PlanarHom.FixedRealComponents.problem sourceBasis MS US wS)) :=
  sorry

/-- Paper item A.2. -/
noncomputable def item_A_2_3 :
  ({d e c f s z b u : Nat} →
    {K F S C : Type} →
      [inst : Field.{0} K] →
        [inst_1 : Field.{0} F] →
          [inst_2 : Field.{0} S] →
            [inst_3 : Fintype.{0} C] →
              [inst_4 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction d) K] →
                [inst_5 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction c) F] →
                  [inst_6 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction s) S] →
                    [inst_7 : LinearOrder.{0} K] →
                      [IsStrictOrderedRing.{0} K] →
                        Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction d) K →
                          (targetBasis :
                              Module.Basis.{0, 0, 0} (Fin f) (PlanarHom.DensePolynomial.RationalFunction c) F) →
                            (targetEmbed : RingHom.{0, 0} F K) →
                              (sourceBasis :
                                  Module.Basis.{0, 0, 0} (Fin z) (PlanarHom.DensePolynomial.RationalFunction s) S) →
                                (sourceEmbed : RingHom.{0, 0} S K) →
                                  (MS : Fin b → Matrix.{0, 0, 0} C C S) →
                                    (US : Fin u → C → S) →
                                      (wS : C → S) →
                                        (MT : Fin b → Matrix.{0, 0, 0} C C F) →
                                          (UT : Fin u → C → F) →
                                            (wT : C → F) →
                                              (Eq.{1} (fun (l : Fin b) (i j : C) => targetEmbed (MT l i j))
                                                  fun (l : Fin b) (i j : C) => sourceEmbed (MS l i j)) →
                                                (Eq.{1} (fun (l : Fin u) (i : C) => targetEmbed (UT l i))
                                                    fun (l : Fin u) (i : C) => sourceEmbed (US l i)) →
                                                  (Eq.{1} (fun (i : C) => targetEmbed (wT i)) fun (i : C) =>
                                                      sourceEmbed (wS i)) →
                                                    (∀ (i : C), LT.lt.{0} 0 (sourceEmbed (wS i))) →
                                                      (∀ (l : Fin b) (i j : C),
                                                          Eq.{1} (sourceEmbed (MS l i j)) (sourceEmbed (MS l j i))) →
                                                        (side : C → Bool) →
                                                          (∀ (l : Fin b) (i j : C),
                                                              Ne.{1} (sourceEmbed (MS l i j)) 0 →
                                                                Ne.{1} (side i) (side j)) →
                                                            PlanarHom.RepresentedBit.Reduction
                                                              (PlanarHom.FixedRealMixedOrientation.problem targetBasis MT
                                                                UT wT side)
                                                              (PlanarHom.FixedRealComponents.problem sourceBasis MS US wS)) :=
  sorry

/-- Paper item A.3. -/
noncomputable def item_A_3_1 :
  ({d e c f s z q b u r v : Nat} →
    {K F S : Type} →
      [inst : Field.{0} K] →
        [inst_1 : Field.{0} F] →
          [inst_2 : Field.{0} S] →
            [inst_3 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction d) K] →
              [inst_4 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction c) F] →
                [inst_5 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction s) S] →
                  Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction d) K →
                    (targetBasis : Module.Basis.{0, 0, 0} (Fin f) (PlanarHom.DensePolynomial.RationalFunction c) F) →
                      (targetEmbed : RingHom.{0, 0} F K) →
                        (sourceBasis : Module.Basis.{0, 0, 0} (Fin z) (PlanarHom.DensePolynomial.RationalFunction s) S) →
                          (sourceEmbed : RingHom.{0, 0} S K) →
                            (MS : Fin b → Matrix.{0, 0, 0} (Fin q) (Fin q) S) →
                              (US : Fin u → Fin q → S) →
                                (wS : Fin q → S) →
                                  (MT : Fin b → Matrix.{0, 0, 0} (Fin q) (Fin q) F) →
                                    (UT : Fin u → Fin q → F) →
                                      (wT : Fin q → F) →
                                        (N : Fin r → Matrix.{0, 0, 0} (Fin q) (Fin q) F) →
                                          (V : Fin v → Fin q → F) →
                                            (∀ (l : Fin b) (i j : Fin q),
                                                Eq.{1} (targetEmbed (MT l i j)) (sourceEmbed (MS l i j))) →
                                              (∀ (l : Fin u) (i : Fin q),
                                                  Eq.{1} (targetEmbed (UT l i)) (sourceEmbed (US l i))) →
                                                (∀ (i : Fin q), Eq.{1} (targetEmbed (wT i)) (sourceEmbed (wS i))) →
                                                  (oldM : Fin r → Fin b) →
                                                    (oldU : Fin v → Fin u) →
                                                      (∀ (l : Fin r) (i j : Fin q),
                                                          Eq.{1} (sourceEmbed (MS (oldM l) i j)) 0 →
                                                            Eq.{1} (targetEmbed (N l i j)) 0) →
                                                        (∀ (l : Fin r),
                                                            PlanarHom.ProductCompatibility.HasProductMaps
                                                              (fun (p : Prod.{0, 0} (Fin q) (Fin q)) =>
                                                                sourceEmbed (MS (oldM l) p.1 p.2))
                                                              fun (p : Prod.{0, 0} (Fin q) (Fin q)) =>
                                                              targetEmbed (N l p.1 p.2)) →
                                                          (∀ (l : Fin v) (i : Fin q),
                                                              Eq.{1} (sourceEmbed (US (oldU l) i)) 0 →
                                                                Eq.{1} (targetEmbed (V l i)) 0) →
                                                            (∀ (l : Fin v),
                                                                PlanarHom.ProductCompatibility.HasProductMaps
                                                                  (fun (i : Fin q) => sourceEmbed (US (oldU l) i))
                                                                  fun (i : Fin q) => targetEmbed (V l i)) →
                                                              (base : PlanarHom.RepresentedBit.Problem) →
                                                                PlanarHom.RepresentedBit.Reduction
                                                                    (PlanarHom.FixedRealMixedInterpolation.problem
                                                                      sourceBasis MS US wS)
                                                                    base →
                                                                  PlanarHom.RepresentedBit.Reduction
                                                                    (PlanarHom.FixedRealMixedInterpolation.problem
                                                                      targetBasis
                                                                      (PlanarHom.FiniteLanguageAliases.appendFamily MT N)
                                                                      (PlanarHom.FiniteLanguageAliases.appendFamily UT V)
                                                                      wT)
                                                                    base) :=
  sorry

/-- Paper item A.4. -/
noncomputable def item_A_4_1.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] (m : ι → Real),
    (∀ (i : ι), Ne.{1} (m i) 0) →
      ∀ (δ : Real),
        LT.lt.{0} 0 δ →
          ∃ (q : ι → Rat),
            And (∀ (i : ι), Ne.{1} (q i) 0)
              (And (∀ (i : ι), LT.lt.{0} (abs.{0} (HSub.hSub.{0, 0, 0} (↑(q i)) (m i))) δ)
                (And (∀ (i : ι), Eq.{1} (Real.sign ↑(q i)) (Real.sign (m i)))
                  (∀ (z : ι → Int),
                    Eq.{1} (∏ i : ι, HPow.hPow.{0, 0, 0} (m i) (z i)) 1 →
                      Eq.{1} (∏ i : ι, HPow.hPow.{0, 0, 0} (q i) (z i)) 1)))) :=
  sorry

/-- Paper item A.4. -/
noncomputable def item_A_4_2 :
  (∀ {n e q b u : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Fin b → Matrix.{0, 0, 0} (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K),
    (∀ (l : Fin b) (i j : Fin q), Eq.{1} (M l i j) (M l j i)) →
      ∀ (δ : Real),
        LT.lt.{0} 0 δ →
          ∀ (base : PlanarHom.RepresentedBit.Problem)
            (available :
              PlanarHom.RepresentedBit.Reduction (PlanarHom.FixedRealMixedInterpolation.problem basis M U w) base),
            ∃ (N : Fin b → Matrix.{0, 0, 0} (Fin q) (Fin q) Rat),
              And (∀ (l : Fin b) (i j : Fin q), Eq.{1} (N l i j) (N l j i))
                (And (∀ (l : Fin b) (i j : Fin q), Iff (Eq.{1} (N l i j) 0) (Eq.{1} (M l i j) 0))
                  (And
                    (∀ (l : Fin b) (i j : Fin q), LT.lt.{0} (abs.{0} (HSub.hSub.{0, 0, 0} (↑(N l i j)) (φ (M l i j)))) δ)
                    (And (∀ (l : Fin b) (i j : Fin q), Eq.{1} (Real.sign ↑(N l i j)) (Real.sign (φ (M l i j))))
                      (Nonempty.{2}
                        (PlanarHom.RepresentedBit.Reduction
                          (PlanarHom.FixedRealMixedInterpolation.problem basis
                            (PlanarHom.FiniteLanguageAliases.appendFamily M fun (l : Fin b) (i j : Fin q) => ↑(N l i j)) U
                            w)
                          base)))))) :=
  sorry

/-- Paper item A.4. -/
noncomputable def item_A_4_3 :
  (∀ {n e q : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin q) (Fin q) K),
    (∀ (i j : Fin q), Eq.{1} (M i j) (M j i)) →
      ∀ (δ : Real),
        LT.lt.{0} 0 δ →
          ∃ (N : Matrix.{0, 0, 0} (Fin q) (Fin q) Rat),
            And (∀ (i j : Fin q), Eq.{1} (N i j) (N j i))
              (And (∀ (i j : Fin q), Iff (Eq.{1} (N i j) 0) (Eq.{1} (M i j) 0))
                (And (∀ (i j : Fin q), LT.lt.{0} (abs.{0} (HSub.hSub.{0, 0, 0} (↑(N i j)) (φ (M i j)))) δ)
                  (And (∀ (i j : Fin q), Eq.{1} (Real.sign ↑(N i j)) (Real.sign (φ (M i j))))
                    (Nonempty.{2}
                      (PlanarHom.RepresentedBit.Reduction
                        (PlanarHom.RepresentedBit.ofCanonical
                          (PlanarHom.AlgebraicProductInterpolation.RealLanguage.problem
                            (PlanarHom.FixedRealApproximation.rationalLanguage N)))
                        (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                          (fun (l : Fin 0) => Fin.elim0.{1} l) fun (x : Fin q) => 1))))))) :=
  sorry

/-- Paper item A.5. -/
noncomputable def item_A_5_1.{u_1} :
  (∀ {C : Type u_1} [Fintype.{u_1} C] (P : C → C → Prop),
    IsClosed.{u_1}
      (setOf.{u_1} fun (M : PlanarHom.FixedChartClosedness.SupportMatrix.{u_1, u_1} P) =>
        PlanarHom.Structures.NonnegativeClass.{u_1} M.val)) :=
  sorry

/-- Paper item A.5. -/
noncomputable def item_A_5_2.{u_1, u_2} :
  (∀ {C : Type u_1} {A : Type u_2} [Fintype.{u_1} C] {f : Filter.{u_2} A} [Filter.NeBot.{u_2} f]
    (P : C → C → Prop) (M : A → C → C → Real) (L : C → C → Real),
    (∀ (n : A), PlanarHom.FixedChartClosedness.HasSupport.{u_1, u_1} P (M n)) →
      PlanarHom.FixedChartClosedness.HasSupport.{u_1, u_1} P L →
        (∀ (n : A), PlanarHom.Structures.NonnegativeClass.{u_1} (M n)) →
          (∀ (i j : C), Filter.Tendsto.{u_2, 0} (fun (n : A) => M n i j) f (nhds.{0} (L i j))) →
            PlanarHom.Structures.NonnegativeClass.{u_1} L) :=
  sorry

/-- Paper item A.6. -/
noncomputable def item_A_6_1 :
  (∀ {n e q : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin q) (Fin q) K),
    (∀ (i j : Fin q), Eq.{1} (M i j) (M j i)) →
      (∀ (i j : Fin q), LE.le.{0} 0 (φ (M i j))) →
        And
          ((PlanarHom.Structures.NonnegativeClass.{0} fun (i j : Fin q) => φ (M i j)) →
            PlanarHom.RepresentedBit.Problem.InFP
              (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                (fun (l : Fin 0) => Fin.elim0.{1} l) fun (x : Fin q) => 1))
          (Not (PlanarHom.Structures.NonnegativeClass.{0} fun (i j : Fin q) => φ (M i j)) →
            PlanarHom.RepresentedBit.SharpPHard
              (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                (fun (l : Fin 0) => Fin.elim0.{1} l) fun (x : Fin q) => 1))) :=
  sorry

/-- Paper item A.7. -/
noncomputable def item_A_7_1 :
  (∀ {n e q b u : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Fin b → Matrix.{0, 0, 0} (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) (selected : Fin b),
    Ne.{1} (M selected) 0 →
      ∀ (base : PlanarHom.RepresentedBit.Problem)
        (available : PlanarHom.RepresentedBit.Reduction (PlanarHom.FixedRealMixedInterpolation.problem basis M U w) base),
        ∃ (a : Real) (z : Real),
          And (LT.lt.{0} 0 a)
            (And (LT.lt.{0} 0 z)
              (And (∃ (i : Fin q) (j : Fin q), Eq.{1} (abs.{0} (φ (M selected i j))) a)
                (And (∃ (i : Fin q) (j : Fin q), Eq.{1} (abs.{0} (φ (M selected i j))) z)
                  (And (∀ (i j : Fin q), Ne.{1} (M selected i j) 0 → LE.le.{0} a (abs.{0} (φ (M selected i j))))
                    (And (∀ (i j : Fin q), LE.le.{0} (abs.{0} (φ (M selected i j))) z)
                      (Nonempty.{2}
                        (PlanarHom.RepresentedBit.Reduction
                          (PlanarHom.FixedRealMixedInterpolation.problem basis
                            (PlanarHom.FiniteLanguageAliases.appendFamily
                              (PlanarHom.FiniteLanguageAliases.appendFamily M
                                (PlanarHom.FixedRealSignedTransforms.transform φ (M selected)))
                              (PlanarHom.FixedRealSignedTransforms.extremalTransforms φ (M selected) a z))
                            U w)
                          base)))))))) :=
  sorry

/-- Paper item A.7. -/
noncomputable def item_A_7_2 :
  (∀ {n e q u : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K),
    And
      (Nonempty.{2}
        (PlanarHom.RepresentedBit.Reduction
          (PlanarHom.FixedRealMixedInterpolation.problem basis
            (fun (x : Fin 1) (i j : Fin q) => PlanarHom.FixedRealSignedTransforms.support (M i j)) U w)
          (PlanarHom.FixedRealMixedInterpolation.problem basis
            (fun (x : Fin 1) (i j : Fin q) => PlanarHom.FixedRealSignedTransforms.magnitude φ (M i j)) U w)))
      (Nonempty.{2}
        (PlanarHom.RepresentedBit.Reduction
          (PlanarHom.FixedRealMixedInterpolation.problem basis
            (fun (x : Fin 1) (i j : Fin q) => PlanarHom.FixedRealSignedTransforms.magnitude φ (M i j)) U w)
          (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M) U w)))) :=
  sorry

/-- Paper item A.7. -/
noncomputable def item_A_7_3 :
  (∀ {n e q u : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K),
    And
      (Nonempty.{2}
        (PlanarHom.RepresentedBit.Reduction
          (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M) U w)
          (PlanarHom.FixedRealMixedInterpolation.problem basis (PlanarHom.FixedRealSignedTransforms.mixed φ M) U w)))
      (Nonempty.{2}
        (PlanarHom.RepresentedBit.Reduction
          (PlanarHom.FixedRealMixedInterpolation.problem basis (PlanarHom.FixedRealSignedTransforms.mixed φ M) U w)
          (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M) U w)))) :=
  sorry

/-- Paper item A.8. -/
noncomputable def item_A_8_1 :
  ({n e c f q bt ut : Nat} →
    {K F : Type} →
      [inst : Field.{0} K] →
        [inst_1 : Field.{0} F] →
          [inst_2 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K] →
            [inst_3 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction c) F] →
              [inst_4 : Algebra.{0, 0} K Real] →
                (sourceBasis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) →
                  (targetBasis : Module.Basis.{0, 0, 0} (Fin f) (PlanarHom.DensePolynomial.RationalFunction c) F) →
                    (embed : RingHom.{0, 0} F K) →
                      (M : Fin bt → Matrix.{0, 0, 0} (Fin q) (Fin q) F) →
                        (U : Fin ut → Fin q → F) →
                          (w : Fin q → K) →
                            (old : Fin bt) →
                              (∀ (i j : Fin q),
                                  Eq.{1} ((algebraMap.{0, 0} K Real) (embed (M old i j)))
                                    ((algebraMap.{0, 0} K Real) (embed (M old j i)))) →
                                (∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.RelativeWeightedSpectralField.realWeights w i)) →
                                  (∀ (i : Fin q),
                                      Ne.{1} (fun (j : Fin q) => (algebraMap.{0, 0} K Real) (embed (M old i j))) 0) →
                                    (∀ (i j : Fin q),
                                        Ne.{1} i j →
                                          ∀ (t : Real),
                                            Ne.{1} (fun (k : Fin q) => (algebraMap.{0, 0} K Real) (embed (M old i k)))
                                              (HSMul.hSMul.{0, 0, 0} t fun (k : Fin q) =>
                                                (algebraMap.{0, 0} K Real) (embed (M old j k)))) →
                                      PlanarHom.RepresentedBit.Reduction
                                        (PlanarHom.FixedRealMixedInterpolation.problem targetBasis M U fun (x : Fin q) =>
                                          1)
                                        (PlanarHom.FixedRealMixedInterpolation.problem sourceBasis
                                          (fun (l : Fin bt) (i j : Fin q) => embed (M l i j))
                                          (fun (l : Fin ut) (i : Fin q) => embed (U l i)) w)) :=
  sorry

/-- Paper item A.8. -/
noncomputable def item_A_8_2 :
  ({n e q bt ut s : Nat} →
    {F : Type} →
      [inst : Field.{0} F] →
        [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) F] →
          [inst_2 : Algebra.{0, 0} F Real] →
            (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) F) →
              (M : Fin bt → Matrix.{0, 0, 0} (Fin q) (Fin q) F) →
                (U : Fin ut → Fin q → F) →
                  (w : Fin q → F) →
                    (old : Fin bt) →
                      (∀ (i j : Fin q),
                          Eq.{1} (PlanarHom.RelativeWeightedSpectralField.realMatrix (M old) i j)
                            (PlanarHom.RelativeWeightedSpectralField.realMatrix (M old) j i)) →
                        (hw : ∀ (i : Fin q), LT.lt.{0} 0 (PlanarHom.RelativeWeightedSpectralField.realWeights w i)) →
                          (∀ (i : Fin q), Ne.{1} (PlanarHom.RelativeWeightedSpectralField.realMatrix (M old) i) 0) →
                            (∀ (i j : Fin q),
                                Ne.{1} i j →
                                  ∀ (t : Real),
                                    Ne.{1} (PlanarHom.RelativeWeightedSpectralField.realMatrix (M old) i)
                                      (HSMul.hSMul.{0, 0, 0} t
                                        (PlanarHom.RelativeWeightedSpectralField.realMatrix (M old) j))) →
                              (r : Fin s → Rat) →
                                have P := PlanarHom.FixedRealWeightRemoval.powerModel basis w hw r;
                                PlanarHom.RepresentedBit.Reduction
                                  (PlanarHom.FixedRealMixedInterpolation.problem
                                    (PlanarHom.FixedRealWeightRemoval.PowerModel.basis P)
                                    (PlanarHom.FixedRealWeightRemoval.powerMatrices
                                      (fun (l : Fin bt) (i j : Fin q) =>
                                        (PlanarHom.FixedRealWeightRemoval.PowerModel.inclusion P) (M l i j))
                                      (fun (i : Fin q) => (PlanarHom.FixedRealWeightRemoval.PowerModel.inclusion P) (w i))
                                      (PlanarHom.FixedRealWeightRemoval.PowerModel.powers P))
                                    (PlanarHom.FixedRealWeightRemoval.powerUnaries
                                      (fun (l : Fin ut) (i : Fin q) =>
                                        (PlanarHom.FixedRealWeightRemoval.PowerModel.inclusion P) (U l i))
                                      (PlanarHom.FixedRealWeightRemoval.PowerModel.powers P))
                                    fun (x : Fin q) => 1)
                                  (PlanarHom.FixedRealMixedInterpolation.problem basis M U w)) :=
  sorry

/-- Paper item A.9. -/
noncomputable def item_A_9_1 :
  (∀ {n e q : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin q) (Fin q) K) (hs : ∀ (i j : Fin q), Eq.{1} (M i j) (M j i)) (w : Fin q → K),
    (∀ (i : Fin q), LT.lt.{0} 0 (φ (w i))) →
      (∀ (i j : Fin q), Or (Eq.{1} (M i j) 0) (Eq.{1} (M i j) 1)) →
        And
          (PlanarHom.FixedRealSupportHardness.BasicSupport φ M hs →
            PlanarHom.RepresentedBit.Problem.InFP
              (PlanarHom.FixedRealComponents.problem basis (fun (x : Fin 1) => M) (fun (i : Fin 0) => Fin.elim0.{1} i) w))
          (Not (PlanarHom.FixedRealSupportHardness.BasicSupport φ M hs) →
            PlanarHom.RepresentedBit.SharpPHard
              (PlanarHom.FixedRealComponents.problem basis (fun (x : Fin 1) => M) (fun (i : Fin 0) => Fin.elim0.{1} i) w))) :=
  sorry

/-- Paper item A.9. -/
noncomputable def item_A_9_2 :
  (∀ {n e q : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin q) (Fin q) K) (hs : ∀ (i j : Fin q), Eq.{1} (M i j) (M j i)) (w : Fin q → K),
    (∀ (i : Fin q), LT.lt.{0} 0 (φ (w i))) →
      (∃ (c :
          SimpleGraph.ConnectedComponent.{0}
            (PlanarHom.RootedRestriction.colorSupport (fun (i j : Fin q) => φ (M i j)) fun (i j : Fin q) =>
              congrArg.{1, 1} (⇑φ) (hs i j))),
          Not
            (PlanarHom.ZeroOneBasicStructure.BasicZeroOneComponent
              fun (i j : ↑(SimpleGraph.ConnectedComponent.supp.{0} c)) => ite.{1} (Eq.{1} (φ (M ↑i ↑j)) 0) 0 1)) →
        PlanarHom.RepresentedBit.SharpPHard
          (PlanarHom.FixedRealComponents.problem basis (fun (x : Fin 1) => M) (fun (i : Fin 0) => Fin.elim0.{1} i) w)) :=
  sorry

/-- Paper item A.10. -/
noncomputable def item_A_10_1 :
  (∀ {n e d : Nat} {F : Type} [inst : Field.{0} F]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) F] [inst_2 : Algebra.{0, 0} F Real]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) F) (ρ : Fin d → F),
    (∀ (j : Fin d), LT.lt.{0} 0 ((algebraMap.{0, 0} F Real) (ρ j))) →
      (∀ (j : Fin d), Ne.{1} ((algebraMap.{0, 0} F Real) (ρ j)) 1) →
        ∀ (u : PlanarHom.Boolean.Cube d → F),
          (∀ (i : PlanarHom.Boolean.Cube d), LT.lt.{0} 0 ((algebraMap.{0, 0} F Real) (u i))) →
            And
              ((∀ (i j : PlanarHom.Boolean.Cube d), Eq.{1} (u i) (u j)) →
                PlanarHom.RepresentedBit.Problem.InFP (PlanarHom.FixedRealLemmaA10.problem basis ρ u))
              ((∃ (i : PlanarHom.Boolean.Cube d) (j : PlanarHom.Boolean.Cube d), Ne.{1} (u i) (u j)) →
                PlanarHom.RepresentedBit.SharpPHard (PlanarHom.FixedRealLemmaA10.problem basis ρ u))) :=
  sorry

/-- Paper item A.11. -/
noncomputable def item_A_11_1 :
  (∀ {n e d : Nat} {F : Type} [inst : Field.{0} F]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) F] [inst_2 : Algebra.{0, 0} F Real]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) F) (c : F),
    LT.lt.{0} 0 ((algebraMap.{0, 0} F Real) c) →
      ∀ (ρ : Fin d → F),
        (∀ (j : Fin d), LT.lt.{0} 0 ((algebraMap.{0, 0} F Real) (ρ j))) →
          (∀ (j : Fin d), Ne.{1} ((algebraMap.{0, 0} F Real) (ρ j)) 1) →
            ∀ (μ ν : PlanarHom.Boolean.Cube d → F),
              (∀ (i : PlanarHom.Boolean.Cube d), LT.lt.{0} 0 ((algebraMap.{0, 0} F Real) (μ i))) →
                (∀ (i : PlanarHom.Boolean.Cube d), LT.lt.{0} 0 ((algebraMap.{0, 0} F Real) (ν i))) →
                  And
                    (And (∀ (i j : PlanarHom.Boolean.Cube d), Eq.{1} (μ i) (μ j))
                        (∀ (i j : PlanarHom.Boolean.Cube d), Eq.{1} (ν i) (ν j)) →
                      And (PlanarHom.RepresentedBit.Problem.InFP (PlanarHom.FixedRealLemmaA11.problem basis c ρ μ ν))
                        (PlanarHom.RepresentedBit.Problem.InFP
                          (PlanarHom.FixedRealLemmaA11.prescribedProblem basis c ρ μ ν)))
                    (Or (∃ (i : PlanarHom.Boolean.Cube d) (j : PlanarHom.Boolean.Cube d), Ne.{1} (μ i) (μ j))
                        (∃ (i : PlanarHom.Boolean.Cube d) (j : PlanarHom.Boolean.Cube d), Ne.{1} (ν i) (ν j)) →
                      And (PlanarHom.RepresentedBit.SharpPHard (PlanarHom.FixedRealLemmaA11.problem basis c ρ μ ν))
                        (PlanarHom.RepresentedBit.SharpPHard
                          (PlanarHom.FixedRealLemmaA11.prescribedProblem basis c ρ μ ν)))) :=
  sorry

/-- Paper item A.12. -/
noncomputable def item_A_12_1 :
  (∀ {n e q : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin q) (Fin q) K) (hs : ∀ (i j : Fin q), Eq.{1} (M i j) (M j i)),
    (∀ (i j : Fin q), LE.le.{0} 0 (φ (M i j))) →
      ∀ (w : Fin q → K),
        (∀ (i : Fin q), LT.lt.{0} 0 (φ (w i))) →
          And
            ((PlanarHom.Structures.PositiveVertexWeightClass.{0} (fun (i j : Fin q) => φ (M i j))
                (fun (i : Fin q) => φ (w i)) fun (i j : Fin q) => congrArg.{1, 1} (⇑φ) (hs i j)) →
              PlanarHom.RepresentedBit.Problem.InFP
                (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                  (fun (l : Fin 0) => Fin.elim0.{1} l) w))
            (Not
                (PlanarHom.Structures.PositiveVertexWeightClass.{0} (fun (i j : Fin q) => φ (M i j))
                  (fun (i : Fin q) => φ (w i)) fun (i j : Fin q) => congrArg.{1, 1} (⇑φ) (hs i j)) →
              PlanarHom.RepresentedBit.SharpPHard
                (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                  (fun (l : Fin 0) => Fin.elim0.{1} l) w))) :=
  sorry

/-- Paper item A.13. -/
noncomputable def item_A_13_1 :
  (∀ {n e q : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin q) (Fin q) K) (hs : ∀ (i j : Fin q), Eq.{1} (M i j) (M j i)),
    (∀ (i j : Fin q), LE.le.{0} 0 (φ (M i j))) →
      ∀ (w : Fin q → K),
        (∀ (i : Fin q), LE.le.{0} 0 (φ (w i))) →
          And
            (PlanarHom.FixedRealSurvivingWeights.SurvivingClass φ M w hs →
              PlanarHom.RepresentedBit.Problem.InFP
                (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                  (fun (l : Fin 0) => Fin.elim0.{1} l) w))
            (Not (PlanarHom.FixedRealSurvivingWeights.SurvivingClass φ M w hs) →
              PlanarHom.RepresentedBit.SharpPHard
                (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                  (fun (l : Fin 0) => Fin.elim0.{1} l) w))) :=
  sorry

/-- Paper item A.14. -/
noncomputable def item_A_14_1 :
  (∀ {n e q : Nat} {K : Type} [inst : Field.{0} K]
    [inst_1 : Algebra.{0, 0} (PlanarHom.DensePolynomial.RationalFunction n) K]
    (basis : Module.Basis.{0, 0, 0} (Fin e) (PlanarHom.DensePolynomial.RationalFunction n) K) (φ : RingHom.{0, 0} K Real)
    (M : Matrix.{0, 0, 0} (Fin q) (Fin q) K) (hs : ∀ (i j : Fin q), Eq.{1} (M i j) (M j i)) (w : Fin q → K),
    (∀ (i : Fin q), LT.lt.{0} 0 (φ (w i))) →
      And
        (Nonempty.{2}
          (PlanarHom.RepresentedBit.Reduction
            (PlanarHom.FixedRealMixedInterpolation.problem basis
              (fun (x : Fin 1) (i j : Fin q) => PlanarHom.FixedRealSignedTransforms.support (M i j))
              (fun (l : Fin 0) => Fin.elim0.{1} l) w)
            (PlanarHom.FixedRealMixedInterpolation.problem basis
              (fun (x : Fin 1) (i j : Fin q) => PlanarHom.FixedRealSignedTransforms.magnitude φ (M i j))
              (fun (l : Fin 0) => Fin.elim0.{1} l) w)))
        (And
          (Nonempty.{2}
            (PlanarHom.RepresentedBit.Reduction
              (PlanarHom.FixedRealMixedInterpolation.problem basis
                (fun (x : Fin 1) (i j : Fin q) => PlanarHom.FixedRealSignedTransforms.magnitude φ (M i j))
                (fun (l : Fin 0) => Fin.elim0.{1} l) w)
              (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                (fun (l : Fin 0) => Fin.elim0.{1} l) w)))
          (And
            ((∃ (c :
                SimpleGraph.ConnectedComponent.{0}
                  (PlanarHom.RootedRestriction.colorSupport (fun (i j : Fin q) => φ (M i j)) fun (i j : Fin q) =>
                    congrArg.{1, 1} (⇑φ) (hs i j))),
                Not
                  (PlanarHom.ZeroOneBasicStructure.BasicZeroOneComponent
                    fun (i j : ↑(SimpleGraph.ConnectedComponent.supp.{0} c)) => ite.{1} (Eq.{1} (φ (M ↑i ↑j)) 0) 0 1)) →
              PlanarHom.RepresentedBit.SharpPHard
                (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                  (fun (l : Fin 0) => Fin.elim0.{1} l) w))
            (And
              ((∀ (i : Fin q), Eq.{1} (w i) 1) →
                Not (PlanarHom.Structures.NonnegativeClass.{0} fun (i j : Fin q) => abs.{0} (φ (M i j))) →
                  PlanarHom.RepresentedBit.SharpPHard
                    (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                      (fun (l : Fin 0) => Fin.elim0.{1} l) w))
              ((∀ (i j : Fin q), Or (Eq.{1} (M i j) 0) (Eq.{1} (M i j) 1)) →
                And
                  (PlanarHom.FixedRealSupportHardness.BasicSupport φ M hs →
                    PlanarHom.RepresentedBit.Problem.InFP
                      (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                        (fun (l : Fin 0) => Fin.elim0.{1} l) w))
                  (Not (PlanarHom.FixedRealSupportHardness.BasicSupport φ M hs) →
                    PlanarHom.RepresentedBit.SharpPHard
                      (PlanarHom.FixedRealMixedInterpolation.problem basis (fun (x : Fin 1) => M)
                        (fun (l : Fin 0) => Fin.elim0.{1} l) w))))))) :=
  sorry

end PlanarHomAudit.Comparator
