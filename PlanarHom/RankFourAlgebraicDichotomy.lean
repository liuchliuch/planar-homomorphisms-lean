import PlanarHom.RankFourPositiveRefinement
import PlanarHom.RankFourBooleanOriginalCriterion
import PlanarHom.MainDichotomiesClosed
import PlanarHom.UnitBackgroundLanguage

/-! Theorem 2.4 in the paper's algebraic body model. Rank four is used in
the finite-dimensional structural equivalence, not assumed as a complexity
seed. Both the main hardness and Ising algorithm foundations are closed.
The cited unrestricted fixed-real representation model is a separate scope. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Structures RankFour

theorem theorem2_4 (L:RealLanguage 4 1 0) (hunit:∀i,L.weights i=1)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn:∀i j,0≤L.matrices 0 i j) (hr:(L.matrices 0).rank=4) :
    (FourStateClass (L.matrices 0)→L.problem.InFP) ∧
    (¬FourStateClass (L.matrices 0)→PromisedSharpPHard L.problem) := by
  have h:=MainDichotomyScope.theorem11 L hunit hs hnn
  have he:=nonnegativeClass_iff_fourStateClass hr
  exact ⟨fun hp=>h.1 (he.mpr hp),fun hp=>h.2 (fun hc=>hp (he.mp hc))⟩

theorem theorem2_4_positive (L:RealLanguage 4 1 0) (hunit:∀i,L.weights i=1)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hp:∀i j,0<L.matrices 0 i j) (hr:(L.matrices 0).rank=4) :
    (PositiveFourTensor (L.matrices 0)→L.problem.InFP) ∧
    (¬PositiveFourTensor (L.matrices 0)→PromisedSharpPHard L.problem) := by
  have h:=MainDichotomyScope.theorem11 L hunit hs (fun i j=>(hp i j).le)
  have he:=positive_nonnegativeClass_iff_tensor hp hr
  exact ⟨fun hp=>h.1 (he.mpr hp),fun hp=>h.2 (fun hc=>hp (he.mp hc))⟩

/-- Every structural block mentioned in the displayed split has a genuine
closed algorithm once its entries are specialized to the source algebraic
body model. This does not posit an oracle for either smaller block. -/
theorem class_unitLanguage_inFP {n:ℕ} (A:Matrix (Fin n) (Fin n) ℝ)
    (halg:∀i j,IsAlgebraic ℚ (A i j)) (h:NonnegativeClass A) :
    (unitLanguage (fun _:Fin 1=>A) (fun _=>halg)).problem.InFP := by
  apply nonnegative_class_inFP _ (fun _=>rfl)
  exact h

theorem directSum_block_algorithms (L:RealLanguage 4 1 0)
    {n m:ℕ} (A:Matrix (Fin n) (Fin n) ℝ) (B:Matrix (Fin m) (Fin m) ℝ)
    (e:Fin 4≃Fin n⊕Fin m)
    (hm:∀i j,L.matrices 0 (e.symm i) (e.symm j)=sumMatrix A B i j)
    (hA:NonnegativeClass A) (hB:NonnegativeClass B) :
    ∃(ha:∀i j,IsAlgebraic ℚ (A i j))(hb:∀i j,IsAlgebraic ℚ (B i j)),
      (unitLanguage (fun _:Fin 1=>A) (fun _=>ha)).problem.InFP ∧
      (unitLanguage (fun _:Fin 1=>B) (fun _=>hb)).problem.InFP := by
  have ha:∀i j,IsAlgebraic ℚ (A i j) := by
    intro i j
    have h:=L.matrices_algebraic 0 (e.symm (.inl i)) (e.symm (.inl j))
    simpa only [hm,sumMatrix] using h
  have hb:∀i j,IsAlgebraic ℚ (B i j) := by
    intro i j
    have h:=L.matrices_algebraic 0 (e.symm (.inr i)) (e.symm (.inr j))
    simpa only [hm,sumMatrix] using h
  exact ⟨ha,hb,class_unitLanguage_inFP A ha hA,class_unitLanguage_inFP B hb hB⟩

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
