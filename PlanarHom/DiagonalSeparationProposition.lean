import PlanarHom.DiagonalSeparationComplexity
import PlanarHom.GadgetSupportRankCondition

/-! NEW complete main-text Proposition 2.5 assembly. The actual gadget
condition and every literal support-component rank alternative are retained.
Only the separately owned all-q Potts foundation is still explicit. -/
noncomputable section
namespace PlanarHom.GadgetDiagonalSeparation
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage Complexity
variable {q:ℕ}

 theorem proposition25_of_potts (hPotts:PositivePottsFoundation) (L:RealLanguage q 1 0)
    (hunit:∀i,L.weights i=1) (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn:∀i j,0≤L.matrices 0 i j) :
    ((∀i j,0<L.matrices 0 i j)→Function.Injective (fun i=>L.matrices 0 i i)→
      ((L.matrices 0).rank=1→L.problem.InFP) ∧
        (1<(L.matrices 0).rank→PromisedSharpPHard L.problem)) ∧
    (Separates (L.matrices 0)→
      (SupportRankCondition (L.matrices 0) hs→L.problem.InFP) ∧
        (¬SupportRankCondition (L.matrices 0) hs→PromisedSharpPHard L.problem)) :=
  ⟨fun hp hd=>proposition25i_of_potts hPotts L hunit hs hp hd,
    fun hsep=>proposition25ii_of_potts hPotts L hunit hs hnn hsep⟩

end PlanarHom.GadgetDiagonalSeparation
