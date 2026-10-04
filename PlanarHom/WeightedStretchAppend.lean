import PlanarHom.WeightedStretchSemantics
import PlanarHom.SelectedStretchAppend

/-! Appended weighted-chain labels use exactly the old source alphabet. -/
noncomputable section
open Classical
namespace PlanarHom.Complexity.MixedCode
variable {C R : Type} [Fintype C] [DecidableEq C] [CommSemiring R]

def weightedChain (M : Matrix C C R) (w : C → R) (h : ℕ) : Matrix C C R :=
  M * (Matrix.diagonal w * M)^(h-1)

theorem substituteLabels_appendOne {b : ℕ} (M : Fin b → Matrix C C R) (N : Matrix C C R) :
    substituteLabels (a := b+1) M b N = FiniteLanguageAliases.appendOne M N := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [substituteLabels,FiniteLanguageAliases.appendOne_aux]
  · change substituteLabels M b N (Fin.castAdd 1 j) =
      FiniteLanguageAliases.appendOne M N (Fin.castAdd 1 j)
    simp [substituteLabels,j.isLt.ne,j.isLt,FiniteLanguageAliases.appendOne_old]

/-- All positive-length source chains have exactly the weighted K(DK)^(h−1)
signature. The total zero-length fallback is one segment, as in the code. -/
theorem evaluate_stretchLabelLength_weighted {b u : ℕ} (g : MixedCode)
    (hg : g.Valid (b+1) u) (replacement : Fin b) (h : ℕ)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R) (w : C → R) :
    (g.stretchLabelLength b replacement.val h).evaluate
      (g.stretchLabelLength_valid hg b h replacement (g.appended_companion_bound hg)) M U w =
    g.evaluate hg (FiniteLanguageAliases.appendOne M (weightedChain (M replacement) w h)) U w := by
  simpa only [stretchLabelLength,weightedChain,substituteLabels_appendOne] using
    g.evaluate_stretchLabel_weighted hg b (h-1) replacement (g.appended_companion_bound hg) M U w

end PlanarHom.Complexity.MixedCode
