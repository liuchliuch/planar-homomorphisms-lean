import PlanarHom.MixedParallelSemantics

/-! A total typed value used only to state oracle answers; invalid label/range
codes receive zero and remain outside every evaluation promise. -/
namespace PlanarHom.Complexity.MixedCode
noncomputable section
open Classical
variable {C K : Type} [Fintype C] [CommSemiring K] {binaryTypes unaryTypes : ℕ}

def totalEvaluation (M : Fin binaryTypes→Matrix C C K) (U : Fin unaryTypes→C→K) (w : C→K)
    (g : MixedCode) : K:=if hg:g.Valid binaryTypes unaryTypes then g.evaluate hg M U w else 0

@[simp] theorem totalEvaluation_valid (M : Fin binaryTypes→Matrix C C K) (U : Fin unaryTypes→C→K)
    (w : C→K) (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes) :
    totalEvaluation M U w g=g.evaluate hg M U w:=by simp only [totalEvaluation,dif_pos hg]

end
end PlanarHom.Complexity.MixedCode
