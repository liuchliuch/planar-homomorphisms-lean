import PlanarHom.FixedRealBooleanEasy
import PlanarHom.SignedThreeStateCriterion

/-! NEW exact signed three-state easy implication. Every real chart is
realized by literal entries of the original source field; no displayed real
factor is assumed to belong to that field. -/
noncomputable section
namespace PlanarHom.FixedRealSmallState
open DensePolynomial FixedRealGraphEvaluation SignedThreeState
variable {n e : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K) (φ : K →+* ℝ)

 theorem three_easy (M : Matrix (Fin 3) (Fin 3) K) (hs : ∀i j, M i j = M j i)
    (h : ThreeStateEasy (fun i j => φ (M i j))) : Evaluable basis M (fun _ => 1) := by
  rcases h with hr | ⟨a,b,c,t,hbool,p,hm⟩ | ⟨a,b,p,hm⟩
  · exact real_rankOne basis φ M hs hr
  · let aK := M (p.symm 0) (p.symm 0)
    let bK := M (p.symm 0) (p.symm 1)
    let cK := M (p.symm 1) (p.symm 1)
    let tK := M (p.symm 2) (p.symm 2)
    have ha : φ aK = a := by simpa [aK,blockMatrix] using hm (p.symm 0) (p.symm 0)
    have hb : φ bK = b := by simpa [bK,blockMatrix] using hm (p.symm 0) (p.symm 1)
    have hc : φ cK = c := by simpa [cK,blockMatrix] using hm (p.symm 1) (p.symm 1)
    have ht : φ tK = t := by simpa [tK,blockMatrix] using hm (p.symm 2) (p.symm 2)
    have he : M = fun i j => blockMatrix aK bK cK tK (p i) (p j) := by
      funext i j
      apply φ.injective
      have hmij := hm i j
      dsimp only at hmij
      rw [hmij]
      generalize p i = x
      generalize p j = y
      fin_cases x <;> fin_cases y <;> simp [blockMatrix,ha,hb,hc,ht]
    have hbf : BooleanEasy (φ aK) (φ bK) (φ cK) := by simpa only [ha,hb,hc] using hbool
    rw [he]
    exact color basis p _ (fun _ => 1) (two_plus_one basis aK bK cK tK (boolean_easy basis φ aK bK cK hbf))
  · let aK := M (p.symm 0) (p.symm 2)
    let bK := M (p.symm 1) (p.symm 2)
    have ha : φ aK = a := by simpa [aK,starMatrix] using hm (p.symm 0) (p.symm 2)
    have hb : φ bK = b := by simpa [bK,starMatrix] using hm (p.symm 1) (p.symm 2)
    have he : M = fun i j => starMatrix aK bK (p i) (p j) := by
      funext i j
      apply φ.injective
      have hmij := hm i j
      dsimp only at hmij
      rw [hmij]
      generalize p i = x
      generalize p j = y
      fin_cases x <;> fin_cases y <;> simp [starMatrix,ha,hb]
    rw [he]
    exact color basis p _ (fun _ => 1) (signed_star basis aK bK)

end PlanarHom.FixedRealSmallState
