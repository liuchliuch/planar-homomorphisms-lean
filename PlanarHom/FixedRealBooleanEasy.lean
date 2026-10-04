import PlanarHom.FixedRealSmallStateClosure
import PlanarHom.SignedThreeEasyClosure

/-! NEW all four signed Boolean easy alternatives in the represented source
field, including the true signed Hadamard branch and every zero/singular limit. -/
noncomputable section
namespace PlanarHom.FixedRealSmallState
open DensePolynomial FixedRealGraphEvaluation SignedThreeState
variable {n e : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

 theorem equal_diagonal (a b : K) : Evaluable basis (booleanBool a b a) (fun _ => 1) := by
  by_cases ha : a = 0
  · subst a
    have h := bipartite basis (fun _ : Fin 1 => b) (fun _ => 1) (fun _ : Fin 1 => 1) (fun _ => 1)
    have hw : Sum.elim (fun _ : Fin 1 => (1 : K)) (fun _ : Fin 1 => 1) = fun _ => 1 := by
      funext i; cases i <;> rfl
    rw [hw] at h
    have he : booleanBool 0 b 0 = fun i j => BipartiteRankTwoTractability.matrix
        (fun _ : Fin 1 => b) (fun _ : Fin 1 => 1) (boolSumOne i) (boolSumOne j) := by
      funext i j; cases i <;> cases j <;> simp [booleanBool,boolSumOne,BipartiteRankTwoTractability.matrix]
    rw [he]
    exact color basis boolSumOne _ (fun _ => 1) h
  · have he : booleanBool a b a = a • BooleanTensorEasyAssembly.isingMatrix (b / a) := by
      funext i j
      cases i <;> cases j <;> simp [booleanBool,BooleanTensorEasyAssembly.isingMatrix,Pi.smul_apply,smul_eq_mul]
      all_goals field_simp [ha]
    rw [he]
    exact scalar basis a _ (ising basis
      ((algebraMap (RationalFunction n) K).comp (DenseRationalConstantExtraction.constantMap n)) _)

 theorem exceptional_boolean (φ : K →+* ℝ) (a b c : K)
    (h : φ a * φ c = -(φ b ^ 2) ∧ φ a = -φ c) :
    Evaluable basis (booleanBool a b c) (fun _ => 1) := by
  obtain ⟨hc,hb⟩ := (boolean_exceptional_iff (φ a) (φ b) (φ c)).mp h
  have hcK : c = -a := φ.injective (by simpa only [map_neg] using hc)
  rw [hcK]
  rcases hb with hb | hb
  · have hbK : b = a := φ.injective hb
    rw [hbK]
    have hm : booleanBool a a (-a) = a • SignedHadamard.interaction := by
      funext i j
      cases i <;> cases j <;> simp [booleanBool,SignedHadamard.interaction,BooleanQuadratic.hadamard]
    rw [hm]
    exact scalar basis a _ (hadamard basis)
  · have hbK : b = -a := φ.injective (by simpa only [map_neg] using hb)
    rw [hbK]
    have hm : booleanBool a (-a) (-a) = fun i j =>
        ((-a) • (SignedHadamard.interaction : Matrix Bool Bool K)) (boolFlip i) (boolFlip j) := by
      funext i j
      cases i <;> cases j <;> simp [booleanBool,SignedHadamard.interaction,BooleanQuadratic.hadamard,boolFlip]
    rw [hm]
    exact color basis boolFlip _ (fun _ => 1) (scalar basis (-a) _ (hadamard basis))

 theorem boolean_easy (φ : K →+* ℝ) (a b c : K) (h : BooleanEasy (φ a) (φ b) (φ c)) :
    Evaluable basis (booleanBool a b c) (fun _ => 1) := by
  rcases h with h | h | h | h
  · exact rankOne_boolean basis a b c (φ.injective (by simpa only [map_mul,map_pow] using h))
  · have hb : b = 0 := (map_eq_zero φ).mp h
    rw [hb]
    exact diagonal_boolean basis a c
  · have hc : c = a := φ.injective h.symm
    rw [hc]
    exact equal_diagonal basis a b
  · exact exceptional_boolean basis φ a b c h

end PlanarHom.FixedRealSmallState
