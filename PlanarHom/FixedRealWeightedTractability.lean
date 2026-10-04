import PlanarHom.FixedRealNonnegativeTractability
import PlanarHom.FixedRealQuotientTransport
import PlanarHom.WeightedStructureTransport

/-! NEW represented weighted structural algorithms. Source-entry charts and
actual original weights stay in their prescribed field, including unequal
bipartite sides, zero blocks, components and the actual row quotient. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealGraphEvaluation
open Complexity Complexity.MixedCode DensePolynomial FixedRealEvaluation Structures BooleanTensorEasyAssembly
variable {n e : ℕ} {K C : Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

theorem weightedScalar (γ : K) (A : Matrix C C K) (w : C → K) (h : Evaluable basis A w) :
    Evaluable basis (γ • A) w := by
  obtain ⟨P⟩ := h
  have hd := MixedCode.fp_edges.comp (ListUnaryLengthMachine.fp_length
    (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)))
  let Q : Program basis MixedCode.encoding (PlanarValid 1 0) (fun g => γ^g.edges.length) :=
    (power basis γ).pullback _ _ (fun g : MixedCode => g.edges.length) hd (fun _ _ => True.intro)
  refine ⟨(Q.mul P).congr _ ?_⟩
  intro g hp
  simp only [value,totalEvaluation_valid _ _ _ g hp.1,evaluate_homogeneous]
  unfold MultiGraph.partition MultiGraph.assignmentWeight
  simp only [Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

 theorem allowedWeightedBlock (φ : K →+* ℝ) (M : Matrix C C K) (w : C → K)
    (h : AllowedWeightedBlock (fun i j => φ (M i j)) (fun i => φ (w i))) :
    Evaluable basis M w := by
  letI : CharZero K := φ.charZero
  cases h with
  | zero a hz hw =>
    let f : C ≃ Fin 1 := a.trans (Equiv.ofUnique Unit (Fin 1))
    have hh := color basis f (fun _ _ : Fin 1 => (0 : K)*(0 : K)) (fun i => w (f.symm i))
      (rankOne basis (fun _ : Fin 1 => (0 : K)) (fun i => w (f.symm i)))
    have hm : M = 0 := by funext i j; apply φ.injective; simpa using hz i j
    simpa only [hm,zero_mul,Matrix.zero_apply,f.symm_apply_apply] using hh
  | positive k d hk a mass ρ ha hmass hρ f hm hw =>
    have hsource : Matrix.reindex f f (fun i j => φ (M i j)) =
        fun p r => a p.1*a r.1*Boolean.tensor ρ p.2 r.2 := by
      ext i j
      simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,f.apply_symm_apply] using hm (f.symm i) (f.symm j)
    obtain ⟨γ,α,p,hp⟩ := positive_ratios φ M ⟨0,hk⟩ f a ha ρ hsource
    let μ : Fin k → K := fun i => w (f.symm (i,fun _ => false))
    have hwK : ∀ i,w i=μ (f i).1 := by
      intro i
      apply φ.injective
      simp only [μ,hw,f.apply_symm_apply]
    let T := BooleanTensorSpectral.tensor (fun r => isingMatrix (p r))
    let B := MultiGraph.tensorInteraction (fun i j => α i*α j) T
    let W := MultiGraph.tensorVertexWeight μ (fun _ : Boolean.Cube d => (1 : K))
    have ht : Evaluable basis T (fun _ => 1) := tensor basis (fun r => isingMatrix (p r))
      (fun r => ising basis (Rat.castHom K) (p r))
    have hb : Evaluable basis B W := product basis (fun i j => α i*α j) T μ (fun _ => 1)
      (rankOne basis α μ) ht
    have hh := color basis f (γ • B) W (weightedScalar basis γ B W hb)
    have heq : M = fun i j => (γ • B) (f i) (f j) := funext (fun i => funext (hp i))
    have hwq : w = fun i => W (f i) := by
      funext i
      simpa only [W,MultiGraph.tensorVertexWeight,mul_one] using hwK i
    simpa only [←heq,←hwq] using hh
  | bipartite k l d hk hl a massX b massY ρ ha hb hmassX hmassY hρ f hm hw =>
    have hsource : Matrix.reindex f f (fun i j => φ (M i j)) =
        MultiGraph.tensorInteraction (BipartiteRankTwoTractability.matrix a b) (Boolean.tensor ρ) := by
      ext i j
      simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,f.apply_symm_apply] using hm (f.symm i) (f.symm j)
    obtain ⟨α,β,p,hp⟩ := bipartite_ratios φ M ⟨0,hk⟩ ⟨0,hl⟩ f a b ha hb ρ hsource
    let μ : Fin k → K := fun i => w (f.symm (Sum.inl i,fun _ => false))
    let ν : Fin l → K := fun i => w (f.symm (Sum.inr i,fun _ => false))
    have hwK : ∀ i,w i=Sum.elim μ ν (f i).1 := by
      intro i
      apply φ.injective
      cases hi : (f i).1 with
      | inl j => simp only [hi,Sum.elim_inl,μ,hw,f.apply_symm_apply]
      | inr j => simp only [hi,Sum.elim_inr,ν,hw,f.apply_symm_apply]
    let T := BooleanTensorSpectral.tensor (fun r => isingMatrix (p r))
    let B := MultiGraph.tensorInteraction (BipartiteRankTwoTractability.matrix α β) T
    let W := MultiGraph.tensorVertexWeight (Sum.elim μ ν) (fun _ : Boolean.Cube d => (1 : K))
    have ht : Evaluable basis T (fun _ => 1) := tensor basis (fun r => isingMatrix (p r))
      (fun r => ising basis (Rat.castHom K) (p r))
    have hB : Evaluable basis B W := product basis (BipartiteRankTwoTractability.matrix α β) T
      (Sum.elim μ ν) (fun _ => 1) (bipartite basis α μ β ν) ht
    have hh := color basis f B W hB
    have heq : M = fun i j => B (f i) (f j) := funext (fun i => funext (hp i))
    have hwq : w = fun i => W (f i) := by
      funext i
      simpa only [W,MultiGraph.tensorVertexWeight,mul_one] using hwK i
    simpa only [←heq,←hwq] using hh

 theorem weightedClass (φ : K →+* ℝ) (M : Matrix C C K) (w : C → K)
    (h : WeightedClass (fun i j => φ (M i j)) (fun i => φ (w i))) :
    Evaluable basis M w := by
  have hs := h.unweighted.symmetric
  obtain ⟨t,block,honto,hzero,hforms⟩ := h
  letI : DecidableEq (Fin t) := Classical.decEq _
  apply fibers basis block M (fun i j => φ.injective (hs i j))
    (fun i j h => φ.injective (by simpa using hzero i j h)) w
  intro r
  exact allowedWeightedBlock basis φ _ _ (hforms r)

 theorem positiveVertexWeightClass_inFP (φ : K →+* ℝ) (M : Matrix C C K) (w : C → K)
    (hs : ∀ i j,M i j=M j i)
    (h : PositiveVertexWeightClass (fun i j => φ (M i j)) (fun i => φ (w i))
      (fun i j => congrArg φ (hs i j))) :
    (FixedRealComponents.problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w).InFP := by
  let a := FixedRealActualTwins.rowEquiv φ M
  have hm : (fun i j => φ (Twins.quotientMatrix M hs i j)) =
      (fun i j => Twins.quotientMatrix (fun i j => φ (M i j)) (fun i j => congrArg φ (hs i j)) (a i) (a j)) :=
    funext (fun i => funext (FixedRealActualTwins.quotientMatrix_map φ M hs i))
  have hw : (fun i => φ (Twins.quotientWeight M w i)) =
      (fun i => Twins.quotientWeight (fun i j => φ (M i j)) (fun i => φ (w i)) (a i)) :=
    funext (FixedRealActualTwins.quotientWeight_map φ M w)
  have hc : WeightedClass (fun i j => φ (Twins.quotientMatrix M hs i j))
      (fun i => φ (Twins.quotientWeight M w i)) := by
    rw [hm,hw]
    exact h.equiv a
  have hfp := inFP basis _ _ (weightedClass basis φ _ _ hc)
  exact (FixedRealActualTwins.originalReduction basis M hs w).inFP hfp

end PlanarHom.FixedRealGraphEvaluation
