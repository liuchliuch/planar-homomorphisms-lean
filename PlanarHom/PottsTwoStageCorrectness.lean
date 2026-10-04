import PlanarHom.PottsTwoStageMachines
import PlanarHom.PottsRandomClusterPolynomial

/-! Exact correctness of the concrete two-stage program on literal normalized
random-cluster samples. Connecting radial graph coefficients to these samples
is the separate combinatorial theorem, not a premise of any hardness claim. -/
noncomputable section
open Classical
namespace PlanarHom.PottsTwoStageInterpolation
open MultiGraph

def colorNode (δ : ℚ) (k : ℕ) : ℚ := (δ^(k+1))^2
def edgeNode (δ : ℚ) (k l : ℕ) : ℚ := (1+δ^(k+1))^(l+1)-1

theorem colorNode_pos {δ : ℚ} (hδ : 1<δ) (k : ℕ) : 0<colorNode δ k := by
  exact pow_pos (pow_pos (lt_trans zero_lt_one hδ) _) _

theorem colorNode_injective {δ : ℚ} (hδ : 1<δ) : Function.Injective (colorNode δ) := by
  intro k l h
  unfold colorNode at h
  rw [← pow_mul,← pow_mul] at h
  have he := (pow_right_injective₀ (lt_trans zero_lt_one hδ) (ne_of_gt hδ)) h
  omega

theorem edgeNode_injective {δ : ℚ} (hδ : 1<δ) (k : ℕ) : Function.Injective (edgeNode δ k) := by
  have hb : 1<1+δ^(k+1) := by linarith [pow_pos (lt_trans zero_lt_one hδ) (k+1)]
  intro l r h
  have he := (pow_right_injective₀ (lt_trans zero_lt_one hb) (ne_of_gt hb))
    (sub_left_inj.mp h)
  omega
end PlanarHom.PottsTwoStageInterpolation

namespace PlanarHom.PottsTwoStageMachines
open MultiGraph PottsTwoStageInterpolation
variable {V E : Type} [Fintype V] [Fintype E]

theorem edgeTable_samples (G : MultiGraph V E) (δ : ℚ) (answers : List ℚ)
    (hs : ∀ k<Fintype.card V,∀ l<Fintype.card E+1,
      (δ^(k+1))^Fintype.card V*answers.getD (k*(Fintype.card E+1)+l) 0=
        G.randomCluster (colorNode δ k) (edgeNode δ k l))
    (k : ℕ) (hk : k<Fintype.card V) :
    edgeTable δ (Fintype.card V,(Fintype.card E,answers)) k=
      (List.range (Fintype.card E+1)).map (fun l =>
        (edgeNode δ k l,(G.randomClusterEdgePolynomial (colorNode δ k)).eval (edgeNode δ k l))) := by
  apply List.map_congr_left
  intro l hl
  have hll : l<Fintype.card E+1 := List.mem_range.mp hl
  simp only [edgeSample,rowPower,min_eq_right (show k+1≤Fintype.card V by omega),
    min_eq_right (show l+1≤Fintype.card E+1 by omega)]
  rw [hs k hk l hll]
  simp only [eval_randomClusterEdgePolynomial]
  rfl

theorem rowValue_samples (G : MultiGraph V E) (δ v₀ : ℚ) (hδ : 1<δ) (answers : List ℚ)
    (hs : ∀ k<Fintype.card V,∀ l<Fintype.card E+1,
      (δ^(k+1))^Fintype.card V*answers.getD (k*(Fintype.card E+1)+l) 0=
        G.randomCluster (colorNode δ k) (edgeNode δ k l))
    (k : ℕ) (hk : k<Fintype.card V) :
    rowValue δ v₀ (Fintype.card V,(Fintype.card E,answers)) k=
      G.randomCluster (colorNode δ k) v₀ := by
  rw [rowValue,edgeTable_samples G δ answers hs k hk]
  have hd : (G.randomClusterEdgePolynomial (colorNode δ k)).degree<↑(Fintype.card E+1) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast Nat.lt_succ_of_le (G.randomClusterEdgePolynomial_degree (colorNode δ k))
  rw [MaterializedPolynomialInterpolationMachines.recover_eq_eval v₀ _
    (by simpa only [List.map_map,Function.comp_def] using List.nodup_range.map (edgeNode_injective hδ k))
    (G.randomClusterEdgePolynomial (colorNode δ k)) (by simpa using hd) (by
      intro row hr
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp hr
      rfl)]
  exact eval_randomClusterEdgePolynomial G _ _

/-- Full two-stage recovery from the exact row-major normalized samples. The
zero-color sample is justified by actual nonempty vertex connectivity. -/
theorem recover_randomCluster_samples [Nonempty V] (G : MultiGraph V E) (δ Q₀ v₀ : ℚ)
    (hδ : 1<δ) (answers : List ℚ)
    (hs : ∀ k<Fintype.card V,∀ l<Fintype.card E+1,
      (δ^(k+1))^Fintype.card V*answers.getD (k*(Fintype.card E+1)+l) 0=
        G.randomCluster (colorNode δ k) (edgeNode δ k l)) :
    recover δ Q₀ v₀ (Fintype.card V,(Fintype.card E,answers))=G.randomCluster Q₀ v₀ := by
  let nodes := (0:ℚ)::(List.range (Fintype.card V)).map (colorNode δ)
  have hn : nodes.Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨k,_,hk⟩ := List.mem_map.mp hm
      exact (colorNode_pos hδ k).ne' hk
    · exact List.nodup_range.map (colorNode_injective hδ)
  have ht : colorTable δ v₀ (Fintype.card V,(Fintype.card E,answers))=
      nodes.map (fun x => (x,(G.randomClusterColorPolynomial v₀).eval x)) := by
    apply congrArg₂ List.cons
    · simp [eval_randomClusterColorPolynomial,G.randomCluster_zero_color]
    · rw [List.map_map]
      apply List.map_congr_left
      intro k hk
      have hkk := List.mem_range.mp hk
      simp only [Function.comp_apply,colorRow,rowPower,
        min_eq_right (show k+1≤Fintype.card V by omega)]
      rw [rowValue_samples G δ v₀ hδ answers hs k hkk]
      simp only [eval_randomClusterColorPolynomial,colorNode]
  rw [recover,ht,MaterializedPolynomialInterpolationMachines.recover_samples Q₀ nodes hn
    (G.randomClusterColorPolynomial v₀)]
  · exact eval_randomClusterColorPolynomial G _ _
  · apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    have hd := Nat.lt_succ_of_le (G.randomClusterColorPolynomial_degree v₀)
    simp only [nodes,List.length_cons,List.length_map,List.length_range]
    exact_mod_cast hd

theorem recover_threeState_samples [Nonempty V] (G : MultiGraph V E) (δ : ℚ)
    (hδ : 1<δ) (answers : List ℚ)
    (hs : ∀ k<Fintype.card V,∀ l<Fintype.card E+1,
      (δ^(k+1))^Fintype.card V*answers.getD (k*(Fintype.card E+1)+l) 0=
        G.randomCluster (colorNode δ k) (edgeNode δ k l)) :
    recover δ 3 1 (Fintype.card V,(Fintype.card E,answers))=
      G.unweighted (ProperColoringPottsReduction.positivePottsMatrix 3) := by
  rw [recover_randomCluster_samples G δ 3 1 hδ answers hs]
  exact G.randomCluster_potts 3
end PlanarHom.PottsTwoStageMachines
