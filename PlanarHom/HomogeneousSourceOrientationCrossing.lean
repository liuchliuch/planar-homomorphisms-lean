import PlanarHom.HomogeneousSourceOrientationConnected

/-! Numerical crossing suffices for orientation propagation even when an
occurrence is traversed against its stored direction. No symmetry hypothesis
on the source matrix is needed for the homogeneous source-orientation bridge. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.HomogeneousSourceOrientation
open Complexity Complexity.MixedCode PrescribedDomains TypedBipartiteContext
open FixedRealRootRestrictions RootedRestriction
variable {C K : Type} [Fintype C] [Field K]

theorem assignment_adj_sides_ne (g : MixedCode) (hg : g.Valid 1 0)
    (M : Matrix C C K) (w : C → K) (side : C → Bool)
    (hcross : ∀ i j, M i j ≠ 0 → side i ≠ side j)
    (σ : Fin g.vertices → C) (h : (g.toMultiGraph hg).assignmentWeight M w σ ≠ 0)
    (u v : Fin g.vertices) (huv : (GraphComponentCode.support g).Adj u v) :
    side (σ u) ≠ side (σ v) := by
  obtain ⟨_,e,he,hends|hends⟩ := huv
  all_goals
    obtain ⟨k,hk⟩ := List.get_of_mem he
    have hn := RootedRestriction.assignment_edge_ne_zero g hg M w σ h k
    have hsrc : (g.toMultiGraph hg).src k = ⟨e.1,(hg.1 e he).1⟩ := by
      apply Fin.ext; simpa only [toMultiGraph] using congrArg Prod.fst hk
    have hdst : (g.toMultiGraph hg).dst k = ⟨e.2.1,(hg.1 e he).2.1⟩ := by
      apply Fin.ext; simpa only [toMultiGraph] using congrArg (fun a : ℕ × (ℕ × ℕ) => a.2.1) hk
    rw [hsrc,hdst] at hn
    have hside := hcross _ _ hn
  · have hu : (⟨e.1,(hg.1 e he).1⟩ : Fin g.vertices)=u := Fin.ext hends.1
    have hv : (⟨e.2.1,(hg.1 e he).2.1⟩ : Fin g.vertices)=v := Fin.ext hends.2
    simpa only [hu,hv] using hside
  · have hv : (⟨e.1,(hg.1 e he).1⟩ : Fin g.vertices)=v := Fin.ext hends.1
    have hu : (⟨e.2.1,(hg.1 e he).2.1⟩ : Fin g.vertices)=u := Fin.ext hends.2
    simpa only [hu,hv] using hside.symm

theorem sides_eq_of_root_of_nonzero_of_crosses (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (w : C → K)
    (side : C → Bool) (hcross : ∀ i j, M i j ≠ 0 → side i ≠ side j)
    (δ : Fin g.vertices → Bool)
    (hproper : ∀ u v, (GraphComponentCode.support g).Adj u v → δ u ≠ δ v)
    (σ : Fin g.vertices → C) (hr : side (σ r) = δ r)
    (h : (g.toMultiGraph hg).assignmentWeight M w σ ≠ 0) :
    ∀ v, side (σ v) = δ v := by
  intro v
  have hv := (SimpleGraph.reachable_iff_reflTransGen r v).mp (hc.preconnected r v)
  induction hv with
  | refl => exact hr
  | @tail u v _ huv ih =>
    exact bool_agreement_across_edge
      (assignment_adj_sides_ne g hg M w side hcross σ h u v huv) (hproper u v huv) ih

theorem rootRestricted_eq_side_sum_of_crosses (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (w : C → K)
    (side : C → Bool) (hcross : ∀ i j, M i j ≠ 0 → side i ≠ side j)
    (δ : Fin g.vertices → Bool)
    (hproper : ∀ u v, (GraphComponentCode.support g).Adj u v → δ u ≠ δ v) :
    (g.toMultiGraph hg).rootRestricted r M w {c | side c = δ r} =
      ∑ σ : Fin g.vertices → C, if (∀ v, side (σ v) = δ v) then
        (g.toMultiGraph hg).assignmentWeight M w σ else 0 := by
  unfold MultiGraph.rootRestricted
  apply Finset.sum_congr
  · ext σ; simp
  intro σ _
  by_cases hz : (g.toMultiGraph hg).assignmentWeight M w σ = 0
  · simp [hz]
  · have he : side (σ r) = δ r ↔ ∀ v, side (σ v) = δ v :=
      ⟨fun hr => sides_eq_of_root_of_nonzero_of_crosses g hg hc r M w side hcross δ hproper σ hr hz,
        fun ha => ha r⟩
    simp only [Set.mem_setOf_eq, he]

theorem evaluate_withDomains_eq_rootRestricted_of_crosses (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (w : C → K)
    (side : C → Bool) (hcross : ∀ i j, M i j ≠ 0 → side i ≠ side j)
    (δ : Fin g.vertices → Fin 2)
    (hproper : ∀ u v, (GraphComponentCode.support g).Adj u v →
      decide (δ u = 1) ≠ decide (δ v = 1)) :
    (withDomains (unaryTypes := 0) g δ).evaluate (withDomains_valid g hg δ)
      (fun _ : Fin 1 => M)
      (extendedUnaries (fun u : Fin 0 => u.elim0) (Bipartite.domains side)) w =
      (g.toMultiGraph hg).rootRestricted r M w (Bipartite.domains side (δ r)) := by
  rw [evaluate_withDomains g hg]
  change _ = (g.toMultiGraph hg).rootRestricted r M w {c | side c = decide (δ r = 1)}
  rw [rootRestricted_eq_side_sum_of_crosses g hg hc r M w side hcross _ hproper]
  unfold evaluateRestricted
  apply Finset.sum_congr
  · ext σ; simp
  intro σ _
  simp only [Allowed, Bipartite.domains, Set.mem_setOf_eq, homogeneous_assignmentWeight g hg M w σ]

variable [Algebra ℚ K] [LinearOrder K] [IsStrictOrderedRing K] {dimension : ℕ}

def connectedReductionOfCrosses (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K)
    (hw : ∀ i, 0 < w i) (side : C → Bool)
    (hcross : ∀ i j, M i j ≠ 0 → side i ≠ side j) :
    PromisePolyTimeTuringReduction (connectedTypedProblem basis M w side)
      (evaluationProblem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w) := by
  let data₀ := exists_computed_root_queries M w hw (Bipartite.domains side 0)
  let k₀ := Classical.choose data₀
  let graphs₀ := Classical.choose (Classical.choose_spec data₀)
  let c₀ := Classical.choose (Classical.choose_spec (Classical.choose_spec data₀))
  have h₀ := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec data₀))
  let data₁ := exists_computed_root_queries M w hw (Bipartite.domains side 1)
  let k₁ := Classical.choose data₁
  let graphs₁ := Classical.choose (Classical.choose_spec data₁)
  let c₁ := Classical.choose (Classical.choose_spec (Classical.choose_spec data₁))
  have h₁ := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec data₁))
  apply reductionOfPipeline basis BitEncoding.bool
    (fun _ : Fin 1 => M) (extendedUnaries (fun l : Fin 0 => l.elim0) (Bipartite.domains side)) w
    (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w
    connectedTypedGraph (MixedCode.PlanarValid 1 0)
    (fun _ h => h.1.planarValid.1) (fun _ h => h.1)
    (prepareSides graphs₀ graphs₁) (recoverSides c₀ c₁)
    (fp_prepareSides graphs₀ graphs₁) (fp_recoverSides basis c₀ c₁)
  · intro code hc query hquery
    obtain ⟨he, hconn, hn⟩ := hc
    obtain ⟨g, hg, δ, ht, hp, hd⟩ := he
    rw [MixedCode.encoding.decode_encode] at hd
    have heq := Option.some.inj hd
    subst code
    have hn' : 0 < g.vertices := hn
    simp only [prepareSides, eraseDomains_withDomains g hg δ] at hquery
    split at hquery
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hquery
      exact RootedCodeMachines.attach_planarValid _ (graphs₁ j).2.2.property 0 _ ⟨hg,hp⟩ ⟨0,hn'⟩ (by decide)
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hquery
      exact RootedCodeMachines.attach_planarValid _ (graphs₀ j).2.2.property 0 _ ⟨hg,hp⟩ ⟨0,hn'⟩ (by decide)
  · intro code hc
    obtain ⟨he, hconn, hn⟩ := hc
    obtain ⟨g, hg, δ, ht, hp, hd⟩ := he
    rw [MixedCode.encoding.decode_encode] at hd
    have heq := Option.some.inj hd
    subst code
    have hn' : 0 < g.vertices := hn
    have hconn' : (GraphComponentCode.support g).Connected := hconn
    rw [evaluate_withDomains_eq_rootRestricted_of_crosses g hg hconn' ⟨0,hn'⟩ M w side hcross δ
      (typed_proper g hg δ ht)]
    have htag := rootSide_withDomains g hg δ hn'
    simp only [prepareSides, eraseDomains_withDomains g hg δ, recoverSides, htag]
    by_cases hd₁ : δ ⟨0,hn'⟩ = 1
    · simp only [hd₁, decide_true, Bool.true_eq, ↓reduceIte, RootedRestriction.prepare,
        List.map_ofFn, RootedRestriction.recover_ofFn]
      simpa only [MultiGraph.atRoot_restricted] using (h₁ g ⟨hg,hp⟩ ⟨0,hn'⟩).symm
    · have hd₀ : δ ⟨0,hn'⟩ = 0 := by
        apply Fin.ext
        have hh := (δ ⟨0,hn'⟩).isLt
        have hne : (δ ⟨0,hn'⟩).val ≠ 1 := by intro h; exact hd₁ (Fin.ext h)
        change (δ ⟨0,hn'⟩).val = 0
        omega
      simp only [hd₀, show (0 : Fin 2) ≠ 1 by decide, decide_false, Bool.false_eq_true, ↓reduceIte,
        RootedRestriction.prepare, List.map_ofFn, RootedRestriction.recover_ofFn]
      simpa only [MultiGraph.atRoot_restricted] using (h₀ g ⟨hg,hp⟩ ⟨0,hn'⟩).symm


end PlanarHom.HomogeneousSourceOrientation
