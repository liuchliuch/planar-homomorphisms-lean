import PlanarHom.HomogeneousSourceOrientationMachines
import PlanarHom.TypedRealLanguagePresentation

/-! A genuine original-oracle reduction for connected homogeneous typed source
inputs. This is a specialization of source orientation, not an assumption of
source availability. The full raw mixed-code promise includes alternate
successful encodings. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.HomogeneousSourceOrientation
open Complexity Complexity.MixedCode PrescribedDomains TypedBipartiteContext
open FixedRealRootRestrictions RootedRestriction

private theorem finTwo_side_injective : Function.Injective (fun d : Fin 2 => decide (d = 1)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | cases h

theorem typed_proper (g : MixedCode) (hg : g.Valid 1 0)
    (δ : Fin g.vertices → Fin 2) (ht : Typed sidePolicies emptyPolicies g hg δ) :
    ∀ u v, (GraphComponentCode.support g).Adj u v →
      decide (δ u = 1) ≠ decide (δ v = 1) := by
  intro u v huv he
  have hd : δ u = δ v := finTwo_side_injective he
  obtain ⟨_, e, he, hends | hends⟩ := huv
  all_goals
    have ht' := ht.1 e he
    change δ ⟨e.1,(hg.1 e he).1⟩ ≠ δ ⟨e.2.1,(hg.1 e he).2.1⟩ at ht'
  · have hu : (⟨e.1,(hg.1 e he).1⟩ : Fin g.vertices) = u := Fin.ext hends.1
    have hv : (⟨e.2.1,(hg.1 e he).2.1⟩ : Fin g.vertices) = v := Fin.ext hends.2
    exact ht' (by simpa only [hu,hv] using hd)
  · have hv : (⟨e.1,(hg.1 e he).1⟩ : Fin g.vertices) = v := Fin.ext hends.1
    have hu : (⟨e.2.1,(hg.1 e he).2.1⟩ : Fin g.vertices) = u := Fin.ext hends.2
    exact ht' (by simpa only [hu,hv] using hd.symm)

def connectedTypedGraph (g : MixedCode) : Prop :=
  EncodedGraph sidePolicies emptyPolicies g ∧
    (GraphComponentCode.support g).Connected ∧ 0 < g.vertices

variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable [LinearOrder K] [IsStrictOrderedRing K] {dimension : ℕ}

def connectedTypedProblem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K) (side : C → Bool) : PromiseProblem :=
  restrictedEvaluationProblem basis (fun _ : Fin 1 => M)
    (extendedUnaries (fun l : Fin 0 => l.elim0) (Bipartite.domains side)) w connectedTypedGraph

/-- Connected typed homogeneous evaluation uses original homogeneous planar
queries only. The root's side is read by the literal FP metadata program. -/
def connectedReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i) (w : C → K)
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
    rw [evaluate_withDomains_eq_rootRestricted g hg hconn' ⟨0,hn'⟩ M hs w side hcross δ
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
