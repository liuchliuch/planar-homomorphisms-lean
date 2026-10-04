import PlanarHom.OrdinaryToPrescribedBipartite

/-! NEW literal domain doubling. The computed bipartition fixes the first
coordinate, giving a weight-preserving bijection with the original colors. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.ComputedDomainDoubling
open Complexity Complexity.MixedCode PrescribedDomains FixedRealRootRestrictions
open ComputedBipartiteSideQueries BipartiteRankTwoTractability
variable {C K : Type} [Fintype C] [Field K]

def matrix (M : Matrix C C K) : Matrix (Bool×C) (Bool×C) K :=
  fun i j=>if i.1=j.1 then 0 else M i.2 j.2

def weights (w : C→K) : Bool×C→K := fun i=>w i.2

theorem crosses (M : Matrix C C K) : ∀i j,matrix M i j≠0 → i.1≠j.1 := by
  intro i j hn he
  exact hn (if_pos he)

def assignmentEquiv (n : ℕ) (δ : Fin n→Bool) :
    (Fin n→C)≃{σ : Fin n→Bool×C // ∀v,(σ v).1=δ v} where
  toFun τ:=⟨fun v=>(δ v,τ v),fun _=>rfl⟩
  invFun σ:=fun v=>(σ.val v).2
  left_inv _:=rfl
  right_inv σ:=by
    apply Subtype.ext
    funext v
    exact Prod.ext (σ.property v).symm rfl

theorem oriented_assignment (g : MixedCode) (hg : g.Valid 1 0)
    (δ : Fin g.vertices→Bool)
    (hδ : ∀e,δ ((g.toMultiGraph hg).src e)≠δ ((g.toMultiGraph hg).dst e))
    (M : Matrix C C K) (w : C→K) (τ : Fin g.vertices→C) :
    (g.toMultiGraph hg).assignmentWeight (matrix M) (weights w) (fun v=>(δ v,τ v))=
      (g.toMultiGraph hg).assignmentWeight M w τ := by
  unfold MultiGraph.assignmentWeight
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  exact if_neg (hδ e)

theorem oriented_value (g : MixedCode) (hg : g.Valid 1 0)
    (δ : Fin g.vertices→Fin 2)
    (hδ : ∀e,decide (δ ((g.toMultiGraph hg).src e)=1)≠
      decide (δ ((g.toMultiGraph hg).dst e)=1))
    (M : Matrix C C K) (w : C→K) :
    evaluateRestricted g hg (fun _ : Fin 1=>matrix M) (fun u : Fin 0=>u.elim0)
      (weights w) (Bipartite.domains Prod.fst) δ=
      g.evaluate hg (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w := by
  let P : (Fin g.vertices→Bool×C)→Prop := fun σ=>∀v,(σ v).1=decide (δ v=1)
  let f := (g.toMultiGraph hg).assignmentWeight (matrix M) (weights w)
  letI (σ : Fin g.vertices→Bool×C) : Decidable (P σ) := Classical.propDecidable _
  have hs : (∑σ,if P σ then f σ else 0)=∑σ : {σ // P σ},f σ.val := by
    rw [←Fintype.sum_subtype_add_sum_subtype P (fun σ=>if P σ then f σ else 0)]
    have hy : (∑σ : {σ // P σ},if P σ.val then f σ.val else 0)=∑σ : {σ // P σ},f σ.val := by
      apply Finset.sum_congr rfl
      intro σ _
      exact if_pos σ.property
    have hn : (∑σ : {σ // ¬P σ},if P σ.val then f σ.val else 0)=0 := by
      apply Finset.sum_eq_zero
      intro σ _
      exact if_neg σ.property
    rw [hy,hn,add_zero]
  unfold evaluateRestricted
  simp only [HomogeneousSourceOrientation.homogeneous_assignmentWeight g hg]
  change (∑σ,if P σ then f σ else 0)=_
  rw [hs]
  unfold evaluate
  simp only [HomogeneousSourceOrientation.homogeneous_assignmentWeight g hg]
  symm
  apply Fintype.sum_equiv (assignmentEquiv g.vertices (fun v=>decide (δ v=1)))
  intro τ
  exact (oriented_assignment g hg _ hδ M w τ).symm

theorem tag_proper_edges (g : MixedCode) (hg : g.Valid 1 0)
    (hok : (coloring g).1=true) (flip : Bool) :
    ∀e,decide (tag g flip ((g.toMultiGraph hg).src e)=1)≠
      decide (tag g flip ((g.toMultiGraph hg).dst e)=1) := by
  intro e
  rw [tag_bit,tag_bit]
  have h:=coloring_sound g hok (g.edges.get e) (List.get_mem _ _)
  change bit g flip (g.edges.get e).1≠bit g flip (g.edges.get e).2.1
  cases h1 : PlanarityParitySolver.lookup (coloring g).2 (g.edges.get e).1 <;>
    cases h2 : PlanarityParitySolver.lookup (coloring g).2 (g.edges.get e).2.1 <;>
    cases flip <;> simp_all [bit]

theorem query_value (g : MixedCode) (hg : g.Valid 1 0) (hok : (coloring g).1=true)
    (flip : Bool) (M : Matrix C C K) (w : C→K) :
    totalEvaluation (fun _ : Fin 1=>matrix M)
      (extendedUnaries (fun u : Fin 0=>u.elim0) (Bipartite.domains Prod.fst))
      (weights w) (query flip g)=g.evaluate hg (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w := by
  rw [query_eq_withDomains g hg flip,totalEvaluation_valid _ _ _ _ (withDomains_valid g hg _),
    evaluate_withDomains]
  exact oriented_value g hg _ (tag_proper_edges g hg hok flip) M w

theorem connected_value (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (hn : 0<g.vertices)
    (hok : (coloring g).1=true) (M : Matrix C C K) (w : C→K) :
    g.evaluate hg (fun _ : Fin 1=>matrix M) (fun u : Fin 0=>u.elim0) (weights w)=
      2*g.evaluate hg (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w := by
  rw [←queries_value_sum g hg hc hn (matrix M) (weights w) Prod.fst (crosses M)]
  simp only [queries,hok,ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  rw [query_value g hg hok false M w,query_value g hg hok true M w]
  ring

end PlanarHom.ComputedDomainDoubling
