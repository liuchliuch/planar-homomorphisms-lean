import PlanarHom.RootedRealAvailability
import PlanarHom.SupportComponentReduction

/-! Source3.5's real-algebraic support-component endpoints preserve the original
field presentation and the literal real numerical support components. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.MultiGraph
variable {V E C K L : Type} [Fintype V] [Fintype E] [Fintype C]
variable [CommSemiring K] [CommSemiring L]

theorem map_partition (φ : K →+* L) (G : MultiGraph V E)
    (M : Matrix C C K) (w : C → K) :
    φ (G.partition M w) = G.partition (fun i j => φ (M i j)) (fun i => φ (w i)) := by
  simp [partition,assignmentWeight,map_sum,map_mul,map_prod]

end PlanarHom.MultiGraph
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode
variable {q : ℕ} (L : RealLanguage q 1 0)

def supportRestrictionProblem (X : Set (Fin q)) : PromiseProblem :=
  evaluationProblem L.basis (fun _ : Fin 1 => fun i j : X => L.matricesK 0 i.val j.val)
    (fun u : Fin 0 => Fin.elim0 u) (fun i : X => L.weightsK i.val)

/-- Original-field output representation of the literal color-submatrix sum. -/
theorem supportRestriction_value_coe (X : Set (Fin q)) (g : MixedCode) (hg : g.Valid 1 0) :
    L.field.val (g.evaluate hg (fun _ : Fin 1 => fun i j : X => L.matricesK 0 i.val j.val)
      (fun u : Fin 0 => Fin.elim0 u) (fun i : X => L.weightsK i.val)) =
    g.evaluate hg (fun _ : Fin 1 => fun i j : X => L.matrices 0 i.val j.val)
      (fun u : Fin 0 => Fin.elim0 u) (fun i : X => L.weights i.val) :=
by
  have h := map_evaluate L.field.val.toRingHom g hg
    (fun _ : Fin 1 => fun i j : X => L.matricesK 0 i.val j.val)
    (fun u : Fin 0 => Fin.elim0 u) (fun i : X => L.weightsK i.val)
  have hU : (fun (l : Fin 0) (i : X) =>
      L.field.val.toRingHom ((Fin.elim0 l : X → L.field) i)) =
      (fun l : Fin 0 => (Fin.elim0 l : X → ℝ)) := by
    funext l
    exact l.elim0
  rw [hU] at h
  exact h

/-- Actual arbitrary-input restriction to any fixed union of numerical support
components; this retains the original weighted source oracle and exact basis. -/
def lemma35_submatrix (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hw : ∀ i,0<L.weights i) (X : Set (Fin q))
    (hX : RootedRestriction.ColorClosed (L.matrices 0) X) :
    PromisePolyTimeTuringReduction (L.supportRestrictionProblem X) L.problem := by
  letI : IsStrictOrderedRing L.field := Subfield.toIsStrictOrderedRing L.field.toSubfield
  have hsK : ∀ i j,L.matricesK 0 i j=L.matricesK 0 j i := by
    intro i j
    apply Subtype.ext
    exact hs i j
  have hwK : ∀ i,0<L.weightsK i := hw
  have hXK : RootedRestriction.ColorClosed (L.matricesK 0) X := by
    intro i hi j hn
    apply hX i hi j
    intro hz
    apply hn
    apply Subtype.ext
    exact hz
  have h := RootedRestriction.submatrixReduction L.basis (L.matricesK 0) hsK L.weightsK hwK X hXK
  have hM : (fun _ : Fin 1 => L.matricesK 0) = L.matricesK := by
    funext l
    congr 1
    exact (Fin.eq_zero l).symm
  have hU : (fun u : Fin 0 => Fin.elim0 u) = L.unariesK := by funext u; exact u.elim0
  rw [hM,hU] at h
  exact h

/-- The source paper's component extraction, for a component of the actual real
numerical support, including a zero-row isolated color component. -/
def lemma35_component (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hw : ∀ i,0<L.weights i) (c : (RootedRestriction.colorSupport (L.matrices 0) hs).ConnectedComponent) :
    PromisePolyTimeTuringReduction (L.supportRestrictionProblem c.supp) L.problem :=
  L.lemma35_submatrix hs hw c.supp (RootedRestriction.component_colorClosed _ hs c)

/-- The displayed source identity with fixed coefficients in Q(A,w), interpreted
in the real sums. The original algebraic language alone determines that field. -/
theorem exists_real_root_formula (hw : ∀ i,0<L.weights i) (X : Set (Fin q)) :
    ∃ n : ℕ, ∃ graphs : Fin n → FiniteRootedPlanar, ∃ c : Fin n → L.field,
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : MultiGraph V E) (r : V), G.Planar →
        G.rootRestricted r (L.matrices 0) L.weights X =
          ∑ j, (c j : ℝ) * (G.attachRooted (graphs j).2.2.val r).partition (L.matrices 0) L.weights := by
  letI : IsStrictOrderedRing L.field := Subfield.toIsStrictOrderedRing L.field.toSubfield
  have hwK : ∀ i,0<L.weightsK i := hw
  obtain ⟨n,graphs,c,h⟩ := RootedRestriction.exists_attachment_coefficients (L.matricesK 0) L.weightsK hwK X
  refine ⟨n,graphs,c,?_⟩
  intro V E _ _ G r hG
  have hc := h V E G r hG
  rw [MultiGraph.atRoot_restricted] at hc
  have hr := congrArg L.field.val.toRingHom hc
  simpa only [map_sum,map_mul,MultiGraph.map_rootRestricted,MultiGraph.map_partition,
    matricesK_coe,weightsK_coe] using hr

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
