import PlanarHom.RootedRealComponentAvailability
import PlanarHom.SupportBlockTractability

/-! Source3.5's final FP implication for the actual real-algebraic source
support components, in the original source field and raw-word model. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode
variable {q : ℕ} (L : RealLanguage q 1 0)

private theorem liftedSymmetry (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :
    ∀ i j,L.matricesK 0 i j=L.matricesK 0 j i := by
  intro i j
  apply Subtype.ext
  exact hs i j

/-- The exact field lift changes no numerical zero or source support edge. -/
theorem colorSupport_lift (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i) :
    RootedRestriction.colorSupport (L.matricesK 0) (liftedSymmetry L hs) =
      RootedRestriction.colorSupport (L.matrices 0) hs := by
  ext i j
  change (i≠j ∧ L.matricesK 0 i j≠0) ↔ (i≠j ∧ L.matrices 0 i j≠0)
  constructor
  · rintro ⟨hij,hn⟩
    refine ⟨hij,?_⟩
    intro hz
    apply hn
    apply Subtype.ext
    exact hz
  · rintro ⟨hij,hn⟩
    refine ⟨hij,?_⟩
    intro hz
    exact hn (congrArg Subtype.val hz)

private theorem component_supp_cast {V : Type} {G H : SimpleGraph V}
    (h : G=H) (c : G.ConnectedComponent) : (h ▸ c).supp=c.supp := by
  subst H
  rfl

/-- All actual real support blocks in raw promised FP imply the full original
problem is in raw promised FP. No full-source evaluator or cost oracle is assumed. -/
theorem lemma35_inFP (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (h : ∀ c : (RootedRestriction.colorSupport (L.matrices 0) hs).ConnectedComponent,
      (L.supportRestrictionProblem c.supp).InFP) : L.problem.InFP := by
  have hb : ∀ c : (RootedRestriction.colorSupport (L.matricesK 0) (liftedSymmetry L hs)).ConnectedComponent,
      (evaluationProblem L.basis (fun _ : Fin 1 => fun i j : c.supp => L.matricesK 0 i.val j.val)
        (fun u : Fin 0 => Fin.elim0 u) (fun i : c.supp => L.weightsK i.val)).InFP := by
    intro c
    have hc := h (L.colorSupport_lift hs ▸ c)
    have he := component_supp_cast (L.colorSupport_lift hs) c
    change (L.supportRestrictionProblem c.supp).InFP
    rw [he] at hc
    exact hc
  have hfull := RootedRestriction.supportBlocks_inFP L.basis (L.matricesK 0) (liftedSymmetry L hs) L.weightsK hb
  have hM : (fun _ : Fin 1 => L.matricesK 0) = L.matricesK := by
    funext l
    congr 1
    exact (Fin.eq_zero l).symm
  have hU : (fun u : Fin 0 => Fin.elim0 u) = L.unariesK := by funext u; exact u.elim0
  rw [hM,hU] at hfull
  exact hfull

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
