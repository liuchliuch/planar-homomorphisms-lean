import PlanarHom.PositiveDefiniteDichotomyAssembly
import PlanarHom.PositivePrincipalSubmatrix
import PlanarHom.MainSupportFiniteSource

/-! NEW actual source classification of every numerical support block of a
nonnegative PD matrix. Component restriction is a genuine original-source
reduction; all positive-definite and connectedness hypotheses are derived. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity RootedRestriction ClosedMatrixFamily LogarithmicSupport Boolean
variable {q : ℕ}

theorem positiveDefinite_support_block_tensor (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hpd : (L.matrices 0).PosDef) (hnn : ∀i j,0≤L.matrices 0 i j)
    (hnot : ¬PromisedSharpPHard L.problem)
    (c : (colorSupport (L.matrices 0) hs).ConnectedComponent) :
    ∃d : ℕ, ∃e : c.supp ≃ Cube d, ∃γ : ℝ, ∃ρ : Fin d → ℝ,
      0<γ ∧ (∀r,0<ρ r ∧ ρ r<1) ∧
      ∀i j : c.supp,L.matrices 0 i.val j.val=γ*tensor ρ (e i) (e j) := by
  let S := L.supportFiniteLanguage c.supp
  let e := (Fintype.equivFin c.supp).symm
  letI : Nonempty c.supp := c.nonempty_supp.to_subtype
  letI : Nonempty (Fin (Fintype.card c.supp)) := ⟨⟨0,Fintype.card_pos⟩⟩
  have hSunit : ∀i,S.weights i=1 := fun i=>hunit (e i).val
  have hSpos : (S.matrices 0).PosDef :=
    posDef_principal (L.matrices 0) hpd (fun i=>(e i).val) (Subtype.val_injective.comp e.injective)
  let iso : offDiagonalSupport (S.matrices 0) hSpos.1 ≃g c.toSimpleGraph := {
    toEquiv := e
    map_rel_iff' := by
      intro i j
      change ((e i).val≠(e j).val ∧ L.matrices 0 (e i).val (e j).val≠0) ↔
        (i≠j ∧ L.matrices 0 (e i).val (e j).val≠0)
      constructor
      · rintro ⟨hne,hm⟩
        exact ⟨fun hij=>hne (congrArg (fun i=>(e i).val) hij),hm⟩
      · rintro ⟨hne,hm⟩
        exact ⟨fun hij=>hne (e.injective (Subtype.ext hij)),hm⟩ }
  have hconn : (offDiagonalSupport (S.matrices 0) hSpos.1).Connected :=
    c.connected_toSimpleGraph.map iso.symm.toHom iso.symm.surjective
  have hw : ∀i,0<L.weights i := fun i=>by rw [hunit]; exact zero_lt_one
  have red := L.supportFiniteReduction hs hw c.supp (component_colorClosed _ hs c)
  obtain ⟨d,f,γ,ρ,hγ,hρ,he⟩ := S.positiveDefiniteTensorForm_of_not_hard hPotts hSunit hSpos
    (fun i j=>hnn _ _) hconn (fun hh=>hnot (hh.trans red))
  refine ⟨d,e.symm.trans f,γ,ρ,hγ,hρ,?_⟩
  intro i j
  have h := congrFun (congrFun he (f (e.symm i))) (f (e.symm j))
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.smul_apply,Pi.smul_apply,smul_eq_mul] at h
  simpa only [S,supportFiniteLanguage,e,Equiv.apply_symm_apply,Equiv.trans_apply] using h

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
