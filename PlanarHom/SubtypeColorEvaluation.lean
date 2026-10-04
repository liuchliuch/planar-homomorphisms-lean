import PlanarHom.PrescribedDomains
import PlanarHom.ActualTwinReduction

/-! Exact homogeneous evaluation on a fixed color subset. The background
indicator is intrinsic metadata, not a newly available arbitrary unary. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
local instance (priority := 10000) subtypeColorDecEq (α : Type*) : DecidableEq α := Classical.decEq α
open PrescribedDomains
variable {C R : Type} [Fintype C] [CommSemiring R] {bt : ℕ}

def allowedColorEquiv (n : ℕ) (S : Set C) :
    (Fin n→S) ≃ {σ : Fin n→C // Allowed (fun _:Fin 1=>S) (fun _:Fin n=>(0:Fin 1)) σ} where
  toFun τ := ⟨fun v=>(τ v).val,fun v=>(τ v).property⟩
  invFun σ v := ⟨σ.val v,σ.property v⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem evaluate_subset_colors (g : MixedCode) (hg : g.Valid bt 0)
    (M : Fin bt→Matrix C C R) (S : Set C) [Fintype S] :
    g.evaluate hg M (fun l:Fin 0=>l.elim0) (indicator S)=
      g.evaluate hg (fun (l : Fin bt) (i j : S)=>M l i.val j.val) (fun l:Fin 0=>l.elim0) (fun _=>1) := by
  have hu : g.unaries=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro u hu
    exact Nat.not_lt_zero _ (hg.2 u hu).2
  let f : (Fin g.vertices→C)→R := fun σ=>(g.edges.map (binaryValue g.vertices bt M σ)).prod
  have h := sum_restricted_eq_indicators (fun _:Fin 1=>S) (fun _ : Fin g.vertices=>(0:Fin 1)) f
  have he := (allowedColorEquiv g.vertices S).sum_comp (fun σ=>f σ.val)
  have hc : (∑ σ : Fin g.vertices→C,(∏ v,indicator S (σ v))*f σ)=
      ∑ τ : Fin g.vertices→S,(g.edges.map
        (binaryValue g.vertices bt (fun (l : Fin bt) (i j : S)=>M l i.val j.val) τ)).prod := by
    calc
      (∑ σ : Fin g.vertices→C,(∏ v,indicator S (σ v))*f σ)=
          ∑ σ : Fin g.vertices→C,f σ*(∏ v,indicator S (σ v)) := by
        apply Finset.sum_congr rfl
        intro σ _
        exact mul_comm _ _
      _ = ∑ σ : {σ : Fin g.vertices→C // Allowed (fun _:Fin 1=>S) (fun _:Fin g.vertices=>(0:Fin 1)) σ},f σ.val := h.symm
      _ = ∑ τ : Fin g.vertices→S,(g.edges.map
            (binaryValue g.vertices bt (fun (l : Fin bt) (i j : S)=>M l i.val j.val) τ)).prod := by
        rw [←he]
        rfl
  unfold evaluate
  simp only [hu,List.map_nil,List.prod_nil,mul_one,Finset.prod_const_one,one_mul]
  refine Eq.trans ?_ (Eq.trans hc ?_)
  all_goals
    apply Finset.sum_congr (by ext; simp)
    intro σ _
    rfl

end PlanarHom.Complexity.MixedCode
