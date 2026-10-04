import PlanarHom.ThreeStatePositiveRank
import PlanarHom.PositiveUnitDiagonalRigidity

/-! NEW pure rigidity bridge: actual unit diagonal and distinct rows collapse
the amplitude fiber in the full nonnegative structural class. The surviving
Boolean tensor has no parameter equal to one. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveClassUnitTensor
open Structures Boolean
variable {C : Type} [Nonempty C]

theorem tensor_of_class (M : Matrix C C ℝ) (hp : ∀ i j, 0 < M i j)
    (hd : ∀ i, M i i = 1) (hinj : Function.Injective M) (hc : NonnegativeClass M) :
    ∃ d : ℕ, ∃ e : C ≃ Cube d, ∃ ρ : Fin d → ℝ,
      (∀ r, 0 < ρ r ∧ ρ r ≠ 1) ∧ ∀ i j, M i j = tensor ρ (e i) (e j) := by
  have ha := ThreeStateDimension.positive_class_allowed hp hc
  cases ha with
  | zero e hz =>
    have h := hp (e.symm ()) (e.symm ())
    rw [hz] at h
    exact False.elim (lt_irrefl _ h)
  | bipartite k l d hk hl a b ρ ha hb hρ e hm =>
    let i := e.symm (Sum.inl ⟨0,hk⟩, fun _ => false)
    have h := hp i i
    rw [hm] at h
    simp only [i,e.apply_symm_apply,bipartiteAmplitude,zero_mul] at h
    exact False.elim (lt_irrefl _ h)
  | positive k d hk a ρ ha hρ e hm =>
    have ha1 : ∀ i, a i = 1 := by
      intro i
      have h := hd (e.symm (i,fun _ => false))
      rw [hm] at h
      simp only [e.apply_symm_apply,tensor_diag,mul_one] at h
      nlinarith [ha i]
    have hform : ∀ i j, M i j = tensor ρ (e i).2 (e j).2 := by
      intro i j
      simpa only [ha1,one_mul] using hm i j
    let f : C → Cube d := fun i => (e i).2
    have hf : Function.Bijective f := by
      constructor
      · intro i j hij
        apply hinj
        funext r
        rw [hform,hform]
        exact congrArg (fun x => tensor ρ x (e r).2) hij
      · intro x
        exact ⟨e.symm (⟨0,hk⟩,x),by simp only [f,e.apply_symm_apply]⟩
    let a := Equiv.ofBijective f hf
    have hti : Function.Injective (tensor ρ) := by
      intro x y hxy
      apply a.symm.injective
      apply hinj
      funext r
      rw [hform,hform]
      change tensor ρ (a (a.symm x)) (a r) = tensor ρ (a (a.symm y)) (a r)
      simp only [a.apply_symm_apply]
      exact congrFun hxy (a r)
    exact ⟨d,a,ρ,fun r => ⟨hρ r,PositiveUnitDiagonalRigidity.tensor_parameters_nonunit ρ hti r⟩,
      hform⟩

end PlanarHom.PositiveClassUnitTensor
