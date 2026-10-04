import PlanarHom.FinitePermutationBoundaryArcSplice
import PlanarHom.FinitePermutationBoundaryPathWord

/-! NEW two-input arbitrary-gap boundary gluing. All hypotheses concern
literal original face arcs, before any vertex is identified. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {A B : Type} [Fintype A] [Fintype B]

structure BoundaryArc (P : Equiv.Perm A) (x : ℕ→A) (t : ℕ) (a b : A) where
  length : ℕ
  positive : 0 < length
  endpoint : P^[length] a=b
  interior : ∀ i, 0 < i → i < length → ∀ j < t, P^[i] a≠x j

 def BoundaryArc.left {P : Equiv.Perm A} {x : ℕ→A} {t : ℕ} {a b : A}
    (arc : BoundaryArc P x t a b) (Q : Equiv.Perm B) (y : ℕ→B) :
    MarkedBoundaryArc (Equiv.sumCongr P Q) (Sum.inl ∘ x) (Sum.inr ∘ y) t (.inl a) (.inl b) where
  length:=arc.length
  positive:=arc.positive
  endpoint:=by rw [boundary_sum_iterate_left,arc.endpoint]
  interior:=by
    intro i hi hi' j hj
    rw [boundary_sum_iterate_left]
    exact ⟨fun h=>arc.interior i hi hi' j hj (Sum.inl.inj h),Sum.inl_ne_inr⟩

 def BoundaryArc.right {Q : Equiv.Perm B} {y : ℕ→B} {t : ℕ} {a b : B}
    (arc : BoundaryArc Q y t a b) (P : Equiv.Perm A) (x : ℕ→A) :
    MarkedBoundaryArc (Equiv.sumCongr P Q) (Sum.inl ∘ x) (Sum.inr ∘ y) t (.inr a) (.inr b) where
  length:=arc.length
  positive:=arc.positive
  endpoint:=by rw [boundary_sum_iterate_right,arc.endpoint]
  interior:=by
    intro i hi hi' j hj
    rw [boundary_sum_iterate_right]
    exact ⟨Sum.inr_ne_inl,fun h=>arc.interior i hi hi' j hj (Sum.inr.inj h)⟩

 theorem boundaryPathSplice_count_arcs (P : Equiv.Perm A) (Q : Equiv.Perm B) (x : ℕ→A) (y : ℕ→B) (n : ℕ)
    (hxi : ∀i<n+1,∀j<n+1,x i=x j→i=j) (hyi : ∀i<n+1,∀j<n+1,y i=y j→i=j)
    (left : ∀i,i<n→BoundaryArc P x (n+1) (x i) (x (i+1)))
    (right : ∀i,i<n→BoundaryArc Q y (n+1) (y (i+1)) (y i)) :
    count (boundaryPathSplice P Q x y (n+1))+1=count P+count Q+n := by
  have hh:=count_splicePrefix_arcs (Equiv.sumCongr P Q) (Sum.inl ∘ x) (Sum.inr ∘ y) n
    (sum_path_markers x y (n+1) hxi hyi) (not_sameCycle_sum_cross P Q (x 0) (y 0))
    (fun i hi=>(left i hi).left Q y) (fun i hi=>(right i hi).right P x)
  simpa only [count_sumCongr] using hh

 theorem boundaryPathSplice_euler_arcs (P : Equiv.Perm A) (Q : Equiv.Perm B) (x : ℕ→A) (y : ℕ→B) (n : ℕ)
    (hxi : ∀i<n+1,∀j<n+1,x i=x j→i=j) (hyi : ∀i<n+1,∀j<n+1,y i=y j→i=j)
    (left : ∀i,i<n→BoundaryArc P x (n+1) (x i) (x (i+1)))
    (right : ∀i,i<n→BoundaryArc Q y (n+1) (y (i+1)) (y i))
    (v₁ e₁ v₂ e₂ v e : ℕ) (h₁ : v₁+count P=e₁+2) (h₂ : v₂+count Q=e₂+2)
    (hv : v+(n+1)=v₁+v₂) (he : e=e₁+e₂) :
    v+count (boundaryPathSplice P Q x y (n+1))=e+2 := by
  have hh:=boundaryPathSplice_count_arcs P Q x y n hxi hyi left right
  omega

end PlanarHom.FinitePermutationCycles
