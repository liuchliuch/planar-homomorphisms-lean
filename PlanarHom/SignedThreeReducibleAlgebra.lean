import PlanarHom.SignedThreeSupportAlgebra

/-! In three dimensions a nonconstant Boolean zero cut has a singleton side.
The isolated color is permuted to the third position without altering entries. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
open ThreeStateDimension

theorem isolated_color_of_reducible (M : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ¬NoBooleanZeroCut M) : ∃p,∀j,j≠p→M p j=0 := by
  unfold NoBooleanZeroCut at h
  push_neg at h
  obtain ⟨f,hz,i,j,hij⟩ := h
  cases h0:f 0 <;> cases h1:f 1 <;> cases h2:f 2
  · fin_cases i <;> fin_cases j <;> simp_all
  · refine ⟨2,?_⟩
    intro j hj
    apply hz
    fin_cases j <;> simp_all
  · refine ⟨1,?_⟩
    intro j hj
    apply hz
    fin_cases j <;> simp_all
  · refine ⟨0,?_⟩
    intro j hj
    apply hz
    fin_cases j <;> simp_all
  · refine ⟨0,?_⟩
    intro j hj
    apply hz
    fin_cases j <;> simp_all
  · refine ⟨1,?_⟩
    intro j hj
    apply hz
    fin_cases j <;> simp_all
  · refine ⟨2,?_⟩
    intro j hj
    apply hz
    fin_cases j <;> simp_all
  · fin_cases i <;> fin_cases j <;> simp_all

/-- Literal 2+1 block with coefficients retained in the original field. -/
theorem block_of_isolated {K : Type} [CommRing K]
    (M : Matrix (Fin 3) (Fin 3) K) (hs : ∀i j,M i j=M j i)
    (p : Fin 3) (hp : ∀j,j≠p→M p j=0) :
    ∃a b c t:K,∃e:Equiv.Perm (Fin 3),∀i j,M i j=blockMatrix a b c t (e i) (e j) := by
  let e := Equiv.swap p (2:Fin 3)
  have he : e.symm 2=p := by simp [e]
  have hn0 : e.symm 0≠p := by
    intro h
    have hh:=congrArg e h
    simpa [e] using hh
  have hn1 : e.symm 1≠p := by
    intro h
    have hh:=congrArg e h
    simpa [e] using hh
  let N : Matrix (Fin 3) (Fin 3) K := fun i j=>M (e.symm i) (e.symm j)
  have hn02 : N 0 2=0 := by dsimp only [N]; rw [he,hs]; exact hp _ hn0
  have hn12 : N 1 2=0 := by dsimp only [N]; rw [he,hs]; exact hp _ hn1
  have hn20 : N 2 0=0 := by dsimp only [N]; rw [he]; exact hp _ hn0
  have hn21 : N 2 1=0 := by dsimp only [N]; rw [he]; exact hp _ hn1
  have hN : ∀i j,N i j=blockMatrix (N 0 0) (N 0 1) (N 1 1) (N 2 2) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [blockMatrix,hn02,hn12,hn20,hn21]
    exact hs _ _
  refine ⟨N 0 0,N 0 1,N 1 1,N 2 2,e,?_⟩
  intro i j
  simpa only [N,e.symm_apply_apply] using hN (e i) (e j)

end PlanarHom.SignedThreeState
