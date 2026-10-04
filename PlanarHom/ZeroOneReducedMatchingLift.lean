import PlanarHom.ActualTwinRemoval

/-! NEW exact lifting through the nonzero actual-row quotient. A matching
quotient implies that all neighbors in the original matrix have equal whole
numerical rows; duplicate colors and the deleted zero row remain explicit. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.ActualTwins
variable {C K : Type} [Fintype C] [Field K]
variable (A : Matrix C C K) (hs : ∀i j,A i j=A j i)

theorem entry_eq_reduced_of_rows (i j : C)
    (a b : Fin (reducedCount A hs))
    (hi : A i=A (representative A hs a)) (hj : A j=A (representative A hs b)) :
    A i j=reducedMatrix A hs a b := by
  rw [reducedMatrix_eq_representatives]
  calc
    A i j = A (representative A hs a) j := congrFun hi _
    _ = A j (representative A hs a) := hs _ _
    _ = A (representative A hs b) (representative A hs a) := congrFun hj _
    _ = A (representative A hs a) (representative A hs b) := hs _ _

theorem rows_of_reduced_matching
    (hm : ∀a b c,reducedMatrix A hs a b≠0 → reducedMatrix A hs a c≠0 → b=c)
    (i j k : C) (hij : A i j≠0) (hik : A i k≠0) : A j=A k := by
  have hi : A i≠0 := by intro h; exact hij (congrFun h j)
  have hj : A j≠0 := by intro h; exact hij ((hs i j).trans (congrFun h i))
  have hk : A k≠0 := by intro h; exact hik ((hs i k).trans (congrFun h i))
  obtain ⟨a,ha⟩ := exists_representative_of_row_ne_zero A hs i hi
  obtain ⟨b,hb⟩ := exists_representative_of_row_ne_zero A hs j hj
  obtain ⟨c,hc⟩ := exists_representative_of_row_ne_zero A hs k hk
  have hab : reducedMatrix A hs a b≠0 := by
    rw [←entry_eq_reduced_of_rows A hs i j a b ha hb]
    exact hij
  have hac : reducedMatrix A hs a c≠0 := by
    rw [←entry_eq_reduced_of_rows A hs i k a c ha hc]
    exact hik
  have he := hm a b c hab hac
  subst c
  exact hb.trans hc.symm

end PlanarHom.ActualTwins
