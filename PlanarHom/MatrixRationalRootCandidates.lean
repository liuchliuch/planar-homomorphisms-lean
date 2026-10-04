import PlanarHom.MatrixRationalRootBounds
import PlanarHom.PolynomialIntegerRootCandidates

/-! # Constant-size candidates for every rational characteristic root -/

noncomputable section
namespace PlanarHom.MatrixRationalRootCandidates
open MatrixRationalRootBounds
variable {I : Type} [Fintype I] [DecidableEq I]

def candidates (A : Matrix I I ℚ) : List ℚ :=
  (PolynomialIntegerRootCandidates.candidates (Fintype.card I) (shifted A).charpoly
    0 (2*bound A+1)).map (fun t : ℕ => ((t:ℚ)-(bound A:ℚ))/(denominator A:ℚ))

theorem root_mem_candidates (A : Matrix I I ℚ) (r : ℚ)
    (hr : A.charpoly.eval r = 0) : r ∈ candidates A := by
  obtain ⟨v, hv, he⟩ := eigenvector_of_charpoly_root A r hr
  have hs := scaled_eigen A r v he
  obtain ⟨z, hz⟩ := rational_eigenvalue_integer (integerMatrix A) _ v hv hs
  have hb := eigenvalue_abs_le_mass _ _ v hv hs
  have hB := mass_integerMatrix A
  have habs : |(z:ℚ)| < (bound A:ℚ) := by rw [← hz]; linarith
  obtain ⟨hzlo, hzhi⟩ := abs_lt.mp habs
  have hznonneg : 0 ≤ z+(bound A:ℤ) := by
    have h : (0:ℚ) < (z:ℚ)+(bound A:ℚ) := by linarith
    have h' : (0:ℤ) < z+(bound A:ℤ) := by exact_mod_cast h
    omega
  let t := (z+(bound A:ℤ)).toNat
  have ht : (t:ℤ) = z+(bound A:ℤ) := Int.toNat_of_nonneg hznonneg
  have htq : (t:ℚ) = (denominator A:ℚ)*r+(bound A:ℚ) := by
    rw [hz]
    exact_mod_cast ht
  have htupper : t < 2*bound A+1 := by
    have hzhi' : z < (bound A:ℤ) := by exact_mod_cast hzhi
    have hti : (t:ℤ) < ((2*bound A+1:ℕ):ℤ) := by push_cast; omega
    exact_mod_cast hti
  have hroot : (shifted A).charpoly.eval (t:ℚ) = 0 := by
    apply PowerRootLiftMatrix.charpoly_eval_zero_of_eigen _ _ v hv
    rw [htq]
    exact shifted_eigen A r v he
  have hmem := PolynomialIntegerRootCandidates.root_mem_candidates (Fintype.card I)
    (shifted A).charpoly (by simp) (Matrix.charpoly_monic _).ne_zero
    0 (2*bound A+1) t (Nat.zero_le _) htupper hroot
  apply List.mem_map.mpr
  refine ⟨t, hmem, ?_⟩
  rw [htq]
  have hD : (denominator A:ℚ) ≠ 0 := by exact_mod_cast (denominator_pos A).ne'
  field_simp
  ring

theorem candidates_length (A : Matrix I I ℚ) :
    (candidates A).length ≤ 3^(Fintype.card I)*Fintype.card I := by
  simpa only [candidates, List.length_map] using
    PolynomialIntegerRootCandidates.candidates_length (Fintype.card I) (shifted A).charpoly
      0 (2*bound A+1)

end PlanarHom.MatrixRationalRootCandidates
