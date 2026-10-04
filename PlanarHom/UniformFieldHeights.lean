import PlanarHom.MaterializedCoefficientHeights

/-! Basis-independent materialized heights for bounded dimension and explicit structure-data bits. -/
noncomputable section
namespace PlanarHom.UniformFieldHeights
open Complexity FieldCoordinateCertificates IntegerCoordinateBounds EncodingSizeBounds MachineComposition

/-- Coordinate framing is monotone in the allowed dimension. -/
theorem coordinatePolynomial_dimension_mono {d c C D n : ℕ} (hd : d ≤ c) :
    (coordinateOutputPolynomial d C D).eval n ≤ (coordinateOutputPolynomial c C D).eval n := by
  have hs := Nat.size_le_size hd
  simp only [coordinateOutputPolynomial, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul]
  nlinarith

/-- An exponentially bounded base contributes only its explicit exponent to
rational normalization input length; the normalization machine is universal. -/
theorem rationalPolynomial_base_bound {B S L : ℕ} (hB : B ≤ 2 ^ S) (hS : 1 ≤ S) :
    (rationalOutputPolynomial B B).eval L ≤ (rationalOutputPolynomial 2 2).eval (S * L) := by
  have hb : Nat.size B ≤ S + 1 := (Nat.size_le_size hB).trans_eq Nat.size_pow
  have hb' : Nat.size B ≤ 2 * S := by omega
  simp only [rationalOutputPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  apply natPolynomial_monotone
  have hs2 : Nat.size 2 = 2 := by simpa using (Nat.size_pow (n := 1))
  rw [hs2]
  nlinarith

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}

/-- All basis dependence is paid by the structure-height budget H and degree cap c. -/
theorem heightBase_le_pow (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2 ^ H) :
    MaterializedFieldHeights.heightBase data ≤ 2 ^ (H + c + 2) := by
  apply max_le
  · exact (show 2 ^ 1 ≤ 2 ^ (H+c+2) from Nat.pow_le_pow_right (by omega) (by omega))
  · apply max_le
    · exact hdata.trans (Nat.pow_le_pow_right (by omega) (by omega))
    · exact Nat.pow_le_pow_right (by omega) (by omega)

/-- A single explicit polynomial depends only on the dimension cap, never on
K, its basis, its structure matrices, or the materialized field inputs. -/
def valuePolynomial (c : ℕ) : Polynomial ℕ :=
  (coordinateOutputPolynomial c 2 2).comp
    ((Polynomial.X + Polynomial.C (c+2)) * (Polynomial.X + Polynomial.C 2)^2)

theorem coordinatePolynomial_uniform (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2 ^ H) (N : ℕ) :
    (coordinateOutputPolynomial dimension (MaterializedFieldHeights.heightBase data)
      (MaterializedFieldHeights.heightBase data)).eval ((N+2)^2) ≤ (valuePolynomial c).eval (N+H) := by
  have hr := rationalPolynomial_base_bound (heightBase_le_pow data hd hdata)
    (by omega : 1 ≤ H+c+2) (L := (N+2)^2)
  have hs := Nat.size_le_size hd
  have hcoord : (coordinateOutputPolynomial dimension (MaterializedFieldHeights.heightBase data)
      (MaterializedFieldHeights.heightBase data)).eval ((N+2)^2) ≤
      (coordinateOutputPolynomial c 2 2).eval ((H+c+2)*((N+2)^2)) := by
    simp only [coordinateOutputPolynomial, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul]
    nlinarith
  apply hcoord.trans
  simp only [valuePolynomial, Polynomial.eval_comp]
  apply natPolynomial_monotone
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow]
  exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)

/-- Uniform products and sums of a list whose members and length are charged to N. -/
theorem list_values_encoding_bound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2 ^ H)
    (xs : List K) (N : ℕ) (hlen : xs.length ≤ N+1)
    (hcode : ∀ x ∈ xs, ((numberFieldEncoding basis).encode x).length ≤ N) :
    ((numberFieldEncoding basis).encode xs.prod).length ≤ (valuePolynomial c).eval (N+H) ∧
    ((numberFieldEncoding basis).encode xs.sum).length ≤ (valuePolynomial c).eval (N+H) := by
  have hb := MaterializedFieldHeights.list_values_encoding_bound data xs N hlen hcode
  have hp := coordinatePolynomial_uniform data hd hdata N
  exact ⟨hb.1.trans hp, hb.2.trans hp⟩

/-- Every coefficient of arbitrary materialized linear factors has the same
uniform bound, with the exponential expansion remaining proof-only. -/
theorem coefficient_encoding_bound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H n : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2 ^ H)
    (nodes : Fin n → K) (N : ℕ) (hn : n ≤ N)
    (hcode : ∀ i, ((numberFieldEncoding basis).encode (nodes i)).length ≤ N) (k : ℕ) :
    ((numberFieldEncoding basis).encode
      ((∏ i, (Polynomial.X - Polynomial.C (nodes i))).coeff k)).length ≤ (valuePolynomial c).eval (N+H) :=
  (MaterializedCoefficientHeights.coefficient_encoding_bound data nodes N hn hcode k).trans
    (coordinatePolynomial_uniform data hd hdata N)

/-- Complete coefficient-list serialization, including all framing and zeroes. -/
def coefficientListPolynomial (c : ℕ) : Polynomial ℕ :=
  (Polynomial.C 2 * valuePolynomial c + Polynomial.C 3) * (Polynomial.X + 1) + 1

theorem coefficient_list_encoding_bound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2 ^ H)
    (nodes : List K) (N : ℕ) (hn : nodes.length ≤ N)
    (hcode : ∀ x ∈ nodes, ((numberFieldEncoding basis).encode x).length ≤ N) :
    ((numberFieldEncoding basis).list.encode (LagrangeCoefficientMachines.productCoefficients nodes)).length ≤
      (coefficientListPolynomial c).eval (N+H) := by
  have hpoly : (nodes.map (fun μ => Polynomial.X - Polynomial.C μ)).prod =
      ∏ i : Fin nodes.length, (Polynomial.X - Polynomial.C (nodes.get i)) := by
    conv_lhs => rw [← List.ofFn_get nodes]
    simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  have hb : ∀ x ∈ LagrangeCoefficientMachines.productCoefficients nodes,
      ((numberFieldEncoding basis).encode x).length ≤ (valuePolynomial c).eval (N+H) := by
    intro x hx
    rw [LagrangeCoefficientMachines.productCoefficients_ofFn, hpoly] at hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact coefficient_encoding_bound data hd hdata (fun i => nodes.get i) N hn
      (fun i => hcode _ (List.get_mem nodes i)) i.val
  have hl := CoefficientListHeights.list_encoding_length_le (numberFieldEncoding basis) _ _ hb
  rw [LagrangeCoefficientMachines.productCoefficients_length] at hl
  apply hl.trans
  simp only [coefficientListPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _

end PlanarHom.UniformFieldHeights
