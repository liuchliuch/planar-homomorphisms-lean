import PlanarHom.UniformFieldArithmeticHeights
import PlanarHom.MaterializedLagrangeRecoveryMachines

/-! A single basis-independent polynomial bounds the total materialized recovery formula. -/
noncomputable section
namespace PlanarHom.UniformFieldHeights
open Complexity FieldCoordinateCertificates IntegerCoordinateBounds MachineComposition
open LagrangeCoefficientMachines MaterializedLagrangeRecoveryMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}

def denominatorPolynomial (c : ℕ) : Polynomial ℕ :=
  (valuePolynomial c).comp (Polynomial.X + operationPolynomial c)

def scalePolynomial (c : ℕ) : Polynomial ℕ :=
  (operationPolynomial c).comp (Polynomial.X + denominatorPolynomial c)

def coefficientProductPolynomial (c : ℕ) : Polynomial ℕ :=
  (operationPolynomial c).comp (Polynomial.X + coefficientListPolynomial c)

def dotPolynomial (c : ℕ) : Polynomial ℕ :=
  (valuePolynomial c).comp (Polynomial.X + coefficientProductPolynomial c)

def rowPolynomial (c : ℕ) : Polynomial ℕ :=
  (operationPolynomial c).comp (Polynomial.X + scalePolynomial c + dotPolynomial c)

def recoveryPolynomial (c : ℕ) : Polynomial ℕ :=
  (valuePolynomial c).comp (Polynomial.X + rowPolynomial c)

private theorem forall_zipWith {A B D : Type} (f : A → B → D) (P : D → Prop)
    (xs : List A) (ys : List B) (h : ∀ a ∈ xs, ∀ b ∈ ys, P (f a b)) :
    ∀ z ∈ List.zipWith f xs ys, P z := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    cases ys with
    | nil => simp
    | cons b ys =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h a (by simp) b (by simp)
      · exact ih ys (fun a ha b hb => h a (by simp [ha]) b (by simp [hb])) z hz

/-- Uniform bounds for the shifted denominator computed from arbitrary literal nodes. -/
theorem denominator_encoding_bound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2^H)
    (μ : K) (nodes : List K) (N : ℕ) (hlen : nodes.length ≤ N)
    (hμ : ((numberFieldEncoding basis).encode μ).length ≤ N)
    (hcode : ∀ x ∈ nodes, ((numberFieldEncoding basis).encode x).length ≤ N) :
    ((numberFieldEncoding basis).encode (MaterializedFieldListMachines.shiftedDenominator (μ,nodes))).length ≤
      (denominatorPolynomial c).eval (N+H) := by
  let O := (operationPolynomial c).eval (N+H)
  have hl : (μ :: nodes.map (fun x => μ-x)).length ≤ N+O+1 := by simp; omega
  have hwords : ∀ x ∈ μ :: nodes.map (fun x => μ-x),
      ((numberFieldEncoding basis).encode x).length ≤ N+O := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hμ.trans (by omega)
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
      exact ((operations_encoding_bound data hd hdata μ z N hμ (hcode z hz)).2.1).trans (by omega)
  have hb := (list_values_encoding_bound data hd hdata _ (N+O) hl hwords).1
  simpa only [O, MaterializedFieldListMachines.shiftedDenominator, List.prod_cons, denominatorPolynomial,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hb

/-- Coefficient/answer products and their dynamic sum have a common uniform bound. -/
theorem dot_encoding_bound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2^H)
    (nodes answers : List K) (N : ℕ) (hlen : nodes.length ≤ N)
    (hcode : ∀ x ∈ nodes, ((numberFieldEncoding basis).encode x).length ≤ N)
    (hanswers : ∀ y ∈ answers, ((numberFieldEncoding basis).encode y).length ≤ N) :
    ((numberFieldEncoding basis).encode
      ((List.zipWith (fun x y => x*y) (productCoefficients nodes) answers).sum)).length ≤
        (dotPolynomial c).eval (N+H) := by
  let C := (coefficientListPolynomial c).eval (N+H)
  let P := (coefficientProductPolynomial c).eval (N+H)
  have hc := coefficient_list_encoding_bound data hd hdata nodes N hlen hcode
  have hp : ∀ x ∈ productCoefficients nodes, ∀ y ∈ answers,
      ((numberFieldEncoding basis).encode (x*y)).length ≤ P := by
    intro x hx y hy
    have hx' := (MaterializedFieldHeights.element_length_le_list (numberFieldEncoding basis) _ hx).trans hc
    have h := (operations_encoding_bound data hd hdata x y (N+C)
      (hx'.trans (by omega)) ((hanswers y hy).trans (by omega))).2.2.1
    simpa only [P, coefficientProductPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, C, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hl : (List.zipWith (fun x y => x*y) (productCoefficients nodes) answers).length ≤ N+P+1 := by
    rw [List.length_zipWith, productCoefficients_length]
    exact (Nat.min_le_left _ _).trans (by omega)
  have hw : ∀ z ∈ List.zipWith (fun x y => x*y) (productCoefficients nodes) answers,
      ((numberFieldEncoding basis).encode z).length ≤ N+P :=
    forall_zipWith _ _ _ _ (fun x hx y hy => (hp x hx y hy).trans (by omega))
  have hb := (list_values_encoding_bound data hd hdata _ (N+P) hl hw).2
  simpa only [P, dotPolynomial, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb

/-- One total recovery row, including zero denominator fallback, has a polynomial
whose constants depend only on the dimension cap c. -/
theorem row_encoding_bound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2^H)
    (μ η : K) (nodes answers : List K) (N : ℕ) (hlen : nodes.length ≤ N)
    (hμ : ((numberFieldEncoding basis).encode μ).length ≤ N)
    (hη : ((numberFieldEncoding basis).encode η).length ≤ N)
    (hcode : ∀ x ∈ nodes, ((numberFieldEncoding basis).encode x).length ≤ N)
    (hanswers : ∀ y ∈ answers, ((numberFieldEncoding basis).encode y).length ≤ N) :
    ((numberFieldEncoding basis).encode ((η / MaterializedFieldListMachines.shiftedDenominator (μ,nodes)) *
      (List.zipWith (fun x y => x*y) (productCoefficients nodes) answers).sum)).length ≤
      (rowPolynomial c).eval (N+H) := by
  let D := (denominatorPolynomial c).eval (N+H)
  let S := (scalePolynomial c).eval (N+H)
  let Z := (dotPolynomial c).eval (N+H)
  have hd' := denominator_encoding_bound data hd hdata μ nodes N hlen hμ hcode
  have hs : ((numberFieldEncoding basis).encode
      (η / MaterializedFieldListMachines.shiftedDenominator (μ,nodes))).length ≤ S := by
    have h := (operations_encoding_bound data hd hdata η _ (N+D)
      (hη.trans (by omega)) (hd'.trans (by omega))).2.2.2
    simpa only [S, D, scalePolynomial, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hz := dot_encoding_bound data hd hdata nodes answers N hlen hcode hanswers
  have hr := (operations_encoding_bound data hd hdata _ _ (N+S+Z)
    (hs.trans (by omega)) (hz.trans (by omega))).2.2.1
  simpa only [S, Z, rowPolynomial, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

variable [DecidableEq K]

/-- Uniform recovery output bound on the exact literal table/answer encoding.
No distinctness, nonzero-node, or answer-length promise is used. -/
theorem recovery_encoding_bound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2^H)
    (input : MaterializedLagrangeRecoveryMachines.Data K) :
    ((numberFieldEncoding basis).encode (MaterializedLagrangeRecoveryMachines.recover input)).length ≤
      (recoveryPolynomial c).eval (((MaterializedLagrangeRecoveryMachines.inputEncoding basis).encode input).length+H) := by
  let e := numberFieldEncoding basis
  let N := ((MaterializedLagrangeRecoveryMachines.inputEncoding basis).encode input).length
  let R := (rowPolynomial c).eval (N+H)
  have hN : N = 2 * ((e.prod e).list.encode input.1).length + (e.list.encode input.2).length + 1 :=
    BitEncoding.prod_length _ _ _
  have htlen : input.1.length ≤ N := ((e.prod e).list_length_le input.1).trans (by omega)
  have hrows : ∀ row ∈ input.1, (e.encode row.1).length ≤ N ∧ (e.encode row.2).length ≤ N := by
    intro row hr
    have hh := MaterializedFieldHeights.element_length_le_list (e.prod e) input.1 hr
    have hl := BitEncoding.prod_length e e row
    constructor <;> omega
  have hanswers : ∀ y ∈ input.2, (e.encode y).length ≤ N := by
    intro y hy
    exact (MaterializedFieldHeights.element_length_le_list e input.2 hy).trans (by omega)
  have hrow : ∀ row ∈ input.1, (e.encode (MaterializedLagrangeRecoveryMachines.rowTerm input row)).length ≤ R := by
    intro row hr
    have ho : (otherNodes row.1 input.1).length ≤ N := by
      exact (List.length_filter_le _ _).trans ((by simp : (input.1.map Prod.fst).length ≤ input.1.length).trans htlen)
    have hw : ∀ x ∈ otherNodes row.1 input.1, (e.encode x).length ≤ N := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_of_mem_filter hx)
      exact (hrows p hp).1
    exact row_encoding_bound data hd hdata row.1 row.2 _ input.2 N ho (hrows row hr).1 (hrows row hr).2 hw hanswers
  have hlen : (input.1.map (fun row => MaterializedLagrangeRecoveryMachines.rowTerm input row)).length ≤ N+R+1 := by
    simp only [List.length_map]
    omega
  have hw : ∀ z ∈ input.1.map (fun row => MaterializedLagrangeRecoveryMachines.rowTerm input row),
      (e.encode z).length ≤ N+R := by
    intro z hz
    obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hz
    exact (hrow row hr).trans (by omega)
  have hb := (list_values_encoding_bound data hd hdata _ (N+R) hlen hw).2
  simpa only [N, R, MaterializedLagrangeRecoveryMachines.recover, recoveryPolynomial, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb

/-- One polynomial simultaneously covers all materialized arithmetic, coefficient,
and recovery outputs; its only parameter is the fixed dimension cap. -/
def allHeightsPolynomial (c : ℕ) : Polynomial ℕ :=
  valuePolynomial c + coefficientListPolynomial c + operationPolynomial c + recoveryPolynomial c

theorem allHeightsPolynomial_ge (c T : ℕ) :
    (valuePolynomial c).eval T ≤ (allHeightsPolynomial c).eval T ∧
    (coefficientListPolynomial c).eval T ≤ (allHeightsPolynomial c).eval T ∧
    (operationPolynomial c).eval T ≤ (allHeightsPolynomial c).eval T ∧
    (recoveryPolynomial c).eval T ≤ (allHeightsPolynomial c).eval T := by
  simp only [allHeightsPolynomial, Polynomial.eval_add]
  omega

omit [DecidableEq K] in
/-- Product, sum, and every prefix coefficient vector fit one universal polynomial
in the original list's exact bit length plus the structure-height budget. -/
theorem list_encoding_bounds (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2^H)
    (xs : List K) (i : ℕ) :
    ((numberFieldEncoding basis).encode xs.prod).length ≤
      (allHeightsPolynomial c).eval (((numberFieldEncoding basis).list.encode xs).length+H) ∧
    ((numberFieldEncoding basis).encode xs.sum).length ≤
      (allHeightsPolynomial c).eval (((numberFieldEncoding basis).list.encode xs).length+H) ∧
    ((numberFieldEncoding basis).list.encode (productCoefficients (xs.take i))).length ≤
      (allHeightsPolynomial c).eval (((numberFieldEncoding basis).list.encode xs).length+H) := by
  let N := ((numberFieldEncoding basis).list.encode xs).length
  have hl : xs.length ≤ N := (numberFieldEncoding basis).list_length_le xs
  have hw : ∀ x ∈ xs, ((numberFieldEncoding basis).encode x).length ≤ N :=
    fun _ hx => MaterializedFieldHeights.element_length_le_list _ xs hx
  have hv := list_values_encoding_bound data hd hdata xs N (by omega) hw
  have hc := coefficient_list_encoding_bound data hd hdata (xs.take i) N
    (by simpa only [List.length_take] using (Nat.min_le_right i xs.length).trans hl)
    (fun _ hx => hw _ (List.mem_of_mem_take hx))
  have hp := allHeightsPolynomial_ge c (N+H)
  exact ⟨hv.1.trans hp.1, hv.2.trans hp.1, hc.trans hp.2.1⟩

/-- Total recovery uses that same universal polynomial and the unaltered exact codec. -/
theorem total_recovery_encoding_bound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2^H)
    (input : MaterializedLagrangeRecoveryMachines.Data K) :
    ((numberFieldEncoding basis).encode (MaterializedLagrangeRecoveryMachines.recover input)).length ≤
      (allHeightsPolynomial c).eval
        (((MaterializedLagrangeRecoveryMachines.inputEncoding basis).encode input).length+H) :=
  (recovery_encoding_bound data hd hdata input).trans (allHeightsPolynomial_ge c _).2.2.2

end PlanarHom.UniformFieldHeights
