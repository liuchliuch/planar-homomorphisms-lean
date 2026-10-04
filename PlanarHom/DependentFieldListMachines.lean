import PlanarHom.DependentFieldFoldMachines
import PlanarHom.UniformFieldPresentationFamilies

/-! Uniform dependent field sums/products from actual source-(b) operators and presentations. -/
noncomputable section
namespace PlanarHom.DependentFieldListMachines
open Complexity FieldCoordinateCertificates IntegerCoordinateBounds MachineComposition
open UniformFieldPresentationHeights UniformFieldHeights
variable {X : Type} (ex : BitEncoding X) (K : X → Type)
variable [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
variable (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))

abbrev fieldEncoding (x : X) := numberFieldEncoding (basis x)

/-- Prefix bounds are derived from the actual FP presentation, with no extra
height invariant assumed by either public fold theorem. -/
theorem exists_prefix_size_bound (c : ℕ) (hc : ∀ x, dimension x ≤ c)
    (hpresentation : FP ex BitEncoding.rat.list (fun x => presentationList (basis x))) :
    ∃ p : Polynomial ℕ, ∀ (s : Σ x, K x × List (K x)) (i : ℕ), i ≤ s.2.2.length →
      ((DependentFieldCodecs.tagged ex (fieldEncoding K dimension basis) s.1).encode
        ((s.2.2.take i).foldl (fun a b => a*b) s.2.1)).length ≤
          p.eval ((DependentFieldCodecs.prepared ex (fieldEncoding K dimension basis)).encode s).length ∧
      ((DependentFieldCodecs.tagged ex (fieldEncoding K dimension basis) s.1).encode
        ((s.2.2.take i).foldl (fun a b => a+b) s.2.1)).length ≤
          p.eval ((DependentFieldCodecs.prepared ex (fieldEncoding K dimension basis)).encode s).length := by
  obtain ⟨H,hH⟩ := UniformFieldPresentationFamilies.exists_height_polynomial ex K dimension basis c hc hpresentation
  let Q := (valuePolynomial c).comp (Polynomial.X+H)
  let P := Polynomial.C 2*Polynomial.X + Q + 1
  refine ⟨P, fun s i _hi => ?_⟩
  rcases s with ⟨x,a,xs⟩
  let e := fieldEncoding K dimension basis x
  let N := ((DependentFieldCodecs.prepared ex (fieldEncoding K dimension basis)).encode ⟨x,(a,xs)⟩).length
  have hN : N = 2*(2*(ex.encode x).length+(e.encode a).length+1)+(e.list.encode xs).length+1 := by
    simp only [N, DependentFieldCodecs.prepared, DependentFieldCodecs.sigma, List.length_append,
      BitEncoding.frame_length]
    dsimp only [e]
    omega
  have hx : (ex.encode x).length ≤ N := by omega
  have ha : (e.encode a).length ≤ N := by omega
  have hl : (e.list.encode xs).length ≤ N := by omega
  have hlen : (a :: xs.take i).length ≤ N+1 := by
    have hs := (e.list_length_le xs).trans hl
    simp only [List.length_cons, List.length_take]
    omega
  have hcode : ∀ z ∈ a :: xs.take i, (e.encode z).length ≤ N := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ha
    · exact (MaterializedFieldHeights.element_length_le_list e xs (List.mem_of_mem_take hz)).trans hl
  have hb := UniformFieldHeights.list_values_encoding_bound (cleared (basis x)) (hc x) (hH x)
    (a :: xs.take i) N hlen hcode
  have hq : (valuePolynomial c).eval (N+H.eval (ex.encode x).length) ≤ Q.eval N := by
    simp only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
    exact natPolynomial_monotone _ (Nat.add_le_add_left (natPolynomial_monotone H hx) N)
  have hm : (e.encode (a*(xs.take i).prod)).length ≤ Q.eval N := by
    simpa only [List.prod_cons] using hb.1.trans hq
  have hs : (e.encode (a+(xs.take i).sum)).length ≤ Q.eval N := by
    simpa only [List.sum_cons] using hb.2.trans hq
  simp only [MaterializedFieldListMachines.fold_mul, MaterializedFieldListMachines.fold_add,
    DependentFieldCodecs.tagged, DependentFieldCodecs.sigma, List.length_append, BitEncoding.frame_length]
  change (2*(ex.encode x).length+1+(e.encode (a*(xs.take i).prod)).length ≤ P.eval N) ∧
    (2*(ex.encode x).length+1+(e.encode (a+(xs.take i).sum)).length ≤ P.eval N)
  simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  constructor <;> omega

/-- Source (b)'s uniform multiplication is the only multiplication-machine
premise; all loop state sizes follow from the materialized presentation. -/
theorem fp_fold_product (c : ℕ) (hc : ∀ x, dimension x ≤ c)
    (hpresentation : FP ex BitEncoding.rat.list (fun x => presentationList (basis x)))
    (hmul : FP (DependentFieldCodecs.pair ex (fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩)) :
    FP (DependentFieldCodecs.input ex (fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (fieldEncoding K dimension basis))
      (fun s : Σ x, K x × List (K x) => ⟨s.1,s.2.1*s.2.2.prod⟩) := by
  obtain ⟨P,hP⟩ := exists_prefix_size_bound ex K dimension basis c hc hpresentation
  exact (DependentFieldFoldMachines.fp_fold ex (fieldEncoding K dimension basis) (fun _ a b => a*b)
    hmul P (fun s i hi => (hP s i hi).1)).congr (fun s => by
      rcases s with ⟨x,a,xs⟩
      simp only [DependentFieldFoldMachines.fold, MaterializedFieldListMachines.fold_mul])

/-- Source (b)'s actual uniform addition, with the same proved dependent trace
invariant and no assumptions about mismatched field encodings. -/
theorem fp_fold_sum (c : ℕ) (hc : ∀ x, dimension x ≤ c)
    (hpresentation : FP ex BitEncoding.rat.list (fun x => presentationList (basis x)))
    (hadd : FP (DependentFieldCodecs.pair ex (fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1+s.2.2⟩)) :
    FP (DependentFieldCodecs.input ex (fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (fieldEncoding K dimension basis))
      (fun s : Σ x, K x × List (K x) => ⟨s.1,s.2.1+s.2.2.sum⟩) := by
  obtain ⟨P,hP⟩ := exists_prefix_size_bound ex K dimension basis c hc hpresentation
  exact (DependentFieldFoldMachines.fp_fold ex (fieldEncoding K dimension basis) (fun _ a b => a+b)
    hadd P (fun s i hi => (hP s i hi).2)).congr (fun s => by
      rcases s with ⟨x,a,xs⟩
      simp only [DependentFieldFoldMachines.fold, MaterializedFieldListMachines.fold_add])

end PlanarHom.DependentFieldListMachines
