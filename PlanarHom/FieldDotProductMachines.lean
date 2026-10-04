import PlanarHom.ListDecompositionMachines
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.ListDedupMachines

/-! Actual exact field dot products with total shortest-list semantics and polynomial bit bounds. -/

noncomputable section
namespace PlanarHom.FieldDotProductMachines
open Complexity PairProjectionMachines MachineComposition ListFlattenMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- Remaining right input and exact running sum form the actual fold state. -/
def step (s : List K × K) (a : K) : List K × K :=
  (s.1.tail, s.2 + a * s.1.headD 0)

omit [Algebra ℚ K] in
theorem fold_step (xs ys : List K) (z : K) :
    xs.foldl step (ys,z) = (ys.drop xs.length, z + (List.zipWith (· * ·) xs ys).sum) := by
  induction xs generalizing ys z with
  | nil => simp
  | cons a xs ih =>
    cases ys with
    | nil => simp [List.foldl_cons,step,ih]
    | cons b ys => simp [List.foldl_cons,step,ih,add_assoc]

theorem fp_step :
    FP (((numberFieldEncoding basis).list.prod (numberFieldEncoding basis)).prod (numberFieldEncoding basis))
      ((numberFieldEncoding basis).list.prod (numberFieldEncoding basis))
      (fun p => step p.1 p.2) := by
  let e := numberFieldEncoding basis
  let es := e.list.prod e
  have hs := fp_fst es e
  have ha := fp_snd es e
  have hyr := hs.comp (fp_fst e.list e)
  have hz := hs.comp (fp_snd e.list e)
  have hy := hyr.comp (ListDecompositionMachines.fp_headD e 0)
  have ht := hyr.comp (ListDecompositionMachines.fp_tail e 0)
  have hm := (ha.pair hy).comp (FixedFieldArithmetic.fp_multiplication basis)
  exact ht.pair ((hz.pair hm).comp (FixedFieldArithmetic.fp_addition basis))

private theorem mem_zipWith {A B D : Type} (f : A → B → D) (xs : List A) (ys : List B) {z : D}
    (hz : z ∈ List.zipWith f xs ys) : ∃ a ∈ xs, ∃ b ∈ ys, f a b = z := by
  induction xs generalizing ys with
  | nil => simp at hz
  | cons a xs ih =>
    cases ys with
    | nil => simp at hz
    | cons b ys =>
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨a, by simp, b, by simp, rfl⟩
      · obtain ⟨a',ha,b',hb,he⟩ := ih ys hz
        exact ⟨a', by simp [ha], b', by simp [hb], he⟩

/-- A real multiplication computer and a real sum computer supply the only local size estimates. -/
theorem exists_prefix_size_bound : ∃ p : Polynomial ℕ,
    ∀ (s : List K × K) (xs : List K) (i : ℕ),
      (((numberFieldEncoding basis).list.prod (numberFieldEncoding basis)).encode
        ((xs.take i).foldl step s)).length ≤
      p.eval ((((numberFieldEncoding basis).list.prod (numberFieldEncoding basis)).prod
        (numberFieldEncoding basis).list).encode (s,xs)).length := by
  obtain ⟨mulComputer⟩ := FixedFieldArithmetic.fp_multiplication basis
  obtain ⟨sumComputer⟩ := MaterializedFieldListMachines.fp_fold_sum basis
  let pm := outputLengthPolynomial mulComputer
  let ps := outputLengthPolynomial sumComputer
  let q := pm.comp (Polynomial.C 3 * Polynomial.X + Polynomial.C 1)
  let r := (Polynomial.C 2 * q + Polynomial.C 5) * Polynomial.X + Polynomial.C 2
  refine ⟨Polynomial.C 6 * Polynomial.X + Polynomial.C 3 + ps.comp r, ?_⟩
  rintro ⟨ys,z⟩ xs i
  let e := numberFieldEncoding basis
  let N := (((e.list.prod e).prod e.list).encode ((ys,z),xs)).length
  have hn : N = 2 * (2 * (e.list.encode ys).length + (e.encode z).length + 1) +
      (e.list.encode xs).length + 1 := by simp [N, BitEncoding.prod_length]
  have hys : (e.list.encode ys).length ≤ N := by omega
  have hz : (e.encode z).length ≤ N := by omega
  have hxs : (e.list.encode xs).length ≤ N := by omega
  have hxlen : xs.length ≤ N := (e.list_length_le xs).trans hxs
  let products := List.zipWith (· * ·) (xs.take i) ys
  have hpval (v : K) (hv : v ∈ products) : (e.encode v).length ≤ q.eval N := by
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_zipWith (· * ·) (xs.take i) ys hv
    have haN := (MaterializedFieldHeights.element_length_le_list e xs (List.mem_of_mem_take ha)).trans hxs
    have hbN := (MaterializedFieldHeights.element_length_le_list e ys hb).trans hys
    have hip : ((e.prod e).encode (a,b)).length ≤ 3*N+1 := by
      rw [BitEncoding.prod_length]
      change 2*(e.encode a).length+(e.encode b).length+1≤3*N+1
      omega
    have ho := encoded_output_length_le mulComputer (a,b)
    have hm := natPolynomial_monotone pm hip
    apply ho.trans
    simpa only [q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, BitEncoding.toFinEncoding] using hm
  have hplen : products.length ≤ N := by
    dsimp [products]
    rw [List.length_zipWith, List.length_take]
    omega
  have hpword := CoefficientListHeights.list_encoding_length_le e products (q.eval N) hpval
  have hsumInput : ((e.prod e.list).encode (z,products)).length ≤ r.eval N := by
    rw [BitEncoding.prod_length]
    have hlist := hpword.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hplen) 1)
    simp only [r, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    nlinarith
  have hsum : (e.encode (z + products.sum)).length ≤ ps.eval (r.eval N) :=
    (encoded_output_length_le sumComputer (z,products)).trans (natPolynomial_monotone ps hsumInput)
  have hpdrop := ListDedupMachines.payloadSize_sublist e (List.drop_sublist (xs.take i).length ys)
  have hdrop : (e.list.encode (ys.drop (xs.take i).length)).length ≤ 3*N+1 := by
    have hwhole := (payloadSize_le_word e ys).trans hys
    have hword := word_length_le_payload e (ys.drop (xs.take i).length)
    omega
  rw [fold_step, BitEncoding.prod_length]
  change 2*(e.list.encode (ys.drop (xs.take i).length)).length + (e.encode (z+products.sum)).length+1 ≤ _
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_comp]
  change _ ≤ 6*N+3+ps.eval (r.eval N)
  omega

/-- This is an ordinary polynomial-time machine, with no uncosted host fold. -/
theorem fp_fold :
    FP ((((numberFieldEncoding basis).list.prod (numberFieldEncoding basis)).prod
        (numberFieldEncoding basis).list))
      ((numberFieldEncoding basis).list.prod (numberFieldEncoding basis))
      (fun p : (List K × K) × List K => p.2.foldl step p.1) := by
  obtain ⟨p,hp⟩ := exists_prefix_size_bound basis
  exact ListFoldMachines.fp_foldl (numberFieldEncoding basis)
    ((numberFieldEncoding basis).list.prod (numberFieldEncoding basis)) step (fp_step basis) p
      (fun s xs i _ => hp s xs i)

/-- Exact total shortest-list dot product. Final projection clears all unused right-input words. -/
theorem fp_dot :
    FP ((numberFieldEncoding basis).list.prod (numberFieldEncoding basis).list)
      (numberFieldEncoding basis)
      (fun p : List K × List K => (List.zipWith (· * ·) p.1 p.2).sum) := by
  let e := numberFieldEncoding basis
  have hl := fp_fst e.list e.list
  have hr := fp_snd e.list e.list
  have hz := fp_const (e.list.prod e.list) e 0
  have hprep := (hr.pair hz).pair hl
  exact ((hprep.comp (fp_fold basis)).comp (fp_snd e.list e)).congr
    (fun p => by simp [Function.comp_apply, fold_step])

end PlanarHom.FieldDotProductMachines
