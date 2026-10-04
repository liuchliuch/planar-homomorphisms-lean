import PlanarHom.SharedLinearCertificates
import PlanarHom.ListFoldMachines

/-! Compilation of a materialized fixed-dimensional linear recurrence. The
shared-denominator theorem proves all prefix heights from the coordinate
representation and actual entry computers. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.LinearFoldMachines
open Complexity MachineComposition PairProjectionMachines SharedLinearCertificates
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)
variable {C A V I : Type} [Fintype I] [Nonempty I]

theorem fp_family_output_bound {J X Y : Type} [Fintype J]
    (ex : BitEncoding X) (ey : BitEncoding Y) (f : J → X → Y)
    (hf : ∀ j, FP ex ey (f j)) :
    ∃ p : Polynomial ℕ, ∀ j x, (ey.encode (f j x)).length ≤ p.eval (ex.encode x).length := by
  let body := fun j => Classical.choice (hf j)
  refine ⟨∑ j, outputLengthPolynomial (body j), fun j x => ?_⟩
  apply (encoded_output_length_le (body j) x).trans
  rw [Polynomial.eval_finset_sum]
  exact Finset.single_le_sum (f:=fun i => (outputLengthPolynomial (body i)).eval (ex.encode x).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

def step (op : C → V → A → V) (v : C × V) (a : A) : C × V :=
  (v.1,op v.1 v.2 a)

theorem fold_step (op : C → V → A → V) (c : C) (v : V) (xs : List A) :
    xs.foldl (step op) (c,v) = (c,xs.foldl (op c) v) := by
  induction xs generalizing v with
  | nil => rfl
  | cons a xs ih => exact ih _

omit [Algebra ℚ K] [Nonempty I] in
theorem coord_fold (op : C → V → A → V) (coord : V → I → K)
    (entry : C → A → I × I → K)
    (he : ∀ c v a i, coord (op c v a) i = ∑ j, coord v j * entry c a (i,j))
    (c : C) (v : V) (xs : List A) :
    coord (xs.foldl (op c) v) = (xs.map (entry c)).foldl transition (coord v) := by
  induction xs generalizing v with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldl_cons,List.map_cons,ih]
    congr 1
    exact funext (he c v a)

theorem exists_prefix_size_bound
    (ec : BitEncoding C) (ea : BitEncoding A) (ev : BitEncoding V)
    (op : C → V → A → V) (coord : V → I → K) (entry : C → A → I × I → K)
    (he : ∀ c v a i, coord (op c v a) i = ∑ j, coord v j * entry c a (i,j))
    (hcoord : ∀ v i, ((numberFieldEncoding basis).encode (coord v i)).length ≤ (ev.encode v).length)
    (M : ℕ) (hsize : ∀ v L, (∀ i, ((numberFieldEncoding basis).encode (coord v i)).length ≤ L) →
      (ev.encode v).length ≤ M*(L+1))
    (hentry : ∀ i, FP (ec.prod ea) (numberFieldEncoding basis) (fun ca => entry ca.1 ca.2 i)) :
    ∃ p : Polynomial ℕ, ∀ (v : C × V) (xs : List A) (i : ℕ),
      ((ec.prod ev).encode ((xs.take i).foldl (step op) v)).length ≤
        p.eval (((ec.prod ev).prod ea.list).encode (v,xs)).length := by
  obtain ⟨data⟩ := IntegerCoordinateBounds.exists_clearedCoordinates basis (fun k : Fin dimension => basis k)
  obtain ⟨q,hq⟩ := fp_family_output_bound (ec.prod ea) (numberFieldEncoding basis)
    (fun i ca => entry ca.1 ca.2 i) hentry
  let q' := Polynomial.X + q.comp (Polynomial.C 3*Polynomial.X+Polynomial.C 1)
  let r := (EncodingSizeBounds.coordinateOutputPolynomial dimension (heightBase data I)
    (heightBase data I)).comp
    ((Polynomial.C (choiceExponent I)*q'+Polynomial.C 2)*(Polynomial.X+Polynomial.C 1))
  refine ⟨Polynomial.C 2*Polynomial.X+Polynomial.C M*(r+Polynomial.C 1)+Polynomial.C 1, ?_⟩
  rintro ⟨c,v⟩ xs i
  let N := (((ec.prod ev).prod ea.list).encode ((c,v),xs)).length
  have hN : N = 2*(2*(ec.encode c).length+(ev.encode v).length+1)+(ea.list.encode xs).length+1 := by
    simp only [N,BitEncoding.prod_length]
  have hc : (ec.encode c).length ≤ N := by omega
  have hv : (ev.encode v).length ≤ N := by omega
  have hx : (ea.list.encode xs).length ≤ N := by omega
  have hlen : ((xs.take i).map (entry c)).length ≤ N := by
    have h := (ea.list_length_le xs).trans hx
    simp only [List.length_map,List.length_take]
    omega
  have hqN : N ≤ q'.eval N := by
    simp only [q',Polynomial.eval_add,Polynomial.eval_X]
    omega
  have hm : ∀ m ∈ (xs.take i).map (entry c), ∀ j,
      ((numberFieldEncoding basis).encode (m j)).length ≤ q'.eval N := by
    intro m hm j
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    have haN := (MaterializedFieldHeights.element_length_le_list ea xs (List.mem_of_mem_take ha)).trans hx
    have hin : ((ec.prod ea).encode (c,a)).length ≤ 3*N+1 := by
      rw [BitEncoding.prod_length]
      change 2*(ec.encode c).length+(ea.encode a).length+1 ≤ 3*N+1
      omega
    have he' := (hq j (c,a)).trans (natPolynomial_monotone q hin)
    simp only [q',Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_comp,
      Polynomial.eval_mul,Polynomial.eval_C]
    exact he'.trans (Nat.le_add_left _ _)
  have hr (j : I) : ((numberFieldEncoding basis).encode (coord ((xs.take i).foldl (op c) v) j)).length
      ≤ r.eval N := by
    rw [coord_fold op coord entry he]
    simpa only [r,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_add,
      Polynomial.eval_C,Polynomial.eval_X] using fold_encoding_bound data
      ((xs.take i).map (entry c)) (coord v) N (q'.eval N) hlen
      (fun j => (hcoord v j).trans (hv.trans hqN)) hm j
  have hs := hsize _ _ hr
  rw [fold_step,BitEncoding.prod_length]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  change 2*(ec.encode c).length+(ev.encode ((xs.take i).foldl (op c) v)).length+1 ≤
    2*N+M*(r.eval N+1)+1
  omega

/-- Actual typed fold compilation with its growth theorem discharged by linear
coordinates. No iteration-height assumption is part of the conclusion. -/
theorem fp_fold
    (ec : BitEncoding C) (ea : BitEncoding A) (ev : BitEncoding V)
    (op : C → V → A → V) (coord : V → I → K) (entry : C → A → I × I → K)
    (he : ∀ c v a i, coord (op c v a) i = ∑ j, coord v j * entry c a (i,j))
    (hcoord : ∀ v i, ((numberFieldEncoding basis).encode (coord v i)).length ≤ (ev.encode v).length)
    (M : ℕ) (hsize : ∀ v L, (∀ i, ((numberFieldEncoding basis).encode (coord v i)).length ≤ L) →
      (ev.encode v).length ≤ M*(L+1))
    (hentry : ∀ i, FP (ec.prod ea) (numberFieldEncoding basis) (fun ca => entry ca.1 ca.2 i))
    (hstep : FP ((ec.prod ev).prod ea) (ec.prod ev) (fun p => step op p.1 p.2)) :
    FP (ec.prod (ev.prod ea.list)) ev (fun p => p.2.2.foldl (op p.1) p.2.1) := by
  obtain ⟨p,hp⟩ := exists_prefix_size_bound basis ec ea ev op coord entry he hcoord M hsize hentry
  have hf := ListFoldMachines.fp_foldl ea (ec.prod ev) (step op) hstep p (fun v xs i _ => hp v xs i)
  have hc := fp_fst ec (ev.prod ea.list)
  have hs := fp_snd ec (ev.prod ea.list)
  have hv := hs.comp (fp_fst ev ea.list)
  have hx := hs.comp (fp_snd ev ea.list)
  exact ((((hc.pair hv).pair hx).comp hf).comp (fp_snd ec ev)).congr
    (fun p => by simp only [Function.comp_apply,fold_step])

end PlanarHom.LinearFoldMachines
