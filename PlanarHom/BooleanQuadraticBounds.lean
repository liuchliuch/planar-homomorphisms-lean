import PlanarHom.BooleanQuadraticStepMachines

/-! NEW complete encoded-state bounds for dense elimination, including every
intermediate prefix and arbitrary initial ragged coefficient lists. -/
namespace PlanarHom.BooleanQuadratic
open Complexity ListFlattenMachines

def Dense (q : Data) : Prop :=
  q.2.2.length=dimension q ∧ ∀row∈q.2.2,row.length=dimension q

 theorem dense_pivot (q : Data) (i j : ℕ) : Dense (pivot q i j) := by
  simp [Dense,pivot,dimension]
 theorem dense_remove (q : Data) (i : ℕ) : Dense (remove q i) := by
  simp [Dense,remove,dimension]
 theorem dense_step (s : State) (i : ℕ) : Dense (step s i).1 := by
  unfold step
  split
  · exact dense_pivot _ _ _
  · exact dense_remove _ _
 theorem dense_fold (xs : List ℕ) (s : State) (hs : Dense s.1) : Dense (xs.foldl step s).1 := by
  induction xs generalizing s with
  | nil=>exact hs
  | cons i xs ih=>exact ih (step s i) (dense_step s i)

 theorem bool_code_length (b : Bool) : (BitEncoding.bool.encode b).length=1 := rfl
 theorem bool_list_bound (xs : List Bool) : (BitEncoding.bool.list.encode xs).length≤9*xs.length+1 := by
  have h:=word_length_le_payload BitEncoding.bool xs
  simp only [payloadSize_eq,bool_code_length,List.map_const,List.sum_replicate] at h
  have hm : (xs.map (fun _ : Bool=>1)).sum=xs.length := by
    induction xs with
    | nil=>rfl
    | cons a xs ih=>simp [Nat.add_comm]
  rw [hm] at h
  nlinarith

 theorem dense_data_bound (q : Data) (hq : Dense q) :
    (dataCode.encode q).length ≤ 100*(dimension q+1)^2 := by
  have hl:=bool_list_bound q.2.1
  have hn:=(word_length_le_payload BitEncoding.bool.list q.2.2)
  have hs:=(ListMapMachines.sum_map_le_mul (fun r=>(BitEncoding.bool.list.encode r).length) q.2.2 (9*dimension q+1) (by
      intro r hr
      exact (bool_list_bound r).trans (by rw [hq.2 r hr])))
  rw [payloadSize_eq] at hn
  rw [hq.1] at hs hn
  simp only [dataCode,BitEncoding.prod_length,bool_code_length]
  unfold dimension at hl
  change (BitEncoding.bool.list.encode q.2.1).length≤9*dimension q+1 at hl
  nlinarith

 theorem state_bound (s : State) (hs : Dense s.1) :
    (stateCode.encode s).length ≤ 200*(dimension s.1+1)^2+2*s.2.1+3 := by
  have h:=dense_data_bound s.1 hs
  simp only [stateCode,BitEncoding.prod_length,BitEncoding.unaryNat_length,bool_code_length]
  omega

 theorem dimension_le_state (s : State) : dimension s.1≤(stateCode.encode s).length := by
  have h:=BitEncoding.list_length_le BitEncoding.bool s.1.2.1
  simp only [stateCode,dataCode,BitEncoding.prod_length,bool_code_length,
    BitEncoding.unaryNat_length]
  change dimension s.1≤_ at h
  omega

 theorem pairs_le_state (s : State) : s.2.1≤(stateCode.encode s).length := by
  simp only [stateCode,BitEncoding.prod_length,BitEncoding.unaryNat_length,bool_code_length]
  omega

 theorem fold_state_bound (xs : List ℕ) (s : State) :
    (stateCode.encode (xs.foldl step s)).length ≤
      (stateCode.encode s).length+200*(dimension s.1+1)^2+2*(s.2.1+xs.length)+3 := by
  cases xs with
  | nil=>simp only [List.foldl_nil,List.length_nil]; omega
  | cons i xs=>
    have hd:=dense_fold xs (step s i) (dense_step s i)
    have hb:=state_bound (xs.foldl step (step s i)) hd
    have hn:=fold_dimension (i::xs) s
    have hp:=fold_pairs_bound (i::xs) s
    simp only [List.foldl_cons] at hn hp ⊢
    rw [hn] at hb
    omega

 theorem prefix_state_bound (s : State) (xs : List ℕ) (i : ℕ) :
    (stateCode.encode ((xs.take i).foldl step s)).length ≤
      (Polynomial.C 300*(Polynomial.X+1)^2).eval ((stateCode.prod BitEncoding.nat.list).encode (s,xs)).length := by
  let N:=((stateCode.prod BitEncoding.nat.list).encode (s,xs)).length
  have hN:N=2*(stateCode.encode s).length+(BitEncoding.nat.list.encode xs).length+1 :=
    BitEncoding.prod_length _ _ _
  have hs:(stateCode.encode s).length≤N := by omega
  have hn:(dimension s.1)≤N := (dimension_le_state s).trans hs
  have hp:s.2.1≤N := (pairs_le_state s).trans hs
  have hx:xs.length≤N := (BitEncoding.list_length_le BitEncoding.nat xs).trans (by omega)
  have ht:(xs.take i).length≤N := by rw [List.length_take]; exact (Nat.min_le_right _ _).trans hx
  have hb:=fold_state_bound (xs.take i) s
  have hsq:(dimension s.1+1)^2≤(N+1)^2 := Nat.pow_le_pow_left (by omega) _
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one]
  change _≤300*(N+1)^2
  nlinarith

end PlanarHom.BooleanQuadratic
