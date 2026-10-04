import PlanarHom.BooleanRetentionPrograms

/-! NEW exact equal-length block slicing for the actual sample-major answer
stream. No distinctness assumption is imposed on samples or answers. -/
namespace PlanarHom.BooleanAnswerSlices

theorem slice_flatMap {A B : Type} (xs : List A) (f : A→List B) (n : ℕ)
    (hlen : ∀x∈xs,(f x).length=n) (j : ℕ) (hj:j<xs.length) :
    ((xs.flatMap f).drop (j*n)).take n = f xs[j] := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    have hx:=hlen x (by simp)
    have ht:∀y∈xs,(f y).length=n:=fun y hy=>hlen y (by simp [hy])
    cases j with
    | zero =>
      simp only [Nat.zero_mul,List.drop_zero,List.flatMap_cons,List.getElem_cons_zero]
      rw [List.take_append_of_le_length (by omega : n≤(f x).length),←hx,List.take_length]
    | succ j =>
      rw [List.flatMap_cons,List.drop_append]
      have hn:n≤(j+1)*n:=by rw [Nat.add_mul,Nat.one_mul];omega
      rw [List.drop_eq_nil_of_le (by omega : (f x).length≤(j+1)*n),List.nil_append,hx]
      have he:(j+1)*n-n=j*n:=by rw [Nat.add_mul,Nat.one_mul,Nat.add_sub_cancel]
      rw [he]
      exact ih ht j (by simpa using hj)

end PlanarHom.BooleanAnswerSlices
