import Mathlib.Data.List.Lex

/-! NEW exact convexity of a common natural-word prefix in lexicographic order. -/
namespace PlanarHom.NatWordPrefix

 theorem head_le {x y : ℕ} {xs ys : List ℕ} (h : x::xs≤y::ys) : x≤y := by
  rcases lt_or_eq_of_le h with h | h
  · exact List.head_le_of_lt h
  · exact Nat.le_of_eq (List.cons.inj h).1

 theorem tail_le {x : ℕ} {xs ys : List ℕ} (h : x::xs≤x::ys) : xs≤ys := by
  rcases lt_or_eq_of_le h with h | h
  · exact le_of_lt (show xs<ys from List.lex_cons_iff.mp h)
  · exact le_of_eq (List.cons.inj h).2

 theorem between_append (pre left right middle : List ℕ)
    (hl : pre++left≤middle) (hr : middle≤pre++right) : pre.IsPrefix middle := by
  induction pre generalizing middle with
  | nil => exact List.nil_prefix
  | cons x pre ih =>
    cases middle with
    | nil =>
      rcases lt_or_eq_of_le hl with h | h
      · cases h
      · cases h
    | cons y middle =>
      have hxy:=head_le hl
      have hyx:=head_le hr
      have he:x=y:=Nat.le_antisymm hxy hyx
      subst y
      obtain ⟨tail,he⟩:=ih middle (tail_le hl) (tail_le hr)
      exact ⟨tail,by simp only [List.cons_append,he]⟩

 theorem convex {pre left middle right : List ℕ}
    (hl : pre.IsPrefix left) (hr : pre.IsPrefix right)
    (hlm : left≤middle) (hmr : middle≤right) : pre.IsPrefix middle := by
  obtain ⟨l,rfl⟩:=hl
  obtain ⟨r,rfl⟩:=hr
  exact between_append pre l r middle hlm hmr

end PlanarHom.NatWordPrefix
