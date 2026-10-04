import Mathlib.Data.List.Lex

/-! NEW exact order preservation for a state-dependent relabeling of finite
ranked paths. Local ranks are required to be strictly increasing on their
actual finite range; applications prove this from literal row projections. -/
namespace PlanarHom.StateWordRelabel
variable {S : Type}

 def walk (step : S→ℕ→S) : S→List ℕ→S
   | s, [] => s
   | s, i::xs => walk step (step s i) xs
 def relabel (code : S→ℕ→ℕ) (step : S→ℕ→S) : S→List ℕ→List ℕ
   | s, [] => []
   | s, i::xs => code s i::relabel code step (step s i) xs
 def Valid (bound : S→ℕ) (step : S→ℕ→S) : S→List ℕ→Prop
   | _, [] => True
   | s, i::xs => i<bound s ∧ Valid bound step (step s i) xs

 theorem walk_append (step : S→ℕ→S) (s : S) (xs ys : List ℕ) :
    walk step s (xs++ys)=walk step (walk step s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih => exact ih (step s i)

 theorem relabel_append (code : S→ℕ→ℕ) (step : S→ℕ→S) (s : S) (xs ys : List ℕ) :
    relabel code step s (xs++ys)=relabel code step s xs++relabel code step (walk step s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih => simpa only [List.cons_append,relabel,walk] using congrArg (List.cons (code s i)) (ih (step s i))

 theorem valid_append (bound : S→ℕ) (step : S→ℕ→S) (s : S) (xs ys : List ℕ) :
    Valid bound step s (xs++ys) ↔ Valid bound step s xs ∧ Valid bound step (walk step s xs) ys := by
  induction xs generalizing s with
  | nil => simp [Valid,walk]
  | cons i xs ih => simp only [List.cons_append,Valid,walk,ih,and_assoc]

 theorem relabel_lt_iff (bound : S→ℕ) (code : S→ℕ→ℕ) (step : S→ℕ→S)
    (hcode : ∀s i j,i<j→j<bound s→code s i<code s j)
    (s : S) (xs ys : List ℕ) (hx : Valid bound step s xs) (hy : Valid bound step s ys) :
    relabel code step s xs<relabel code step s ys ↔ xs<ys := by
  induction xs generalizing s ys with
  | nil =>
    cases ys with
    | nil => simp [relabel]
    | cons y ys => constructor <;> intro h <;> exact List.Lex.nil
  | cons x xs ih =>
    cases ys with
    | nil => constructor <;> intro h <;> cases h
    | cons y ys =>
      rcases hx with ⟨hx,hxs⟩
      rcases hy with ⟨hy,hys⟩
      rcases lt_trichotomy x y with hxy | hxy | hyx
      · constructor
        · intro h; exact List.Lex.rel hxy
        · intro h; exact List.Lex.rel (hcode s x y hxy hy)
      · subst y
        change List.Lex (·<·) (code s x::relabel code step (step s x) xs)
          (code s x::relabel code step (step s x) ys) ↔ List.Lex (·<·) (x::xs) (x::ys)
        rw [List.lex_cons_iff,List.lex_cons_iff]
        exact ih (step s x) ys hxs hys
      · have hrev:=hcode s y x hyx hx
        constructor
        · intro h
          have hh:=List.head_le_of_lt h
          omega
        · intro h
          have hh:=List.head_le_of_lt h
          omega

end PlanarHom.StateWordRelabel
