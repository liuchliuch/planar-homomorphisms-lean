import PlanarHom.DependentFieldListMachines

open PlanarHom PlanarHom.Complexity

-- The parameter occurs once in the original input; values keep their own exact words.
example {X : Type} {A : X → Type} (ex : BitEncoding X) (e : ∀ x, BitEncoding (A x))
    (x : X) (a : A x) (xs : List (A x)) :
    (DependentFieldCodecs.input ex e).encode ⟨x,(a,xs)⟩ =
      BitEncoding.frame (ex.encode x) ++ BitEncoding.frame ((e x).encode a) ++ (e x).list.encode xs := by
  simp [DependentFieldCodecs.input, DependentFieldCodecs.sigma, BitEncoding.prod, List.append_assoc]

example {X : Type} {A : X → Type} (ex : BitEncoding X) (e : ∀ x, BitEncoding (A x))
    (x : X) (a b : A x) :
    (DependentFieldCodecs.step ex e).encode ⟨x,(a,b)⟩ =
      ((DependentFieldCodecs.tagged ex e x).prod (e x)).encode (a,b) :=
  DependentFieldCodecs.step_sameWords ex e x a b

example {X : Type} {A : X → Type} (f : ∀ x, A x → A x → A x) (x : X) (a : A x) :
    DependentFieldFoldMachines.fold f ⟨x,(a,[])⟩ = ⟨x,a⟩ := rfl

-- No DecidableEq X, runtime inverse, or arbitrary height-polynomial premise.
example {X : Type} (ex : BitEncoding X) (K : X → Type)
    [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
    (d : X → ℕ) (basis : ∀ x, Module.Basis (Fin (d x)) ℚ (K x))
    (c : ℕ) (hc : ∀ x, d x ≤ c)
    (hp : FP ex BitEncoding.rat.list (fun x => UniformFieldPresentationHeights.presentationList (basis x)))
    (hmul : FP (DependentFieldCodecs.pair ex (fun x => numberFieldEncoding (basis x)))
      (DependentFieldCodecs.sigma ex (fun x => numberFieldEncoding (basis x)))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩)) :
    FP (DependentFieldCodecs.input ex (fun x => numberFieldEncoding (basis x)))
      (DependentFieldCodecs.sigma ex (fun x => numberFieldEncoding (basis x)))
      (fun s : Σ x, K x × List (K x) => ⟨s.1,s.2.1*s.2.2.prod⟩) :=
  DependentFieldListMachines.fp_fold_product ex K d basis c hc hp hmul

example {X : Type} (ex : BitEncoding X) (K : X → Type)
    [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
    (d : X → ℕ) (basis : ∀ x, Module.Basis (Fin (d x)) ℚ (K x))
    (c : ℕ) (hc : ∀ x, d x ≤ c)
    (hp : FP ex BitEncoding.rat.list (fun x => UniformFieldPresentationHeights.presentationList (basis x)))
    (hadd : FP (DependentFieldCodecs.pair ex (fun x => numberFieldEncoding (basis x)))
      (DependentFieldCodecs.sigma ex (fun x => numberFieldEncoding (basis x)))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1+s.2.2⟩)) :
    FP (DependentFieldCodecs.input ex (fun x => numberFieldEncoding (basis x)))
      (DependentFieldCodecs.sigma ex (fun x => numberFieldEncoding (basis x)))
      (fun s : Σ x, K x × List (K x) => ⟨s.1,s.2.1+s.2.2.sum⟩) :=
  DependentFieldListMachines.fp_fold_sum ex K d basis c hc hp hadd
