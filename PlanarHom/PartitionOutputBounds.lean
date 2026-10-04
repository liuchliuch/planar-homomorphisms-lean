import PlanarHom.FixedAlphabetOutputBounds
import PlanarHom.MixedParallelSemantics

/-!
# Actual fixed-number-field partition output sizes

Every assignment contributes a word of length vertices + binary occurrences +
unary occurrences over one fixed finite alphabet. Integer coordinate certificates
and the actual rational normalization machine bound the canonical output code.
The proof applies with loops, parallel edges, isolated vertices and signed values.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.PartitionOutputBounds
open Complexity FixedAlphabetOutputBounds

variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {binaryTypes unaryTypes : ℕ}

/-- The fixed finite alphabet includes the default value used for malformed coordinates. -/
abbrev Factor (C : Type) (binaryTypes unaryTypes : ℕ) :=
  Unit ⊕ (C ⊕ ((Fin binaryTypes × C × C) ⊕ (Fin unaryTypes × C)))

/-- Each symbol denotes one fixed language or background value. -/
def factorValue (M : Fin binaryTypes → Matrix C C K)
    (U : Fin unaryTypes → C → K) (w : C → K) : Factor C binaryTypes unaryTypes → K
  | .inl _ => 1
  | .inr (.inl c) => w c
  | .inr (.inr (.inl (l, c, d))) => M l c d
  | .inr (.inr (.inr (l, c))) => U l c

/-- An ordered edge occurrence retains both endpoint colors and its label. -/
def binaryFactor (vertices binaryTypes unaryTypes : ℕ) (σ : Fin vertices → C)
    (e : ℕ × (ℕ × ℕ)) : Factor C binaryTypes unaryTypes :=
  if h : e.1 < vertices ∧ e.2.1 < vertices ∧ e.2.2 < binaryTypes then
    .inr (.inr (.inl (⟨e.2.2, h.2.2⟩, σ ⟨e.1, h.1⟩, σ ⟨e.2.1, h.2.1⟩)))
  else .inl ()

/-- An ordered unary occurrence retains its vertex color and label. -/
def unaryFactor (vertices binaryTypes unaryTypes : ℕ) (σ : Fin vertices → C)
    (e : ℕ × ℕ) : Factor C binaryTypes unaryTypes :=
  if h : e.1 < vertices ∧ e.2 < unaryTypes then
    .inr (.inr (.inr (⟨e.2, h.2⟩, σ ⟨e.1, h.1⟩)))
  else .inl ()

/-- Every assignment has exactly one symbol per vertex or listed occurrence. -/
def assignmentWord (g : MixedCode) (σ : Fin g.vertices → C) :
    List (Factor C binaryTypes unaryTypes) :=
  List.ofFn (fun v => Sum.inr (Sum.inl (σ v))) ++
    g.edges.map (binaryFactor g.vertices binaryTypes unaryTypes σ) ++
    g.unaries.map (unaryFactor g.vertices binaryTypes unaryTypes σ)

omit [Fintype C] in
theorem assignmentWord_length (g : MixedCode) (σ : Fin g.vertices → C) :
    (assignmentWord (binaryTypes := binaryTypes) (unaryTypes := unaryTypes) g σ).length =
      g.vertices + g.edges.length + g.unaries.length := by
  simp [assignmentWord, Nat.add_assoc]

omit [Fintype C] [Algebra ℚ K] in
theorem factorValue_binaryFactor (M : Fin binaryTypes → Matrix C C K)
    (U : Fin unaryTypes → C → K) (w : C → K) (vertices : ℕ)
    (σ : Fin vertices → C) (e : ℕ × (ℕ × ℕ)) :
    factorValue M U w (binaryFactor vertices binaryTypes unaryTypes σ e) =
      MixedCode.binaryValue vertices binaryTypes M σ e := by
  unfold binaryFactor MixedCode.binaryValue
  split <;> rfl

omit [Fintype C] [Algebra ℚ K] in
theorem factorValue_unaryFactor (M : Fin binaryTypes → Matrix C C K)
    (U : Fin unaryTypes → C → K) (w : C → K) (vertices : ℕ)
    (σ : Fin vertices → C) (e : ℕ × ℕ) :
    factorValue M U w (unaryFactor vertices binaryTypes unaryTypes σ e) =
      MixedCode.unaryValue vertices unaryTypes U σ e := by
  unfold unaryFactor MixedCode.unaryValue
  split <;> rfl

omit [Fintype C] [Algebra ℚ K] in
/-- The word product is the exact weighted assignment contribution. -/
theorem assignmentWord_product (g : MixedCode) (σ : Fin g.vertices → C)
    (M : Fin binaryTypes → Matrix C C K) (U : Fin unaryTypes → C → K) (w : C → K) :
    ((assignmentWord g σ).map (factorValue M U w)).prod =
      (∏ v, w (σ v)) * (g.edges.map (MixedCode.binaryValue g.vertices binaryTypes M σ)).prod *
        (g.unaries.map (MixedCode.unaryValue g.vertices unaryTypes U σ)).prod := by
  simp only [assignmentWord, List.map_append, List.prod_append, List.map_ofFn,
    List.prod_ofFn, List.map_map]
  have hb : factorValue M U w ∘ binaryFactor g.vertices binaryTypes unaryTypes σ =
      MixedCode.binaryValue g.vertices binaryTypes M σ := by
    funext e
    exact factorValue_binaryFactor M U w g.vertices σ e
  have hu : factorValue M U w ∘ unaryFactor g.vertices binaryTypes unaryTypes σ =
      MixedCode.unaryValue g.vertices unaryTypes U σ := by
    funext e
    exact factorValue_unaryFactor M U w g.vertices σ e
  rw [hb, hu]
  simp only [Function.comp_apply, factorValue, mul_assoc]

/-- Exact mixed-language evaluation is a finite sum of equal-length alphabet words. -/
theorem evaluate_eq_sum_words (g : MixedCode) (valid : g.Valid binaryTypes unaryTypes)
    (M : Fin binaryTypes → Matrix C C K) (U : Fin unaryTypes → C → K) (w : C → K) :
    g.evaluate valid M U w =
      ∑ σ : Fin g.vertices → C, ((assignmentWord g σ).map (factorValue M U w)).prod := by
  simp only [MixedCode.evaluate, assignmentWord_product]

/-- Fixed languages have a polynomial bound on actual canonical number-field outputs. -/
theorem exists_polynomial_mixed_evaluation_length_bound {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes → Matrix C C K) (U : Fin unaryTypes → C → K) (w : C → K) :
    ∃ p : Polynomial ℕ, ∀ (g : MixedCode) (valid : g.Valid binaryTypes unaryTypes),
      ((numberFieldEncoding basis).encode (g.evaluate valid M U w)).length ≤
        p.eval (MixedCode.encoding.encode g).length := by
  obtain ⟨p, hp⟩ := exists_output_polynomial basis (factorValue M U w) (max 1 (Fintype.card C))
  refine ⟨p, fun g valid => ?_⟩
  let L := g.vertices + g.edges.length + g.unaries.length
  have hc : Fintype.card (Fin g.vertices → C) ≤ max 1 (Fintype.card C) ^ (L + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    apply (Nat.pow_le_pow_left (Nat.le_max_right 1 (Fintype.card C)) g.vertices).trans
    exact Nat.pow_le_pow_right (Nat.le_max_left 1 _) (by dsimp [L]; omega)
  rw [evaluate_eq_sum_words]
  apply (hp (assignmentWord (binaryTypes := binaryTypes) (unaryTypes := unaryTypes) g) L
    (assignmentWord_length g) hc).trans
  exact MachineComposition.natPolynomial_monotone p (MixedCode.size_le_length g)

end PlanarHom.PartitionOutputBounds
