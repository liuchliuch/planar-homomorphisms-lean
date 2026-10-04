import PlanarHom.PositiveBlockProgram

/-! Exact whole-program solution bijections for numeric routing blocks. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree CountingCookLevin

def compile (n : ℕ) (ops : List Instruction) : NumericFormula := (width n ops,network n ops)

def extensionList (n : ℕ) (ops : List Instruction) (w : Fin n → Bool) : List Bool :=
  execute ops (List.ofFn w)

def extension (n : ℕ) (ops : List Instruction) (w : Fin n → Bool) : Fin (width n ops) → Bool :=
  fun i => readBit (extensionList n ops w) i.val

@[simp] theorem extensionList_length (n : ℕ) (ops : List Instruction) (w : Fin n → Bool) :
    (extensionList n ops w).length=width n ops := by simp [extensionList]

@[simp] theorem ofFn_extension (n : ℕ) (ops : List Instruction) (w : Fin n → Bool) :
    List.ofFn (extension n ops w)=extensionList n ops w :=
  NorExactOne.ofFn_read _ _ (extensionList_length n ops w)

@[simp] theorem restrict_extension (n : ℕ) (ops : List Instruction) (w : Fin n → Bool) :
    (fun i : Fin n => readBit (List.ofFn (extension n ops w)) i.val)=w := by
  funext i
  rw [ofFn_extension]
  change readBit (execute ops (List.ofFn w)) i.val=w i
  rw [execute_read_old _ _ _ (by simpa using i.isLt)]
  simp [readBit]

theorem compile_iff (n : ℕ) (ops : List Instruction) (hv : Valid n ops)
    (xs : List Bool) (hlen : xs.length=width n ops) :
    Satisfies (compile n ops).2 (readBit xs) ↔
      Accepts ops (List.ofFn (fun i : Fin n => readBit xs i.val)) ∧
      xs=extensionList n ops (fun i : Fin n => readBit xs i.val) := by
  have hn : n≤xs.length := (width_ge n ops).trans hlen.ge
  rw [NorExactOne.ofFn_read_take xs n hn]
  change Satisfies (network n ops) (readBit xs) ↔ _
  rw [network_iff ops xs n hv hlen.ge]
  simp only [List.take_of_length_le hlen.le]
  rw [extensionList,NorExactOne.ofFn_read_take xs n hn]

/-- Every accepted input assignment extends once, and restricting any compiled
solution recovers that exact input. No free auxiliary bit is forgotten. -/
def solutionsEquiv (n : ℕ) (ops : List Instruction) (hv : Valid n ops) :
    {w : Fin n → Bool // Accepts ops (List.ofFn w)} ≃ NorExactOne.Solutions (compile n ops) where
  toFun w := ⟨extension n ops w.val,by
    apply (compile_iff n ops hv _ (by simp [compile])).mpr
    rw [restrict_extension,ofFn_extension]
    exact ⟨w.property,rfl⟩⟩
  invFun a := ⟨fun i => readBit (List.ofFn a.val) i.val,
    ((compile_iff n ops hv _ (by simp [compile])).mp a.property).1⟩
  left_inv w := by
    apply Subtype.ext
    exact restrict_extension n ops w.val
  right_inv a := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [ofFn_extension]
    exact ((compile_iff n ops hv _ (by simp [compile])).mp a.property).2.symm

theorem count_preserved (n : ℕ) (ops : List Instruction) (hv : Valid n ops) :
    Fintype.card (NorExactOne.Solutions (compile n ops))=
      Fintype.card {w : Fin n → Bool // Accepts ops (List.ofFn w)} :=
  (Fintype.card_congr (solutionsEquiv n ops hv)).symm

end PlanarHom.PositiveBlockProgram
