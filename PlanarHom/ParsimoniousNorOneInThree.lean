import PlanarHom.ProperColoringNaturalReduction

/-!
# NEW reconstruction: literal parsimonious NOR/EQV one-in-three gadget

The three positive clauses (x,i,n), (y,j,n), (e,i,j) are checked directly,
including uniqueness of every auxiliary value. This is the Boolean operator in
Appendix B of R. Barbanchon, "On Unique Graph 3-Colorability and Parsimonious
Reductions in the Plane", TCS 319 (2004), DOI 10.1016/j.tcs.2004.02.003.
No decision-to-counting hardness inference or source-hardness premise is used.
-/
noncomputable section
open Classical
namespace PlanarHom.ParsimoniousNorOneInThree

/-- Exactly one of the three literal Boolean values is true. -/
def ExactlyOne (x y z : Bool) : Prop := x.toNat+y.toNat+z.toNat=1

/-- The actual three positive clauses, with no negated literals. -/
def Gate (x y n e i j : Bool) : Prop :=
  ExactlyOne x i n ∧ ExactlyOne y j n ∧ ExactlyOne e i j

/-- Every output and every auxiliary bit is forced, not merely existential. -/
theorem gate_iff (x y n e i j : Bool) : Gate x y n e i j ↔
    n=!(x || y) ∧ e=decide (x=y) ∧ i=(!x && y) ∧ j=(x && !y) := by
  cases x <;> cases y <;> cases n <;> cases e <;> cases i <;> cases j <;> simp [Gate,ExactlyOne]

/-- The unique four-bit extension in output, equivalence, left, right order. -/
def extension (x y : Bool) : Fin 4 → Bool := ![!(x||y),decide (x=y),!x&&y,x&&!y]

theorem gate_extension (x y : Bool) :
    Gate x y (extension x y 0) (extension x y 1) (extension x y 2) (extension x y 3) := by
  cases x <;> cases y <;> simp [Gate,ExactlyOne,extension]

theorem gate_unique (x y : Bool) (s : Fin 4 → Bool) :
    Gate x y (s 0) (s 1) (s 2) (s 3) ↔ s=extension x y := by
  rw [gate_iff]
  constructor
  · rintro ⟨hn,he,hi,hj⟩
    funext k
    fin_cases k
    · exact hn
    · exact he
    · exact hi
    · exact hj
  · rintro rfl
    exact (gate_iff _ _ _ _ _ _).mp (gate_extension x y)

/-- A type-level bijection certifies exactly one local extension for every input. -/
def gateEquivUnit (x y : Bool) :
    {s : Fin 4 → Bool // Gate x y (s 0) (s 1) (s 2) (s 3)} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨extension x y,gate_extension x y⟩
  left_inv s := by
    apply Subtype.ext
    exact ((gate_unique x y s.val).mp s.property).symm
  right_inv _ := rfl

theorem gate_count (x y : Bool) :
    Fintype.card {s : Fin 4 → Bool // Gate x y (s 0) (s 1) (s 2) (s 3)}=1 := by
  exact (Fintype.card_congr (gateEquivUnit x y)).trans (by simp)

/-- A concrete positive clause is a triple of variable names. -/
abbrev Clause (V : Type) := V × V × V
abbrev Formula (V : Type) := List (Clause V)

def Satisfies {V : Type} (f : Formula V) (σ : V → Bool) : Prop :=
  ∀ c∈f, ExactlyOne (σ c.1) (σ c.2.1) (σ c.2.2)

def rename {V W : Type} (r : V → W) (f : Formula V) : Formula W :=
  f.map (fun c => (r c.1,r c.2.1,r c.2.2))

theorem satisfies_rename {V W : Type} (r : V → W) (f : Formula V) (σ : W → Bool) :
    Satisfies (rename r f) σ ↔ Satisfies f (σ ∘ r) := by
  constructor
  · intro h c hc
    exact h _ (List.mem_map.mpr ⟨c,hc,rfl⟩)
  · intro h c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact h d hd

/-- The emitted clauses, with four fresh variables indexed 0,1,2,3. -/
def gateClauses {V : Type} (x y : V) : Formula (V ⊕ Fin 4) :=
  [(Sum.inl x,Sum.inr 2,Sum.inr 0),
   (Sum.inl y,Sum.inr 3,Sum.inr 0),
   (Sum.inr 1,Sum.inr 2,Sum.inr 3)]

def appendGate {V : Type} (f : Formula V) (x y : V) : Formula (V ⊕ Fin 4) :=
  rename Sum.inl f ++ gateClauses x y

def extendAssignment {V : Type} (σ : V → Bool) (x y : V) : V ⊕ Fin 4 → Bool :=
  Sum.elim σ (extension (σ x) (σ y))

theorem satisfies_gateClauses {V : Type} (x y : V) (τ : V ⊕ Fin 4 → Bool) :
    Satisfies (gateClauses x y) τ ↔ Gate (τ (.inl x)) (τ (.inl y))
      (τ (.inr 0)) (τ (.inr 1)) (τ (.inr 2)) (τ (.inr 3)) := by
  simp [Satisfies,gateClauses,Gate]

/-- The compiler appends exactly three clauses and exactly four variables. -/
@[simp] theorem appendGate_length {V : Type} (f : Formula V) (x y : V) :
    (appendGate f x y).length=f.length+3 := by simp [appendGate,rename,gateClauses]

/-- Full global characterization after one emitted gadget, including all old
clauses and uniqueness of the four fresh Boolean values. -/
theorem satisfies_appendGate {V : Type} (f : Formula V) (x y : V) (τ : V ⊕ Fin 4 → Bool) :
    Satisfies (appendGate f x y) τ ↔
      Satisfies f (τ ∘ Sum.inl) ∧ τ=extendAssignment (τ ∘ Sum.inl) x y := by
  have hs : Satisfies (appendGate f x y) τ ↔
      Satisfies (rename Sum.inl f) τ ∧ Satisfies (gateClauses x y) τ := by
    constructor
    · intro h
      exact ⟨fun c hc => h c (List.mem_append_left _ hc),
        fun c hc => h c (List.mem_append_right _ hc)⟩
    · rintro ⟨h₁,h₂⟩ c hc
      exact (List.mem_append.mp hc).elim (h₁ c) (h₂ c)
  rw [hs,satisfies_rename,satisfies_gateClauses,
    gate_unique (τ (.inl x)) (τ (.inl y)) (fun k => τ (.inr k))]
  constructor
  · rintro ⟨hf,hg⟩
    refine ⟨hf,?_⟩
    funext v
    cases v with
    | inl v => rfl
    | inr k => exact congrFun hg k
  · rintro ⟨hf,hg⟩
    refine ⟨hf,?_⟩
    funext k
    exact congrFun hg (Sum.inr k)

/-- This is an explicit parsimonious solution bijection for arbitrary old
positive one-in-three formulas, including unused original variables. -/
def appendGateSolutionsEquiv {V : Type} (f : Formula V) (x y : V) :
    {σ : V → Bool // Satisfies f σ} ≃
      {τ : V ⊕ Fin 4 → Bool // Satisfies (appendGate f x y) τ} where
  toFun σ := ⟨extendAssignment σ.val x y, (satisfies_appendGate _ _ _ _).mpr ⟨σ.property,rfl⟩⟩
  invFun τ := ⟨τ.val ∘ Sum.inl, ((satisfies_appendGate _ _ _ _).mp τ.property).1⟩
  left_inv _ := rfl
  right_inv τ := by
    apply Subtype.ext
    exact ((satisfies_appendGate _ _ _ _).mp τ.property).2.symm

theorem appendGate_count {V : Type} [Fintype V] (f : Formula V) (x y : V) :
    Fintype.card {τ : V ⊕ Fin 4 → Bool // Satisfies (appendGate f x y) τ} =
      Fintype.card {σ : V → Bool // Satisfies f σ} :=
  (Fintype.card_congr (appendGateSolutionsEquiv f x y)).symm

end PlanarHom.ParsimoniousNorOneInThree
