import PlanarHom.ParsimoniousNorOneInThree

/-! Compositional exact counting semantics for acyclic Boolean NOR programs.
This closes the auxiliary-assignment multiplicity gate, but does not assert a
Cook-Levin compiler, a planar embedding, or a global raw-bit reduction yet. -/
noncomputable section
open Classical
namespace PlanarHom.ParsimoniousNorOneInThree

/-- Three clauses force an existing variable true and three fresh bits false. -/
def forceTrueClauses {V : Type} (t : V) : Formula (V ⊕ Fin 3) :=
  [(Sum.inl t,Sum.inr 1,Sum.inr 0),
   (Sum.inl t,Sum.inr 2,Sum.inr 0),
   (Sum.inr 1,Sum.inl t,Sum.inr 2)]

def forceTrue {V : Type} (f : Formula V) (t : V) : Formula (V ⊕ Fin 3) :=
  rename Sum.inl f ++ forceTrueClauses t

def extendFalse {V : Type} (σ : V → Bool) : V ⊕ Fin 3 → Bool :=
  Sum.elim σ (fun _ => false)

theorem forceTrue_local (t f i k : Bool) :
    (ExactlyOne t i f ∧ ExactlyOne t k f ∧ ExactlyOne i t k) ↔
      t=true ∧ f=false ∧ i=false ∧ k=false := by
  cases t <;> cases f <;> cases i <;> cases k <;> simp [ExactlyOne]

theorem satisfies_forceTrue {V : Type} (f : Formula V) (t : V) (τ : V ⊕ Fin 3 → Bool) :
    Satisfies (forceTrue f t) τ ↔
      Satisfies f (τ ∘ Sum.inl) ∧ τ (.inl t)=true ∧ τ=extendFalse (τ ∘ Sum.inl) := by
  have hsplit : Satisfies (forceTrue f t) τ ↔
      Satisfies (rename Sum.inl f) τ ∧ Satisfies (forceTrueClauses t) τ := by
    constructor
    · intro h
      exact ⟨fun c hc => h c (List.mem_append_left _ hc),
        fun c hc => h c (List.mem_append_right _ hc)⟩
    · rintro ⟨h₁,h₂⟩ c hc
      exact (List.mem_append.mp hc).elim (h₁ c) (h₂ c)
  have hg : Satisfies (forceTrueClauses t) τ ↔
      τ (.inl t)=true ∧ τ (.inr 0)=false ∧ τ (.inr 1)=false ∧ τ (.inr 2)=false := by
    simpa only [Satisfies,forceTrueClauses,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq] using
        forceTrue_local (τ (.inl t)) (τ (.inr 0)) (τ (.inr 1)) (τ (.inr 2))
  rw [hsplit,satisfies_rename,hg]
  constructor
  · rintro ⟨hf,ht,h0,h1,h2⟩
    refine ⟨hf,ht,?_⟩
    funext v
    cases v with
    | inl v => rfl
    | inr k => fin_cases k <;> assumption
  · rintro ⟨hf,ht,he⟩
    exact ⟨hf,ht,congrFun he (.inr 0),congrFun he (.inr 1),congrFun he (.inr 2)⟩

def forceTrueSolutionsEquiv {V : Type} (f : Formula V) (t : V) :
    {σ : V → Bool // Satisfies f σ ∧ σ t=true} ≃
      {τ : V ⊕ Fin 3 → Bool // Satisfies (forceTrue f t) τ} where
  toFun σ := ⟨extendFalse σ.val, (satisfies_forceTrue _ _ _).mpr ⟨σ.property.1,σ.property.2,rfl⟩⟩
  invFun τ := ⟨τ.val ∘ Sum.inl, by
    have h := (satisfies_forceTrue _ _ _).mp τ.property
    exact ⟨h.1,h.2.1⟩⟩
  left_inv _ := rfl
  right_inv τ := by
    apply Subtype.ext
    exact ((satisfies_forceTrue _ _ _).mp τ.property).2.2.symm

/-- Appending a gate preserves any later acceptance condition exactly. -/
def appendGateAcceptedEquiv {V : Type} (f : Formula V) (x y : V)
    (accept : (V ⊕ Fin 4 → Bool) → Prop) :
    {σ : V → Bool // Satisfies f σ ∧ accept (extendAssignment σ x y)} ≃
      {τ : V ⊕ Fin 4 → Bool // Satisfies (appendGate f x y) τ ∧ accept τ} where
  toFun σ := ⟨extendAssignment σ.val x y,
    ⟨(satisfies_appendGate _ _ _ _).mpr ⟨σ.property.1,rfl⟩,σ.property.2⟩⟩
  invFun τ := ⟨τ.val ∘ Sum.inl, by
    have h := (satisfies_appendGate _ _ _ _).mp τ.property.1
    exact ⟨h.1,h.2 ▸ τ.property.2⟩⟩
  left_inv _ := rfl
  right_inv τ := by
    apply Subtype.ext
    exact ((satisfies_appendGate _ _ _ _).mp τ.property.1).2.symm

/-- A finite acyclic Boolean computation: every new gate reads only existing
variables, then its four deterministic outputs become available to later gates. -/
inductive Program : Type → Type 1 where
  | halt {V : Type} (output : V) : Program V
  | gate {V : Type} (left right : V) (next : Program (V ⊕ Fin 4)) : Program V

namespace Program

def eval {V : Type} : Program V → (V → Bool) → Bool
  | .halt output, σ => σ output
  | .gate x y next, σ => next.eval (extendAssignment σ x y)

def steps {V : Type} : Program V → ℕ
  | .halt _ => 0
  | .gate _ _ next => next.steps+1

def Variables {V : Type} : Program V → Type
  | .halt _ => V ⊕ Fin 3
  | .gate _ _ next => next.Variables

def variableFintype {V : Type} : (p : Program V) → Fintype V → Fintype p.Variables
  | .halt _, h => by
    letI := h
    exact inferInstanceAs (Fintype (V ⊕ Fin 3))
  | .gate _ _ next, h => by
    letI := h
    exact next.variableFintype inferInstance

/-- Concrete compilation to positive exactly-one-in-three clauses. -/
def compile {V : Type} : (p : Program V) → Formula V → Formula p.Variables
  | .halt output, f => forceTrue f output
  | .gate x y next, f => next.compile (appendGate f x y)

/-- Every accepted input assignment has one and only one compiled satisfying
assignment. This is an explicit bijection, so no unknown multiplicity remains. -/
def solutionsEquiv {V : Type} : (p : Program V) → (f : Formula V) →
    {σ : V → Bool // Satisfies f σ ∧ p.eval σ=true} ≃
      {τ : p.Variables → Bool // Satisfies (p.compile f) τ}
  | .halt output, f => forceTrueSolutionsEquiv f output
  | .gate x y next, f =>
      (appendGateAcceptedEquiv f x y (fun τ => next.eval τ=true)).trans
        (next.solutionsEquiv (appendGate f x y))

theorem count_preserved {V : Type} [Fintype V] (p : Program V) (f : Formula V) :
    letI := p.variableFintype inferInstance
    Fintype.card {τ : p.Variables → Bool // Satisfies (p.compile f) τ} =
      Fintype.card {σ : V → Bool // Satisfies f σ ∧ p.eval σ=true} := by
  letI := p.variableFintype inferInstance
  exact (Fintype.card_congr (p.solutionsEquiv f)).symm

theorem compile_length {V : Type} (p : Program V) (f : Formula V) :
    (p.compile f).length=f.length+3*(p.steps+1) := by
  induction p with
  | halt output => simp [compile,forceTrue,rename,forceTrueClauses,steps]
  | gate x y next ih =>
    rw [compile,ih,appendGate_length]
    simp only [steps]
    omega

theorem variables_card {V : Type} (p : Program V) : ∀ h : Fintype V,
    @Fintype.card p.Variables (p.variableFintype h)=@Fintype.card V h+4*p.steps+3 := by
  induction p with
  | halt output =>
    intro h
    letI := h
    simp [Variables,variableFintype,steps]
  | gate x y next ih =>
    intro h
    letI := h
    simpa [Variables,variableFintype,steps,Fintype.card_sum,Nat.mul_add,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using ih (inferInstance : Fintype (_ ⊕ Fin 4))

end Program
end PlanarHom.ParsimoniousNorOneInThree
