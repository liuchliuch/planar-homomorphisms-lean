import PlanarHom.TypedGadgetAppendColoredReduction

/-! Literal mixed-language APPEND regressions: original cross/XX/YY labels,
one ordinary unary label, a new XX loop, and exactly one fresh private tag. -/
noncomputable section
namespace PlanarHom.TypedGadgetAppend.ColoredRegressions
open Complexity PrescribedDomains FixedGadgetNetwork EdgeSubstitution

/-- Three genuinely different old endpoint policies. -/
def mixedPolicy (l : Fin 3) (x y : Fin 2) : Prop :=
  if l=0 then x≠y else if l=1 then x=0 ∧ y=0 else x=1 ∧ y=1

def unaryPolicy (_ : Fin 1) (_ : Fin 2) : Prop := True

def xxPolicy (x y : Fin 2) : Prop := x=0 ∧ y=0

def twoCrossEdges : TwoTerminal (Fin 1) (Fin 2) where
  src i := if i=0 then .inl false else .inr 0
  dst i := if i=0 then .inr 0 else .inl true

def privateTag : Fin 1 → Fin 2 := fun _=>1

def freshTemplate : Template :=
  ofTypedColoredTwoTerminal twoCrossEdges (fun _=>(0:Fin 3)) privateTag 1

theorem twoCrossEdges_typed (x y : Fin 2) (h : xxPolicy x y) (i : Fin 2) :
    mixedPolicy 0 (TwoTerminal.extend x y privateTag (twoCrossEdges.src i))
      (TwoTerminal.extend x y privateTag (twoCrossEdges.dst i)) := by
  obtain ⟨rfl,rfl⟩ := h
  fin_cases i <;> simp [mixedPolicy,twoCrossEdges,TwoTerminal.extend,privateTag]

example : ∃ tag,TemplateTyping (ut:=1) mixedPolicy freshTemplate tag ∧ tag 0=0 ∧ tag 1=0 :=
  ofTypedColoredTwoTerminal_typing_exists mixedPolicy xxPolicy twoCrossEdges
    (fun _=>(0:Fin 3)) privateTag 1 twoCrossEdges_typed 0 0 ⟨rfl,rfl⟩

/-- Same-side original labels remain legal in the original source. -/
example : mixedPolicy 1 0 0 ∧ mixedPolicy 2 1 1 ∧ mixedPolicy 0 0 1 := by
  simp [mixedPolicy]

def templates : List Template :=
  [identityTemplate (0:Fin 3),identityTemplate (1:Fin 3),identityTemplate (2:Fin 3),freshTemplate]

/-- Four old vertices; the first edge is the appended XX loop. The two old
ordinary unary occurrences precede the four exact intrinsic occurrences. -/
def host : MixedCode :=
  ⟨4,[(0,0,3),(0,1,0),(0,2,1),(1,3,2)],
    [(0,0),(1,0),(0,1),(1,2),(2,1),(3,2)]⟩

def query : MixedCode := substitute templates host

/-- The new loop allocates one private vertex. Every old occurrence keeps its
label and endpoints, and the sole fresh intrinsic tag is appended once. -/
theorem query_exact : query =
    ⟨5,[(0,4,0),(4,0,0),(0,1,0),(0,2,1),(1,3,2)],
      [(0,0),(1,0),(0,1),(1,2),(2,1),(3,2),(4,2)]⟩ := by
  rfl

theorem query_valid : query.Valid 3 (1+2) := by
  rw [query_exact]
  simp [MixedCode.Valid]

def queryTag (v : ℕ) : Fin 2 := if v=1 ∨ v=3 ∨ v=4 then 1 else 0

/-- The resulting literal query has exact metadata and keeps both old ordinary
unaries, despite retaining XX and YY companion edges in the source. -/
theorem query_typed : Tagged mixedPolicy unaryPolicy [(0,0),(1,0)] query queryTag := by
  refine ⟨query_valid,?_,?_,?_,?_⟩
  · rw [query_exact]
    rfl
  · intro a ha
    rw [query_exact] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl <;> norm_num [mixedPolicy,queryTag]
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> rw [query_exact] <;> decide
  · intros
    trivial

end PlanarHom.TypedGadgetAppend.ColoredRegressions
