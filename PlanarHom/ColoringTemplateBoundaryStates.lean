import PlanarHom.ParsimoniousBlockTemplate

/-! Removing the uniquely determined Boolean auxiliaries of an actual block
while retaining all its exposed inputs and outputs. This uses the proved
source-template semantics, rather than postulating a coloring gate relation. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringTemplateBoundaryStates
open ParsimoniousNorOneInThree ParsimoniousBlockTemplate

variable (T : Template) (ports : ℕ) (lo : T.inputs≤ports) (hi : ports≤T.inputs+T.fresh)

def input (b : Fin ports → Bool) : Fin T.inputs → Bool := fun i => b (Fin.castLE lo i)
def restrict (a : Fin (T.inputs+T.fresh) → Bool) : Fin ports → Bool := fun i => a (Fin.castLE hi i)

def Allowed (b : Fin ports → Bool) : Prop :=
  T.accepts (input T ports lo b) ∧ ∀ i,T.extend (input T ports lo b) (Fin.castLE hi i)=b i

abbrev SourceSolutions := {a : Fin (T.inputs+T.fresh) → Bool // Satisfies T.clauses a}
abbrev BoundarySolutions := {b : Fin ports → Bool // Allowed T ports lo hi b}

theorem input_restrict (a : Fin (T.inputs+T.fresh) → Bool) :
    input T ports lo (restrict T ports hi a)=(fun i => a (Fin.castAdd T.fresh i)) := rfl

theorem extension_satisfies (a : Fin T.inputs → Bool) (ha : T.accepts a) : Satisfies T.clauses (T.extend a) := by
  have he : (fun i => T.extend a (Fin.castAdd T.fresh i))=a := funext (T.old_value a)
  rw [T.correct,he]
  exact ⟨ha,rfl⟩

def boundaryEquiv : SourceSolutions T ≃ BoundarySolutions T ports lo hi where
  toFun a := ⟨restrict T ports hi a.val,by
    have h := (T.correct a.val).mp a.property
    refine ⟨h.1,?_⟩
    intro i
    exact (congrFun h.2 (Fin.castLE hi i)).symm⟩
  invFun b := ⟨T.extend (input T ports lo b.val),extension_satisfies T _ b.property.1⟩
  left_inv a := Subtype.ext ((T.correct a.val).mp a.property).2.symm
  right_inv b := by
    apply Subtype.ext
    funext i
    exact b.property.2 i

@[simp] theorem boundaryEquiv_value (a : SourceSolutions T) (i : Fin ports) :
    (boundaryEquiv T ports lo hi a).val i=a.val (Fin.castLE hi i) := rfl

@[simp] theorem boundaryEquiv_symm_port (b : BoundarySolutions T ports lo hi) (i : Fin ports) :
    ((boundaryEquiv T ports lo hi).symm b).val (Fin.castLE hi i)=b.val i := b.property.2 i

end PlanarHom.ColoringTemplateBoundaryStates
