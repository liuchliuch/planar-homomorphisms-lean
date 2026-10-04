import PlanarHom.PortPatchAssembly
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact coloring composition for the same literal sigma-incidence assembly
used by the geometric port-patch theorem. The proof shares boundary variables
and reconstructs every internal coloring, retaining exact multiplicity. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringPatchComposition
open MultiGraph
variable {C B A : Type} {P W E : C → Type}
variable (G : ∀ c,MultiGraph (P c ⊕ W c) (E c)) (port : ∀ c,P c → B)

abbrev GlobalVertex := B ⊕ Sigma W

def glue (b : B → A) (u : ∀ c,W c → A) : GlobalVertex (B := B) (W := W) → A :=
  Sum.elim b (fun w => u w.1 w.2)

def localColor (col : GlobalVertex (B := B) (W := W) → A) (c : C) : P c ⊕ W c → A :=
  col ∘ PortPatchAssembly.placeVertex port c

def LocalProper (c : C) (col : P c ⊕ W c → A) : Prop := ∀ e,col ((G c).src e)≠col ((G c).dst e)
def GlobalProper (col : GlobalVertex (B := B) (W := W) → A) : Prop :=
  ∀ e,col ((PortPatchAssembly.graph G port).src e)≠col ((PortPatchAssembly.graph G port).dst e)

theorem globalProper_iff (col : GlobalVertex (B := B) (W := W) → A) :
    GlobalProper G port col ↔ ∀ c,LocalProper G c (localColor port col c) := by
  constructor
  · intro h c e
    exact h ⟨c,e⟩
  · intro h e
    exact h e.1 e.2

@[simp] theorem localColor_glue (b : B → A) (u : ∀ c,W c → A) (c : C) :
    localColor port (glue b u) c=Sum.elim (b ∘ port c) (u c) := by
  funext v
  cases v <;> rfl

def boundaryPart (col : GlobalVertex (B := B) (W := W) → A) : B → A := col ∘ Sum.inl
def insidePart (col : GlobalVertex (B := B) (W := W) → A) : ∀ c,W c → A := fun c w => col (.inr ⟨c,w⟩)

@[simp] theorem glue_parts (col : GlobalVertex (B := B) (W := W) → A) :
    glue (boundaryPart col) (insidePart col)=col := by
  funext v
  cases v <;> rfl

variable (relation : C → (B → A) → Prop) (extend : ∀ c,(B → A) → W c → A)
variable (local_iff : ∀ c b u,LocalProper G c (Sum.elim (b ∘ port c) u) ↔ relation c b ∧ u=extend c b)

include local_iff

/-- Literal gluing preserves each local uniqueness statement simultaneously;
no choices of auxiliary colorings remain in the global object. -/
theorem glued_iff (b : B → A) (u : ∀ c,W c → A) :
    GlobalProper G port (glue b u) ↔ (∀ c,relation c b) ∧ u=(fun c => extend c b) := by
  rw [globalProper_iff]
  simp only [localColor_glue,local_iff]
  constructor
  · intro h
    exact ⟨fun c => (h c).1,funext (fun c => (h c).2)⟩
  · rintro ⟨h,rfl⟩ c
    exact ⟨h c,rfl⟩

/-- A full explicit bijection between assembled graph colorings and admissible
boundary assignments. Geometric gluing uses the identical graph constructor. -/
def coloringEquiv :
    {col : GlobalVertex (B := B) (W := W) → A // GlobalProper G port col} ≃
      {b : B → A // ∀ c,relation c b} where
  toFun col := ⟨boundaryPart col.val,by
    have h := (glued_iff G port relation extend local_iff (boundaryPart col.val) (insidePart col.val)).mp
      (by simpa only [glue_parts] using col.property)
    exact h.1⟩
  invFun b := ⟨glue b.val (fun c => extend c b.val),
    (glued_iff G port relation extend local_iff _ _).mpr ⟨b.property,rfl⟩⟩
  left_inv col := by
    have h := (glued_iff G port relation extend local_iff (boundaryPart col.val) (insidePart col.val)).mp
      (by simpa only [glue_parts] using col.property)
    apply Subtype.ext
    change glue (boundaryPart col.val) (fun c => extend c (boundaryPart col.val))=col.val
    rw [← h.2,glue_parts]
  right_inv b := rfl

/-- Cardinal equality is independent of computable finite-enumeration choices. -/
theorem coloring_card :
    Nat.card {col : GlobalVertex (B := B) (W := W) → A // GlobalProper G port col} =
      Nat.card {b : B → A // ∀ c,relation c b} :=
  Nat.card_congr (coloringEquiv G port relation extend local_iff)

end PlanarHom.ColoringPatchComposition
