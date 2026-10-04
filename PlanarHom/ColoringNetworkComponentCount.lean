import PlanarHom.ColoringPaletteNetwork

/-! Exact disconnected-component multiplicity for the literal palette network.
The quotient is by the emitted palette links themselves. A separate, explicit
coherence proof states that all occurrences of a variable receive one palette.
No connectedness assumption and no single global division by six are used. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringPaletteNetwork
open PlanarColoringClause ThreeColorPaletteCounting ParsimoniousNorOneInThree
set_option maxHeartbeats 6000000

variable {V C L : Type}
variable (occurrence : C → Fin 3 → V) (left right : L → Sector (C := C))

def LinkRelation (c d : C) : Prop := ∃ l,(left l).1=c ∧ (right l).1=d
abbrev Component := Quot (LinkRelation left right)
def component (c : C) : Component left right := Quot.mk _ c

theorem component_surjective : Function.Surjective (component left right) := by
  intro q
  induction q using Quot.inductionOn with | h c => exact ⟨c,rfl⟩

instance [Finite C] : Finite (Component left right) :=
  Finite.of_surjective (component left right) (component_surjective left right)

/-- Precisely the source-side connectivity obligation for a chosen palette
routing network. It is an equality in a generated quotient, not graph planarity. -/
def Coherent : Prop := ∀ c d k j,occurrence c k=occurrence d j →
    component left right c=component left right d

def componentPalette (s : State occurrence left right) : Component left right → Palette :=
  Quot.lift (fun c => (s.val c).1) (by
    rintro c d ⟨l,rfl,rfl⟩
    exact s.property.2 l)

@[simp] theorem componentPalette_at (s : State occurrence left right) (c : C) :
    componentPalette occurrence left right s (component left right c)=(s.val c).1 := rfl

abbrev Solutions := {b : V → Bool // ∀ c,
  ExactlyOne (b (occurrence c 0)) (b (occurrence c 1)) (b (occurrence c 2))}

variable (cover : ∀ v,∃ c k,occurrence c k=v)

def stateBits (s : State occurrence left right) (v : V) : Bool :=
  (s.val (owner occurrence cover v)).2.val (slot occurrence cover v)

variable (coherent : Coherent occurrence left right)

include coherent in
theorem stateBits_at (s : State occurrence left right) (c : C) (k : Fin 3) :
    stateBits occurrence left right cover s (occurrence c k)=(s.val c).2.val k := by
  have ho := owner_slot occurrence cover (occurrence c k)
  have hc := coherent _ _ _ _ ho
  have hp := congrArg (componentPalette occurrence left right s) hc
  simp only [componentPalette_at] at hp
  have hs := s.property.1 _ _ _ _ ho
  simp only [statePort_primary,hp] at hs
  exact boolColor_injective ((palettePermutation (s.val c).1).injective hs)

def stateSolution (s : State occurrence left right) : Solutions occurrence :=
  ⟨stateBits occurrence left right cover s,by
    intro c
    simp only [stateBits_at occurrence left right cover coherent]
    exact (s.val c).2.property⟩

def componentState (p : Component left right → Palette) (b : Solutions occurrence) :
    State occurrence left right := by
  let s : C → PaletteState := fun c =>
    (p (component left right c),⟨fun k => b.val (occurrence c k),b.property c⟩)
  refine ⟨s,?_,?_⟩
  · intro c d k j he
    simp only [statePort_primary]
    change palettePermutation (p (component left right c)) (boolColor (b.val (occurrence c k)))=
      palettePermutation (p (component left right d)) (boolColor (b.val (occurrence d j)))
    rw [he,coherent c d k j he]
  · intro l
    apply congrArg p
    exact Quot.sound ⟨l,rfl,rfl⟩

/-- A state retains one full six-way palette choice per generated component,
independently of the Boolean solution. -/
def componentStateEquiv : State occurrence left right ≃
    (Component left right → Palette) × Solutions occurrence where
  toFun s := (componentPalette occurrence left right s,stateSolution occurrence left right cover coherent s)
  invFun x := componentState occurrence left right coherent x.1 x.2
  left_inv s := by
    apply Subtype.ext
    funext c
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      funext k
      exact stateBits_at occurrence left right cover coherent s c k
  right_inv x := by
    rcases x with ⟨p,b⟩
    apply Prod.ext
    · funext q
      induction q using Quot.inductionOn with | h c => rfl
    · apply Subtype.ext
      funext v
      change b.val (occurrence (owner occurrence cover v) (slot occurrence cover v))=b.val v
      rw [owner_slot occurrence cover v]

include cover coherent in
/-- Literal global coloring count, including arbitrarily many disconnected
formula components and the completely empty formula with no active variables. -/
theorem component_coloring_count [Fintype V] [Fintype C] [Fintype L] :
    ProperColoringPottsReduction.properColoringCount (graph occurrence left right) 3=
      6^Nat.card (Component left right)*Nat.card (Solutions occurrence) := by
  rw [coloring_card occurrence left right cover]
  rw [Nat.card_congr (componentStateEquiv occurrence left right cover coherent),Nat.card_prod]
  congr 1
  letI : Fintype (Component left right) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Fintype.card_fun,palette_card,Nat.card_eq_fintype_card]

include cover coherent in
/-- Recovery divides by the actual component factor; the empty product is one. -/
theorem recover_component_count [Fintype V] [Fintype C] [Fintype L] :
    ProperColoringPottsReduction.properColoringCount (graph occurrence left right) 3 /
      6^Nat.card (Component left right)=Nat.card (Solutions occurrence) := by
  rw [component_coloring_count occurrence left right cover coherent]
  exact Nat.mul_div_cancel_left _ (pow_pos (by omega) _)

end PlanarHom.ColoringPaletteNetwork
