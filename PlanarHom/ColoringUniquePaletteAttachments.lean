import PlanarHom.ColoringPalettePairCopy
import PlanarHom.ThreeColorPaletteCounting

/-! Literal attachment of any finite family of uniquely forced palette copies.
The original graph is retained, and each copy receives its own private vertices.
A proved coloring bijection ensures exposed copies introduce no multiplicity. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringUniquePaletteAttachments
open MultiGraph ThreeColorPaletteCounting

variable {V E C : Type} {W F : C → Type}
variable (G : MultiGraph V E) (K : ∀ c,MultiGraph (Bool ⊕ W c) (F c))
variable (black gray : C → V)

abbrev Vertex := V ⊕ Sigma W
abbrev Edge := E ⊕ Sigma F

def place (c : C) : Bool ⊕ W c → Vertex (V := V) (W := W)
  | .inl false => .inl (black c)
  | .inl true => .inl (gray c)
  | .inr w => .inr ⟨c,w⟩

def graph : MultiGraph (Vertex (V := V) (W := W)) (Edge (E := E) (F := F)) where
  src := Sum.elim (Sum.inl ∘ G.src) (fun p => place black gray p.1 ((K p.1).src p.2))
  dst := Sum.elim (Sum.inl ∘ G.dst) (fun p => place black gray p.1 ((K p.1).dst p.2))

def inputColor (a b : Fin 3) : Bool → Fin 3 := fun q => if q then b else a

def localProper (c : C) (col : Bool ⊕ W c → Fin 3) : Prop :=
  ∀ e,col ((K c).src e)≠col ((K c).dst e)

variable (extend : ∀ c,Fin 3 → Fin 3 → W c → Fin 3)
variable (local_spec : ∀ c a b,a≠b → ∀ u,
  localProper K c (Sum.elim (inputColor a b) u) ↔ u=extend c a b)
variable (separated : ∀ col : Coloring G,∀ c,col.val (black c)≠col.val (gray c))

def realization (col : V → Fin 3) : Vertex (V := V) (W := W) → Fin 3 :=
  Sum.elim col (fun p => extend p.1 (col (black p.1)) (col (gray p.1)) p.2)

theorem realization_local (col : V → Fin 3) (c : C) :
    realization black gray extend col ∘ place black gray c=
      Sum.elim (inputColor (col (black c)) (col (gray c)))
        (extend c (col (black c)) (col (gray c))) := by
  funext v
  rcases v with b | w
  · cases b <;> rfl
  · rfl

include local_spec separated in
theorem realization_proper (col : Coloring G) :
    ∀ e,realization black gray extend col.val ((graph G K black gray).src e)≠
      realization black gray extend col.val ((graph G K black gray).dst e) := by
  rintro (e | ⟨c,e⟩)
  · exact col.property e
  · have h := (local_spec c (col.val (black c)) (col.val (gray c)) (separated col c)
      (extend c (col.val (black c)) (col.val (gray c)))).mpr rfl
    rw [←realization_local black gray extend col.val c] at h
    exact h e

include local_spec separated in
theorem reconstruct (col : Coloring (graph G K black gray)) :
    realization black gray extend (col.val ∘ Sum.inl)=col.val := by
  let base : Coloring G := ⟨col.val ∘ Sum.inl,fun e => col.property (.inl e)⟩
  funext v
  cases v with
  | inl v => rfl
  | inr p =>
    rcases p with ⟨c,w⟩
    have hlocal : localProper K c
        (Sum.elim (inputColor (base.val (black c)) (base.val (gray c)))
          (fun w => col.val (.inr ⟨c,w⟩))) := by
      have he : Sum.elim (inputColor (base.val (black c)) (base.val (gray c)))
          (fun w => col.val (.inr ⟨c,w⟩))=col.val ∘ place black gray c := by
        funext v
        rcases v with b | w
        · cases b <;> rfl
        · rfl
      rw [he]
      exact fun e => col.property (.inr ⟨c,e⟩)
    have hu := (local_spec c _ _ (separated base c) _).mp hlocal
    exact (congrFun hu w).symm

/-- Exact global restriction/extension bijection, retaining ordinary labeled
colors and every original vertex. -/
def coloringEquiv : Coloring (graph G K black gray) ≃ Coloring G where
  toFun col := ⟨col.val ∘ Sum.inl,fun e => col.property (.inl e)⟩
  invFun col := ⟨realization black gray extend col.val,
    realization_proper G K black gray extend local_spec separated col⟩
  left_inv col := Subtype.ext (reconstruct G K black gray extend local_spec separated col)
  right_inv col := rfl

include local_spec separated in
theorem coloring_card [Fintype V] [Fintype E] [Fintype C] [∀ c,Fintype (W c)] [∀ c,Fintype (F c)] :
    ProperColoringPottsReduction.properColoringCount (graph G K black gray) 3=
      ProperColoringPottsReduction.properColoringCount G 3 := by
  rw [properCount_eq_natCard,properCount_eq_natCard]
  exact Nat.card_congr (coloringEquiv G K black gray extend local_spec separated)

end PlanarHom.ColoringUniquePaletteAttachments
