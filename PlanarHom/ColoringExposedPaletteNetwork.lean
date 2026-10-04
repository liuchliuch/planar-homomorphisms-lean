import PlanarHom.ColoringPaletteCopyPatches
import PlanarHom.ColoringNetworkComponentCount

/-! A concrete palette network with independently exposed palette pairs. The
copy shapes may reverse or preserve their physical orientation, and neither
choice changes multiplicity. This is the typed graph behind the numeric macros.
-/
noncomputable section
open Classical
namespace PlanarHom.ColoringExposedPaletteNetwork
open MultiGraph ThreeColorPaletteCounting PlanarColoringClause
open ColoringPaletteNetwork ColoringPalettePairCopy
variable {V C L P : Type}
variable (occurrence : C → Fin 3 → V) (left right : L → Sector (C := C))
variable (shape : P → Shape) (source : P → Sector (C := C))

abbrev Internal (p : P) := (shape p).Internal
abbrev CopyEdge (p : P) := (shape p).Edge
abbrev Vertex := ColoringPaletteNetwork.Vertex V C L ⊕ (p : P) × Internal shape p
abbrev Edge := ColoringPaletteNetwork.Edge C L ⊕ (p : P) × CopyEdge shape p

def blackSource (p : P) : ColoringPaletteNetwork.Vertex V C L := black (source p).1 (source p).2
def graySource (p : P) : ColoringPaletteNetwork.Vertex V C L := gray (source p).1 (source p).2

def graph : MultiGraph (Vertex (V := V) (C := C) (L := L) shape) (Edge (C := C) (L := L) shape) :=
  ColoringUniquePaletteAttachments.graph (ColoringPaletteNetwork.graph occurrence left right)
    (fun p => (shape p).graph) (blackSource source) (graySource source)

def blackInternal (s : Shape) : s.Internal := match s with | .single => (0 : Fin 3) | .double => (0 : Fin 6)
def grayInternal (s : Shape) : s.Internal := match s with | .single => (1 : Fin 3) | .double => (1 : Fin 6)

@[simp] theorem extension_black (s : Shape) (a b : Fin 3) : s.extension a b (blackInternal s)=a := by
  cases s <;> rfl
@[simp] theorem extension_gray (s : Shape) (a b : Fin 3) : s.extension a b (grayInternal s)=b := by
  cases s <;> rfl

def blackPort (p : P) : Vertex (V := V) (C := C) (L := L) shape := .inr ⟨p,blackInternal (shape p)⟩
def grayPort (p : P) : Vertex (V := V) (C := C) (L := L) shape := .inr ⟨p,grayInternal (shape p)⟩
def primary (v : V) : Vertex (V := V) (C := C) (L := L) shape := .inl (.inl v)

theorem copy_spec : ∀ p a b,a≠b → ∀ u,
    ColoringUniquePaletteAttachments.localProper (fun p => (shape p).graph) p
      (Sum.elim (ColoringUniquePaletteAttachments.inputColor a b) u) ↔ u=(shape p).extension a b :=
  fun p a b hab u => (shape p).spec a b hab u

theorem source_separated : ∀ col : Coloring (ColoringPaletteNetwork.graph occurrence left right),∀ p,
    col.val (blackSource source p)≠col.val (graySource source p) :=
  fun col p => palette_separated occurrence left right col.val col.property (source p).1 (source p).2

/-- Restricting a coloring to the original palette network is a bijection. -/
def baseEquiv : Coloring (graph occurrence left right shape source) ≃
    Coloring (ColoringPaletteNetwork.graph occurrence left right) :=
  ColoringUniquePaletteAttachments.coloringEquiv _ _ (blackSource source) (graySource source)
    (fun p => (shape p).extension) (copy_spec shape) (source_separated occurrence left right source)

theorem blackPort_value (col : Coloring (graph occurrence left right shape source)) (p : P) :
    col.val (blackPort shape p)=col.val (.inl (blackSource source p)) := by
  have he := ColoringUniquePaletteAttachments.reconstruct _ _ (blackSource source) (graySource source)
    (fun p => (shape p).extension) (copy_spec shape) (source_separated occurrence left right source) col
  have h := congrFun he (blackPort shape p)
  simpa only [ColoringUniquePaletteAttachments.realization,blackPort,Sum.elim_inr,
    Function.comp_apply,extension_black] using h.symm

theorem grayPort_value (col : Coloring (graph occurrence left right shape source)) (p : P) :
    col.val (grayPort shape p)=col.val (.inl (graySource source p)) := by
  have he := ColoringUniquePaletteAttachments.reconstruct _ _ (blackSource source) (graySource source)
    (fun p => (shape p).extension) (copy_spec shape) (source_separated occurrence left right source) col
  have h := congrFun he (grayPort shape p)
  simpa only [ColoringUniquePaletteAttachments.realization,grayPort,Sum.elim_inr,
    Function.comp_apply,extension_gray] using h.symm

variable (cover : ∀ v,∃ c k,occurrence c k=v)
variable (coherent : Coherent occurrence left right)

def componentEquiv : Coloring (graph occurrence left right shape source) ≃
    (Component left right → Palette) × Solutions occurrence :=
  (baseEquiv occurrence left right shape source).trans
    ((coloringStateEquiv occurrence left right cover).trans
      (componentStateEquiv occurrence left right cover coherent))

theorem componentEquiv_symm_primary (palettes : Component left right → Palette)
    (a : Solutions occurrence) (v : V) :
    ((componentEquiv occurrence left right shape source cover coherent).symm (palettes,a)).val (primary shape v)=
      palettePermutation (palettes (component left right (owner occurrence cover v))) (boolColor (a.val v)) := by
  change statePort ((componentState occurrence left right coherent palettes a).val
    (owner occurrence cover v)) (primaryPort (slot occurrence cover v))=_
  rw [statePort_primary]
  change palettePermutation (palettes (component left right (owner occurrence cover v)))
    (boolColor (a.val (occurrence (owner occurrence cover v) (slot occurrence cover v))))=_
  rw [owner_slot occurrence cover v]

theorem componentEquiv_symm_black (palettes : Component left right → Palette)
    (a : Solutions occurrence) (p : P) :
    ((componentEquiv occurrence left right shape source cover coherent).symm (palettes,a)).val (blackPort shape p)=
      (palettes (component left right (source p).1)).val.1 := by
  change (shape p).extension _ _ (blackInternal (shape p))=_
  rw [extension_black]
  rfl

theorem componentEquiv_symm_gray (palettes : Component left right → Palette)
    (a : Solutions occurrence) (p : P) :
    ((componentEquiv occurrence left right shape source cover coherent).symm (palettes,a)).val (grayPort shape p)=
      (palettes (component left right (source p).1)).val.2 := by
  change (shape p).extension _ _ (grayInternal (shape p))=_
  rw [extension_gray]
  rfl

include cover coherent in
/-- All independent component palettes, all Boolean assignments, and all
orientation-changing copies are included with their exact ordinary multiplicity. -/
theorem coloring_count [Fintype V] [Fintype C] [Fintype L] [Fintype P] :
    ProperColoringPottsReduction.properColoringCount (graph occurrence left right shape source) 3=
      6^Nat.card (Component left right)*Nat.card (Solutions occurrence) := by
  have h := Nat.card_congr (baseEquiv occurrence left right shape source)
  rw [←properCount_eq_natCard,←properCount_eq_natCard] at h
  rw [h]
  exact component_coloring_count occurrence left right cover coherent

end PlanarHom.ColoringExposedPaletteNetwork
