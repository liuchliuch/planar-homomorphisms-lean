import PlanarHom.PlanarStretch
import PlanarHom.PlanarTransport

/-! Stretch one part of an explicit occurrence partition and retain the other
part as single edges. This construction handles input loops directly. -/

noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph

def partitionLeft {V E A B : Type*} (G : MultiGraph V E) (split : A ⊕ B ≃ E) :
    MultiGraph V A := ⟨fun a => G.src (split (.inl a)), fun a => G.dst (split (.inl a))⟩

/-- The selected occurrences receive private internal vertices; the companion
occurrences keep their original endpoints and occurrence identities. -/
def selectedStretch {V E A B : Type*} (G : MultiGraph V E) (split : A ⊕ B ≃ E) (n : ℕ) :
    MultiGraph (V ⊕ (A × Fin n)) ((A × Fin (n+1)) ⊕ B) where
  src := Sum.elim ((G.partitionLeft split).stretchSrc n) (fun b => .inl (G.src (split (.inr b))))
  dst := Sum.elim ((G.partitionLeft split).stretchDst n) (fun b => .inl (G.dst (split (.inr b))))

namespace PlaneDrawing
variable {V E A B : Type*} {G : MultiGraph V E}

def partitionLeft (d : PlaneDrawing G) (split : A ⊕ B ≃ E) : PlaneDrawing (G.partitionLeft split) where
  point := d.point
  point_injective := d.point_injective
  curve a := d.curve (split (.inl a))
  curve_zero a := d.curve_zero _
  curve_one a := d.curve_one _
  interior_injective a b s t hs ht h := by
    obtain ⟨he,hst⟩ := d.interior_injective _ _ s t hs ht h
    exact ⟨Sum.inl.inj (split.injective he),hst⟩
  interior_avoids a t ht v := d.interior_avoids _ t ht v

/-- Selected path segments use affine restrictions of the same original
curves; companion curves are retained literally. -/
def selectedStretch (d : PlaneDrawing G) (split : A ⊕ B ≃ E) (n : ℕ) :
    PlaneDrawing (G.selectedStretch split n) where
  point := (d.partitionLeft split).stretchPoint n
  point_injective := ((d.partitionLeft split).stretch n).point_injective
  curve := Sum.elim ((d.partitionLeft split).stretch n).curve (fun b => d.curve (split (.inr b)))
  curve_zero e := by
    cases e with
    | inl p => exact ((d.partitionLeft split).stretch n).curve_zero p
    | inr b => exact d.curve_zero _
  curve_one e := by
    cases e with
    | inl p => exact ((d.partitionLeft split).stretch n).curve_one p
    | inr b => exact d.curve_one _
  interior_injective := by
    intro e f s t hs ht h
    cases e with
    | inl p =>
      cases f with
      | inl q =>
        obtain ⟨he,hst⟩ := ((d.partitionLeft split).stretch n).interior_injective p q s t hs ht h
        exact ⟨congrArg Sum.inl he,hst⟩
      | inr b =>
        have he := (d.interior_injective (split (.inl p.1)) (split (.inr b))
          (segmentParameter n p.2 s) t (segmentParameter_inside p.2 hs) ht h).1
        exact False.elim (Sum.noConfusion (split.injective he))
    | inr a =>
      cases f with
      | inl q =>
        have he := (d.interior_injective (split (.inr a)) (split (.inl q.1))
          s (segmentParameter n q.2 t) hs (segmentParameter_inside q.2 ht) h).1
        exact False.elim (Sum.noConfusion (split.injective he))
      | inr b =>
        obtain ⟨he,hst⟩ := d.interior_injective _ _ s t hs ht h
        exact ⟨congrArg Sum.inr (Sum.inr.inj (split.injective he)),hst⟩
  interior_avoids := by
    intro e t ht v h
    cases e with
    | inl p => exact ((d.partitionLeft split).stretch n).interior_avoids p t ht v h
    | inr b =>
      cases v with
      | inl a => exact d.interior_avoids _ t ht a h
      | inr p =>
        have he := (d.interior_injective (split (.inr b)) (split (.inl p.1))
          t (knot p.2) ht (knot_inside p.2) h).1
        exact Sum.noConfusion (split.injective he)

end PlaneDrawing

theorem Planar.selectedStretch {V E A B : Type*} {G : MultiGraph V E}
    (h : G.Planar) (split : A ⊕ B ≃ E) (n : ℕ) : (G.selectedStretch split n).Planar :=
  h.map (fun d => d.selectedStretch split n)

end PlanarHom.MultiGraph
