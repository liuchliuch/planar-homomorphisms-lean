import PlanarHom.RotationDartRelabel
import PlanarHom.FisherPipelineValidity

/-! NEW finite rotation transport through the concrete numeric incidence
bijections. Both endpoint bits are retained unchanged. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph.IncidenceEquiv
open Kasteleyn PlanarityLRRealization
variable {V E W F : Type*} {G : MultiGraph V E} {H : MultiGraph W F}

 def dartRelabel (i : IncidenceEquiv G H) : DartRelabel G H where
  vertex:=i.vertex
  dart:=Equiv.prodCongr i.edge (Equiv.refl Bool)
  reverse a:=rfl
  host a:=by
    rcases a with ⟨e,b⟩
    cases b
    · exact i.dst_eq e
    · exact i.src_eq e

end PlanarHom.MultiGraph.IncidenceEquiv

namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} {G : MultiGraph V E}

/-- Preserve literal rows while reconciling equivalent equality deciders from
independently reconstructed generic and numeric source modules. -/
def redecidable {sourceDec : DecidableEq (Dart E)} [targetDec : DecidableEq (Dart E)]
    (R : @RotationRows V E G sourceDec) : RotationRows G where
  row:=@RotationRows.row V E G sourceDec R
  nodup:=@RotationRows.nodup V E G sourceDec R
  mem:=@RotationRows.mem V E G sourceDec R

@[simp] theorem redecidable_row {sourceDec : DecidableEq (Dart E)} [targetDec : DecidableEq (Dart E)]
    (R : @RotationRows V E G sourceDec) (v : V) :
    (redecidable R).row v=@RotationRows.row V E G sourceDec R v := rfl

theorem redecidable_rotation {sourceDec : DecidableEq (Dart E)} [targetDec : DecidableEq (Dart E)]
    (R : @RotationRows V E G sourceDec) :
    (redecidable R).rotation=@RotationRows.rotation V E G sourceDec R := by
  have h:sourceDec=targetDec:=Subsingleton.elim _ _
  subst targetDec
  rfl

theorem redecidable_facePerm [Fintype V] [Fintype E]
    {sourceDec : DecidableEq (Dart E)} [targetDec : DecidableEq (Dart E)]
    (R : @RotationRows V E G sourceDec) :
    (redecidable R).facePerm=@RotationRows.facePerm V E sourceDec G R := by
  have h:sourceDec=targetDec:=Subsingleton.elim _ _
  subst targetDec
  rfl

end PlanarHom.PlanarityLRRealization.RotationRows
