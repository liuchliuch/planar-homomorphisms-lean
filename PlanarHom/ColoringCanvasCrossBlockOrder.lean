import PlanarHom.ColoringMacroPortRays

noncomputable section
namespace PlanarHom
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram

namespace PortPatchAssembly
variable {C B : Type} {P W : C → Type} (port : ∀c,P c→B)

theorem shared_ports_of_distinct {c d : C} (hcd : c≠d) (u : P c ⊕ W c) (v : P d ⊕ W d)
    (h : placeVertex port c u=placeVertex port d v) :
    ∃p q,u=.inl p ∧ v=.inl q ∧ port c p=port d q := by
  cases u with
  | inl p =>
    cases v with
    | inl q => exact ⟨p,q,rfl,rfl,Sum.inl.inj h⟩
    | inr q => cases h
  | inr p =>
    cases v with
    | inl q => cases h
    | inr q => exact False.elim (hcd (congrArg Sigma.fst (Sum.inr.inj h)))

end PortPatchAssembly
namespace ColoringEmitter.Canvas
open RadialPottsAssemblyGeometry ParsimoniousNorOneInThree

theorem cross_block_clockwise (f : NumericFormula) (i j : Index f) (hji : j < i)
    (a : Dart (PatchEdge f i)) (b : Dart (PatchEdge f j))
    (hshare : PortPatchAssembly.placeVertex (port f) i ((patch f i).dartPair a).1=
      PortPatchAssembly.placeVertex (port f) j ((patch f j).dartPair b).1) :
    ClockwiseRayOrder (MacroGeometry.ray (canvasCell f i).shape a)
      (MacroGeometry.ray (canvasCell f j).shape b) := by
  obtain ⟨p,q,hp,hq,hpq⟩:=PortPatchAssembly.shared_ports_of_distinct (port f) (ne_of_gt hji) _ _ hshare
  have hs : boundaryPort f j q.1=boundaryPort f i p.1 :=
    (congrArg (fun x : BoundaryTriple f=>x.1) hpq).symm
  have ho:=canvas_shared_port_order f j i hji q.1 p.1 hs
  have hleft : ((MacroGeometry.originCell (canvasCell f i).shape).portData p.1).2.1=0 := by
    have hx:=MacroGeometry.port_column_offset (canvasCell f i) p.1
    omega
  have hright : ((MacroGeometry.originCell (canvasCell f j).shape).portData q.1).2.1=1 := by
    have hx:=MacroGeometry.port_column_offset (canvasCell f j) q.1
    omega
  exact Or.inr ⟨MacroGeometry.ray_left_port _ a p
    (MacroGeometry.numeric_host_of_patch_port _ a p hp) hleft,
    MacroGeometry.ray_right_port _ b q (MacroGeometry.numeric_host_of_patch_port _ b q hq) hright⟩

end ColoringEmitter.Canvas
end PlanarHom
