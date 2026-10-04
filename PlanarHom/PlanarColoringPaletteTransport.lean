import PlanarHom.PlanarColoringOneWayDrawing

noncomputable section
namespace PlanarHom.PlanarColoringOneWayConverter

theorem palette_copy (col : Fin 34 → Fin 3) (hp : Proper col) :
    col 2=col 7 ∧ col 4=col 6 ∧ col 7≠col 6 := by
  have hw := ((proper_split col).mp hp).1
  have h0 := (PlanarColoringExclusiveCrossing.proper_iff _).mp (hw 0)
  have h1 := (PlanarColoringExclusiveCrossing.proper_iff _).mp (hw 1)
  have h2 := (PlanarColoringExclusiveCrossing.proper_iff _).mp (hw 2)
  have h63 : col 6=col 3 := congrFun h0.2 3
  have h75 : col 7=col 5 := congrFun h1.2 3
  have h52 : col 5=col 2 := congrFun h2.2 2
  have h34 : col 3=col 4 := congrFun h2.2 3
  have hbg : col 2≠col 4 := h2.1
  exact ⟨(h75.trans h52).symm,(h63.trans h34).symm,by rwa [h75,h52,h63,h34]⟩

end PlanarHom.PlanarColoringOneWayConverter
