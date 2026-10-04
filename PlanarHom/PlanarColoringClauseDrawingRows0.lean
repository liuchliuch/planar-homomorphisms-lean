import PlanarHom.PlanarColoringClauseDrawingRows
noncomputable section
namespace PlanarHom.PlanarColoringClause
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000

theorem drawingRow0 : DrawingRow (.inl (0,(.inl (0,0)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow1 : DrawingRow (.inl (0,(.inl (0,1)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow2 : DrawingRow (.inl (0,(.inl (0,2)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow3 : DrawingRow (.inl (0,(.inl (0,3)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow4 : DrawingRow (.inl (0,(.inl (0,4)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow5 : DrawingRow (.inl (0,(.inl (0,5)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow6 : DrawingRow (.inl (0,(.inl (0,6)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow7 : DrawingRow (.inl (0,(.inl (0,7)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow8 : DrawingRow (.inl (0,(.inl (1,0)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow9 : DrawingRow (.inl (0,(.inl (1,1)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow10 : DrawingRow (.inl (0,(.inl (1,2)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow11 : DrawingRow (.inl (0,(.inl (1,3)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow12 : DrawingRow (.inl (0,(.inl (1,4)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow13 : DrawingRow (.inl (0,(.inl (1,5)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow14 : DrawingRow (.inl (0,(.inl (1,6)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow15 : DrawingRow (.inl (0,(.inl (1,7)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

end PlanarHom.PlanarColoringClause
