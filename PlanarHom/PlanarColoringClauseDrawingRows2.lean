import PlanarHom.PlanarColoringClauseDrawingRows
noncomputable section
namespace PlanarHom.PlanarColoringClause
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000

theorem drawingRow32 : DrawingRow (.inl (0,(.inr (false,(.inr (.inl 0)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow33 : DrawingRow (.inl (0,(.inr (false,(.inr (.inl 1)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow34 : DrawingRow (.inl (0,(.inr (false,(.inr (.inl 2)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow35 : DrawingRow (.inl (0,(.inr (false,(.inr (.inl 3)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow36 : DrawingRow (.inl (0,(.inr (false,(.inr (.inl 4)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow37 : DrawingRow (.inl (0,(.inr (false,(.inr (.inl 5)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow38 : DrawingRow (.inl (0,(.inr (false,(.inr (.inl 6)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow39 : DrawingRow (.inl (0,(.inr (false,(.inr (.inl 7)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow40 : DrawingRow (.inl (0,(.inr (false,(.inr (.inr 0)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow41 : DrawingRow (.inl (0,(.inr (false,(.inr (.inr 1)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow42 : DrawingRow (.inl (0,(.inr (false,(.inr (.inr 2)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow43 : DrawingRow (.inl (0,(.inr (false,(.inr (.inr 3)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow44 : DrawingRow (.inl (0,(.inr (false,(.inr (.inr 4)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow45 : DrawingRow (.inl (0,(.inr (false,(.inr (.inr 5)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow46 : DrawingRow (.inl (0,(.inr (false,(.inr (.inr 6)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow47 : DrawingRow (.inl (0,(.inr (false,(.inr (.inr 7)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

end PlanarHom.PlanarColoringClause
