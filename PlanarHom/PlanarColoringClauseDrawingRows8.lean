import PlanarHom.PlanarColoringClauseDrawingRows
noncomputable section
namespace PlanarHom.PlanarColoringClause
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000

theorem drawingRow128 : DrawingRow (.inl (1,(.inr (true,(.inl 2))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow129 : DrawingRow (.inl (1,(.inr (true,(.inl 3))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow130 : DrawingRow (.inl (1,(.inr (true,(.inl 4))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow131 : DrawingRow (.inl (1,(.inr (true,(.inl 5))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow132 : DrawingRow (.inl (1,(.inr (true,(.inl 6))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow133 : DrawingRow (.inl (1,(.inr (true,(.inl 7))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow134 : DrawingRow (.inl (1,(.inr (true,(.inr (.inl 0)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow135 : DrawingRow (.inl (1,(.inr (true,(.inr (.inl 1)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow136 : DrawingRow (.inl (1,(.inr (true,(.inr (.inl 2)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow137 : DrawingRow (.inl (1,(.inr (true,(.inr (.inl 3)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow138 : DrawingRow (.inl (1,(.inr (true,(.inr (.inl 4)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow139 : DrawingRow (.inl (1,(.inr (true,(.inr (.inl 5)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow140 : DrawingRow (.inl (1,(.inr (true,(.inr (.inl 6)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow141 : DrawingRow (.inl (1,(.inr (true,(.inr (.inl 7)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow142 : DrawingRow (.inl (1,(.inr (true,(.inr (.inr 0)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow143 : DrawingRow (.inl (1,(.inr (true,(.inr (.inr 1)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

end PlanarHom.PlanarColoringClause
