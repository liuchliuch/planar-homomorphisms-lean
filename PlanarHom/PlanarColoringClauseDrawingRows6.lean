import PlanarHom.PlanarColoringClauseDrawingRows
noncomputable section
namespace PlanarHom.PlanarColoringClause
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000

theorem drawingRow96 : DrawingRow (.inl (1,(.inl (2,4)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow97 : DrawingRow (.inl (1,(.inl (2,5)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow98 : DrawingRow (.inl (1,(.inl (2,6)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow99 : DrawingRow (.inl (1,(.inl (2,7)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow100 : DrawingRow (.inl (1,(.inr (false,(.inl 0))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow101 : DrawingRow (.inl (1,(.inr (false,(.inl 1))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow102 : DrawingRow (.inl (1,(.inr (false,(.inl 2))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow103 : DrawingRow (.inl (1,(.inr (false,(.inl 3))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow104 : DrawingRow (.inl (1,(.inr (false,(.inl 4))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow105 : DrawingRow (.inl (1,(.inr (false,(.inl 5))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow106 : DrawingRow (.inl (1,(.inr (false,(.inl 6))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow107 : DrawingRow (.inl (1,(.inr (false,(.inl 7))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow108 : DrawingRow (.inl (1,(.inr (false,(.inr (.inl 0)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow109 : DrawingRow (.inl (1,(.inr (false,(.inr (.inl 1)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow110 : DrawingRow (.inl (1,(.inr (false,(.inr (.inl 2)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow111 : DrawingRow (.inl (1,(.inr (false,(.inr (.inl 3)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

end PlanarHom.PlanarColoringClause
