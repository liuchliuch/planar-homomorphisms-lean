import PlanarHom.PlanarColoringClauseDrawingRows
noncomputable section
namespace PlanarHom.PlanarColoringClause
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000

theorem drawingRow112 : DrawingRow (.inl (1,(.inr (false,(.inr (.inl 4)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow113 : DrawingRow (.inl (1,(.inr (false,(.inr (.inl 5)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow114 : DrawingRow (.inl (1,(.inr (false,(.inr (.inl 6)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow115 : DrawingRow (.inl (1,(.inr (false,(.inr (.inl 7)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow116 : DrawingRow (.inl (1,(.inr (false,(.inr (.inr 0)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow117 : DrawingRow (.inl (1,(.inr (false,(.inr (.inr 1)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow118 : DrawingRow (.inl (1,(.inr (false,(.inr (.inr 2)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow119 : DrawingRow (.inl (1,(.inr (false,(.inr (.inr 3)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow120 : DrawingRow (.inl (1,(.inr (false,(.inr (.inr 4)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow121 : DrawingRow (.inl (1,(.inr (false,(.inr (.inr 5)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow122 : DrawingRow (.inl (1,(.inr (false,(.inr (.inr 6)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow123 : DrawingRow (.inl (1,(.inr (false,(.inr (.inr 7)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow124 : DrawingRow (.inl (1,(.inr (false,(.inr (.inr 8)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow125 : DrawingRow (.inl (1,(.inr (false,(.inr (.inr 9)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow126 : DrawingRow (.inl (1,(.inr (true,(.inl 0))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow127 : DrawingRow (.inl (1,(.inr (true,(.inl 1))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

end PlanarHom.PlanarColoringClause
