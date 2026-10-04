import PlanarHom.PlanarColoringClauseDrawingRows
noncomputable section
namespace PlanarHom.PlanarColoringClause
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000

theorem drawingRow64 : DrawingRow (.inl (0,(.inr (true,(.inr (.inl 6)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow65 : DrawingRow (.inl (0,(.inr (true,(.inr (.inl 7)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow66 : DrawingRow (.inl (0,(.inr (true,(.inr (.inr 0)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow67 : DrawingRow (.inl (0,(.inr (true,(.inr (.inr 1)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow68 : DrawingRow (.inl (0,(.inr (true,(.inr (.inr 2)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow69 : DrawingRow (.inl (0,(.inr (true,(.inr (.inr 3)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow70 : DrawingRow (.inl (0,(.inr (true,(.inr (.inr 4)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow71 : DrawingRow (.inl (0,(.inr (true,(.inr (.inr 5)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow72 : DrawingRow (.inl (0,(.inr (true,(.inr (.inr 6)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow73 : DrawingRow (.inl (0,(.inr (true,(.inr (.inr 7)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow74 : DrawingRow (.inl (0,(.inr (true,(.inr (.inr 8)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow75 : DrawingRow (.inl (0,(.inr (true,(.inr (.inr 9)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow76 : DrawingRow (.inl (1,(.inl (0,0)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow77 : DrawingRow (.inl (1,(.inl (0,1)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow78 : DrawingRow (.inl (1,(.inl (0,2)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow79 : DrawingRow (.inl (1,(.inl (0,3)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

end PlanarHom.PlanarColoringClause
