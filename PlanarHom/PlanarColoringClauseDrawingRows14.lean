import PlanarHom.PlanarColoringClauseDrawingRows
noncomputable section
namespace PlanarHom.PlanarColoringClause
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000

theorem drawingRow224 : DrawingRow (.inl (2,(.inr (true,(.inr (.inr 6)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow225 : DrawingRow (.inl (2,(.inr (true,(.inr (.inr 7)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow226 : DrawingRow (.inl (2,(.inr (true,(.inr (.inr 8)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow227 : DrawingRow (.inl (2,(.inr (true,(.inr (.inr 9)))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow228 : DrawingRow (.inr (.inl (0,0))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow229 : DrawingRow (.inr (.inl (0,1))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow230 : DrawingRow (.inr (.inl (0,2))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow231 : DrawingRow (.inr (.inl (0,3))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow232 : DrawingRow (.inr (.inl (0,4))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow233 : DrawingRow (.inr (.inl (0,5))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow234 : DrawingRow (.inr (.inl (0,6))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow235 : DrawingRow (.inr (.inl (1,0))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow236 : DrawingRow (.inr (.inl (1,1))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow237 : DrawingRow (.inr (.inl (1,2))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow238 : DrawingRow (.inr (.inl (1,3))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow239 : DrawingRow (.inr (.inl (1,4))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

end PlanarHom.PlanarColoringClause
