import PlanarHom.PlanarColoringClauseDrawingRows
noncomputable section
namespace PlanarHom.PlanarColoringClause
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000

theorem drawingRow16 : DrawingRow (.inl (0,(.inl (2,0)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow17 : DrawingRow (.inl (0,(.inl (2,1)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow18 : DrawingRow (.inl (0,(.inl (2,2)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow19 : DrawingRow (.inl (0,(.inl (2,3)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow20 : DrawingRow (.inl (0,(.inl (2,4)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow21 : DrawingRow (.inl (0,(.inl (2,5)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow22 : DrawingRow (.inl (0,(.inl (2,6)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow23 : DrawingRow (.inl (0,(.inl (2,7)))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow24 : DrawingRow (.inl (0,(.inr (false,(.inl 0))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow25 : DrawingRow (.inl (0,(.inr (false,(.inl 1))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow26 : DrawingRow (.inl (0,(.inr (false,(.inl 2))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow27 : DrawingRow (.inl (0,(.inr (false,(.inl 3))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow28 : DrawingRow (.inl (0,(.inr (false,(.inl 4))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow29 : DrawingRow (.inl (0,(.inr (false,(.inl 5))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow30 : DrawingRow (.inl (0,(.inr (false,(.inl 6))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem drawingRow31 : DrawingRow (.inl (0,(.inr (false,(.inl 7))))) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

end PlanarHom.PlanarColoringClause
