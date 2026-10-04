import PlanarHom.ColoringTestMacroSpatialData
noncomputable section
namespace PlanarHom.ColoringTestMacroCoordinates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem rank_chunk_0 (i : Fin 16) :
    coordinateRank (point ⟨0+i.val,by have := i.isLt; omega⟩)=0+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_1 (i : Fin 16) :
    coordinateRank (point ⟨16+i.val,by have := i.isLt; omega⟩)=16+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_2 (i : Fin 16) :
    coordinateRank (point ⟨32+i.val,by have := i.isLt; omega⟩)=32+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_3 (i : Fin 16) :
    coordinateRank (point ⟨48+i.val,by have := i.isLt; omega⟩)=48+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_4 (i : Fin 16) :
    coordinateRank (point ⟨64+i.val,by have := i.isLt; omega⟩)=64+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_5 (i : Fin 16) :
    coordinateRank (point ⟨80+i.val,by have := i.isLt; omega⟩)=80+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_6 (i : Fin 16) :
    coordinateRank (point ⟨96+i.val,by have := i.isLt; omega⟩)=96+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_7 (i : Fin 2) :
    coordinateRank (point ⟨112+i.val,by have := i.isLt; omega⟩)=112+i.val := by
  fin_cases i <;> rfl

theorem rank_point (v : Vertex) : coordinateRank (point v)=v.val := by
  by_cases h0 : v.val<16
  · let i : Fin 16 := ⟨v.val-0,by omega⟩
    have he : (⟨0+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_0 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 0+i.val=v.val at hv
    exact h.trans hv
  by_cases h1 : v.val<32
  · let i : Fin 16 := ⟨v.val-16,by omega⟩
    have he : (⟨16+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_1 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 16+i.val=v.val at hv
    exact h.trans hv
  by_cases h2 : v.val<48
  · let i : Fin 16 := ⟨v.val-32,by omega⟩
    have he : (⟨32+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_2 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 32+i.val=v.val at hv
    exact h.trans hv
  by_cases h3 : v.val<64
  · let i : Fin 16 := ⟨v.val-48,by omega⟩
    have he : (⟨48+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_3 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 48+i.val=v.val at hv
    exact h.trans hv
  by_cases h4 : v.val<80
  · let i : Fin 16 := ⟨v.val-64,by omega⟩
    have he : (⟨64+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_4 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 64+i.val=v.val at hv
    exact h.trans hv
  by_cases h5 : v.val<96
  · let i : Fin 16 := ⟨v.val-80,by omega⟩
    have he : (⟨80+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_5 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 80+i.val=v.val at hv
    exact h.trans hv
  by_cases h6 : v.val<112
  · let i : Fin 16 := ⟨v.val-96,by omega⟩
    have he : (⟨96+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_6 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 96+i.val=v.val at hv
    exact h.trans hv
  have hlast : v.val<114 := v.isLt
  let i : Fin 2 := ⟨v.val-112,by omega⟩
  have he : (⟨112+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
    apply Fin.ext
    dsimp [i]
    omega
  have h := rank_chunk_7 i
  rw [he] at h
  have hv := congrArg Fin.val he
  change 112+i.val=v.val at hv
  exact h.trans hv
end PlanarHom.ColoringTestMacroCoordinates
