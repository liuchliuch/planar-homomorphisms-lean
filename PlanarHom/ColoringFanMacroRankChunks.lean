import PlanarHom.ColoringFanMacroSpatialData
noncomputable section
namespace PlanarHom.ColoringFanMacroCoordinates
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

private theorem rank_chunk_7 (i : Fin 16) :
    coordinateRank (point ⟨112+i.val,by have := i.isLt; omega⟩)=112+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_8 (i : Fin 16) :
    coordinateRank (point ⟨128+i.val,by have := i.isLt; omega⟩)=128+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_9 (i : Fin 16) :
    coordinateRank (point ⟨144+i.val,by have := i.isLt; omega⟩)=144+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_10 (i : Fin 16) :
    coordinateRank (point ⟨160+i.val,by have := i.isLt; omega⟩)=160+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_11 (i : Fin 16) :
    coordinateRank (point ⟨176+i.val,by have := i.isLt; omega⟩)=176+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_12 (i : Fin 16) :
    coordinateRank (point ⟨192+i.val,by have := i.isLt; omega⟩)=192+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_13 (i : Fin 16) :
    coordinateRank (point ⟨208+i.val,by have := i.isLt; omega⟩)=208+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_14 (i : Fin 16) :
    coordinateRank (point ⟨224+i.val,by have := i.isLt; omega⟩)=224+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_15 (i : Fin 16) :
    coordinateRank (point ⟨240+i.val,by have := i.isLt; omega⟩)=240+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_16 (i : Fin 16) :
    coordinateRank (point ⟨256+i.val,by have := i.isLt; omega⟩)=256+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_17 (i : Fin 16) :
    coordinateRank (point ⟨272+i.val,by have := i.isLt; omega⟩)=272+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_18 (i : Fin 16) :
    coordinateRank (point ⟨288+i.val,by have := i.isLt; omega⟩)=288+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_19 (i : Fin 16) :
    coordinateRank (point ⟨304+i.val,by have := i.isLt; omega⟩)=304+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_20 (i : Fin 16) :
    coordinateRank (point ⟨320+i.val,by have := i.isLt; omega⟩)=320+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_21 (i : Fin 16) :
    coordinateRank (point ⟨336+i.val,by have := i.isLt; omega⟩)=336+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_22 (i : Fin 16) :
    coordinateRank (point ⟨352+i.val,by have := i.isLt; omega⟩)=352+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_23 (i : Fin 16) :
    coordinateRank (point ⟨368+i.val,by have := i.isLt; omega⟩)=368+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_24 (i : Fin 16) :
    coordinateRank (point ⟨384+i.val,by have := i.isLt; omega⟩)=384+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_25 (i : Fin 16) :
    coordinateRank (point ⟨400+i.val,by have := i.isLt; omega⟩)=400+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_26 (i : Fin 16) :
    coordinateRank (point ⟨416+i.val,by have := i.isLt; omega⟩)=416+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_27 (i : Fin 16) :
    coordinateRank (point ⟨432+i.val,by have := i.isLt; omega⟩)=432+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_28 (i : Fin 16) :
    coordinateRank (point ⟨448+i.val,by have := i.isLt; omega⟩)=448+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_29 (i : Fin 16) :
    coordinateRank (point ⟨464+i.val,by have := i.isLt; omega⟩)=464+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_30 (i : Fin 16) :
    coordinateRank (point ⟨480+i.val,by have := i.isLt; omega⟩)=480+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_31 (i : Fin 16) :
    coordinateRank (point ⟨496+i.val,by have := i.isLt; omega⟩)=496+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_32 (i : Fin 16) :
    coordinateRank (point ⟨512+i.val,by have := i.isLt; omega⟩)=512+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_33 (i : Fin 16) :
    coordinateRank (point ⟨528+i.val,by have := i.isLt; omega⟩)=528+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_34 (i : Fin 16) :
    coordinateRank (point ⟨544+i.val,by have := i.isLt; omega⟩)=544+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_35 (i : Fin 16) :
    coordinateRank (point ⟨560+i.val,by have := i.isLt; omega⟩)=560+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_36 (i : Fin 16) :
    coordinateRank (point ⟨576+i.val,by have := i.isLt; omega⟩)=576+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_37 (i : Fin 16) :
    coordinateRank (point ⟨592+i.val,by have := i.isLt; omega⟩)=592+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_38 (i : Fin 16) :
    coordinateRank (point ⟨608+i.val,by have := i.isLt; omega⟩)=608+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_39 (i : Fin 16) :
    coordinateRank (point ⟨624+i.val,by have := i.isLt; omega⟩)=624+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_40 (i : Fin 16) :
    coordinateRank (point ⟨640+i.val,by have := i.isLt; omega⟩)=640+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_41 (i : Fin 16) :
    coordinateRank (point ⟨656+i.val,by have := i.isLt; omega⟩)=656+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_42 (i : Fin 16) :
    coordinateRank (point ⟨672+i.val,by have := i.isLt; omega⟩)=672+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_43 (i : Fin 16) :
    coordinateRank (point ⟨688+i.val,by have := i.isLt; omega⟩)=688+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_44 (i : Fin 16) :
    coordinateRank (point ⟨704+i.val,by have := i.isLt; omega⟩)=704+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_45 (i : Fin 16) :
    coordinateRank (point ⟨720+i.val,by have := i.isLt; omega⟩)=720+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_46 (i : Fin 16) :
    coordinateRank (point ⟨736+i.val,by have := i.isLt; omega⟩)=736+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_47 (i : Fin 16) :
    coordinateRank (point ⟨752+i.val,by have := i.isLt; omega⟩)=752+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_48 (i : Fin 16) :
    coordinateRank (point ⟨768+i.val,by have := i.isLt; omega⟩)=768+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_49 (i : Fin 16) :
    coordinateRank (point ⟨784+i.val,by have := i.isLt; omega⟩)=784+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_50 (i : Fin 16) :
    coordinateRank (point ⟨800+i.val,by have := i.isLt; omega⟩)=800+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_51 (i : Fin 16) :
    coordinateRank (point ⟨816+i.val,by have := i.isLt; omega⟩)=816+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_52 (i : Fin 16) :
    coordinateRank (point ⟨832+i.val,by have := i.isLt; omega⟩)=832+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_53 (i : Fin 16) :
    coordinateRank (point ⟨848+i.val,by have := i.isLt; omega⟩)=848+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_54 (i : Fin 16) :
    coordinateRank (point ⟨864+i.val,by have := i.isLt; omega⟩)=864+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_55 (i : Fin 16) :
    coordinateRank (point ⟨880+i.val,by have := i.isLt; omega⟩)=880+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_56 (i : Fin 16) :
    coordinateRank (point ⟨896+i.val,by have := i.isLt; omega⟩)=896+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_57 (i : Fin 16) :
    coordinateRank (point ⟨912+i.val,by have := i.isLt; omega⟩)=912+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_58 (i : Fin 16) :
    coordinateRank (point ⟨928+i.val,by have := i.isLt; omega⟩)=928+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_59 (i : Fin 16) :
    coordinateRank (point ⟨944+i.val,by have := i.isLt; omega⟩)=944+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_60 (i : Fin 16) :
    coordinateRank (point ⟨960+i.val,by have := i.isLt; omega⟩)=960+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_61 (i : Fin 16) :
    coordinateRank (point ⟨976+i.val,by have := i.isLt; omega⟩)=976+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_62 (i : Fin 16) :
    coordinateRank (point ⟨992+i.val,by have := i.isLt; omega⟩)=992+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_63 (i : Fin 16) :
    coordinateRank (point ⟨1008+i.val,by have := i.isLt; omega⟩)=1008+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_64 (i : Fin 16) :
    coordinateRank (point ⟨1024+i.val,by have := i.isLt; omega⟩)=1024+i.val := by
  fin_cases i <;> rfl

private theorem rank_chunk_65 (i : Fin 14) :
    coordinateRank (point ⟨1040+i.val,by have := i.isLt; omega⟩)=1040+i.val := by
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
  by_cases h7 : v.val<128
  · let i : Fin 16 := ⟨v.val-112,by omega⟩
    have he : (⟨112+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_7 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 112+i.val=v.val at hv
    exact h.trans hv
  by_cases h8 : v.val<144
  · let i : Fin 16 := ⟨v.val-128,by omega⟩
    have he : (⟨128+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_8 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 128+i.val=v.val at hv
    exact h.trans hv
  by_cases h9 : v.val<160
  · let i : Fin 16 := ⟨v.val-144,by omega⟩
    have he : (⟨144+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_9 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 144+i.val=v.val at hv
    exact h.trans hv
  by_cases h10 : v.val<176
  · let i : Fin 16 := ⟨v.val-160,by omega⟩
    have he : (⟨160+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_10 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 160+i.val=v.val at hv
    exact h.trans hv
  by_cases h11 : v.val<192
  · let i : Fin 16 := ⟨v.val-176,by omega⟩
    have he : (⟨176+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_11 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 176+i.val=v.val at hv
    exact h.trans hv
  by_cases h12 : v.val<208
  · let i : Fin 16 := ⟨v.val-192,by omega⟩
    have he : (⟨192+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_12 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 192+i.val=v.val at hv
    exact h.trans hv
  by_cases h13 : v.val<224
  · let i : Fin 16 := ⟨v.val-208,by omega⟩
    have he : (⟨208+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_13 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 208+i.val=v.val at hv
    exact h.trans hv
  by_cases h14 : v.val<240
  · let i : Fin 16 := ⟨v.val-224,by omega⟩
    have he : (⟨224+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_14 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 224+i.val=v.val at hv
    exact h.trans hv
  by_cases h15 : v.val<256
  · let i : Fin 16 := ⟨v.val-240,by omega⟩
    have he : (⟨240+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_15 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 240+i.val=v.val at hv
    exact h.trans hv
  by_cases h16 : v.val<272
  · let i : Fin 16 := ⟨v.val-256,by omega⟩
    have he : (⟨256+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_16 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 256+i.val=v.val at hv
    exact h.trans hv
  by_cases h17 : v.val<288
  · let i : Fin 16 := ⟨v.val-272,by omega⟩
    have he : (⟨272+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_17 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 272+i.val=v.val at hv
    exact h.trans hv
  by_cases h18 : v.val<304
  · let i : Fin 16 := ⟨v.val-288,by omega⟩
    have he : (⟨288+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_18 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 288+i.val=v.val at hv
    exact h.trans hv
  by_cases h19 : v.val<320
  · let i : Fin 16 := ⟨v.val-304,by omega⟩
    have he : (⟨304+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_19 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 304+i.val=v.val at hv
    exact h.trans hv
  by_cases h20 : v.val<336
  · let i : Fin 16 := ⟨v.val-320,by omega⟩
    have he : (⟨320+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_20 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 320+i.val=v.val at hv
    exact h.trans hv
  by_cases h21 : v.val<352
  · let i : Fin 16 := ⟨v.val-336,by omega⟩
    have he : (⟨336+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_21 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 336+i.val=v.val at hv
    exact h.trans hv
  by_cases h22 : v.val<368
  · let i : Fin 16 := ⟨v.val-352,by omega⟩
    have he : (⟨352+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_22 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 352+i.val=v.val at hv
    exact h.trans hv
  by_cases h23 : v.val<384
  · let i : Fin 16 := ⟨v.val-368,by omega⟩
    have he : (⟨368+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_23 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 368+i.val=v.val at hv
    exact h.trans hv
  by_cases h24 : v.val<400
  · let i : Fin 16 := ⟨v.val-384,by omega⟩
    have he : (⟨384+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_24 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 384+i.val=v.val at hv
    exact h.trans hv
  by_cases h25 : v.val<416
  · let i : Fin 16 := ⟨v.val-400,by omega⟩
    have he : (⟨400+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_25 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 400+i.val=v.val at hv
    exact h.trans hv
  by_cases h26 : v.val<432
  · let i : Fin 16 := ⟨v.val-416,by omega⟩
    have he : (⟨416+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_26 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 416+i.val=v.val at hv
    exact h.trans hv
  by_cases h27 : v.val<448
  · let i : Fin 16 := ⟨v.val-432,by omega⟩
    have he : (⟨432+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_27 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 432+i.val=v.val at hv
    exact h.trans hv
  by_cases h28 : v.val<464
  · let i : Fin 16 := ⟨v.val-448,by omega⟩
    have he : (⟨448+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_28 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 448+i.val=v.val at hv
    exact h.trans hv
  by_cases h29 : v.val<480
  · let i : Fin 16 := ⟨v.val-464,by omega⟩
    have he : (⟨464+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_29 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 464+i.val=v.val at hv
    exact h.trans hv
  by_cases h30 : v.val<496
  · let i : Fin 16 := ⟨v.val-480,by omega⟩
    have he : (⟨480+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_30 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 480+i.val=v.val at hv
    exact h.trans hv
  by_cases h31 : v.val<512
  · let i : Fin 16 := ⟨v.val-496,by omega⟩
    have he : (⟨496+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_31 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 496+i.val=v.val at hv
    exact h.trans hv
  by_cases h32 : v.val<528
  · let i : Fin 16 := ⟨v.val-512,by omega⟩
    have he : (⟨512+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_32 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 512+i.val=v.val at hv
    exact h.trans hv
  by_cases h33 : v.val<544
  · let i : Fin 16 := ⟨v.val-528,by omega⟩
    have he : (⟨528+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_33 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 528+i.val=v.val at hv
    exact h.trans hv
  by_cases h34 : v.val<560
  · let i : Fin 16 := ⟨v.val-544,by omega⟩
    have he : (⟨544+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_34 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 544+i.val=v.val at hv
    exact h.trans hv
  by_cases h35 : v.val<576
  · let i : Fin 16 := ⟨v.val-560,by omega⟩
    have he : (⟨560+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_35 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 560+i.val=v.val at hv
    exact h.trans hv
  by_cases h36 : v.val<592
  · let i : Fin 16 := ⟨v.val-576,by omega⟩
    have he : (⟨576+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_36 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 576+i.val=v.val at hv
    exact h.trans hv
  by_cases h37 : v.val<608
  · let i : Fin 16 := ⟨v.val-592,by omega⟩
    have he : (⟨592+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_37 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 592+i.val=v.val at hv
    exact h.trans hv
  by_cases h38 : v.val<624
  · let i : Fin 16 := ⟨v.val-608,by omega⟩
    have he : (⟨608+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_38 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 608+i.val=v.val at hv
    exact h.trans hv
  by_cases h39 : v.val<640
  · let i : Fin 16 := ⟨v.val-624,by omega⟩
    have he : (⟨624+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_39 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 624+i.val=v.val at hv
    exact h.trans hv
  by_cases h40 : v.val<656
  · let i : Fin 16 := ⟨v.val-640,by omega⟩
    have he : (⟨640+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_40 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 640+i.val=v.val at hv
    exact h.trans hv
  by_cases h41 : v.val<672
  · let i : Fin 16 := ⟨v.val-656,by omega⟩
    have he : (⟨656+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_41 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 656+i.val=v.val at hv
    exact h.trans hv
  by_cases h42 : v.val<688
  · let i : Fin 16 := ⟨v.val-672,by omega⟩
    have he : (⟨672+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_42 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 672+i.val=v.val at hv
    exact h.trans hv
  by_cases h43 : v.val<704
  · let i : Fin 16 := ⟨v.val-688,by omega⟩
    have he : (⟨688+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_43 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 688+i.val=v.val at hv
    exact h.trans hv
  by_cases h44 : v.val<720
  · let i : Fin 16 := ⟨v.val-704,by omega⟩
    have he : (⟨704+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_44 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 704+i.val=v.val at hv
    exact h.trans hv
  by_cases h45 : v.val<736
  · let i : Fin 16 := ⟨v.val-720,by omega⟩
    have he : (⟨720+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_45 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 720+i.val=v.val at hv
    exact h.trans hv
  by_cases h46 : v.val<752
  · let i : Fin 16 := ⟨v.val-736,by omega⟩
    have he : (⟨736+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_46 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 736+i.val=v.val at hv
    exact h.trans hv
  by_cases h47 : v.val<768
  · let i : Fin 16 := ⟨v.val-752,by omega⟩
    have he : (⟨752+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_47 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 752+i.val=v.val at hv
    exact h.trans hv
  by_cases h48 : v.val<784
  · let i : Fin 16 := ⟨v.val-768,by omega⟩
    have he : (⟨768+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_48 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 768+i.val=v.val at hv
    exact h.trans hv
  by_cases h49 : v.val<800
  · let i : Fin 16 := ⟨v.val-784,by omega⟩
    have he : (⟨784+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_49 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 784+i.val=v.val at hv
    exact h.trans hv
  by_cases h50 : v.val<816
  · let i : Fin 16 := ⟨v.val-800,by omega⟩
    have he : (⟨800+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_50 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 800+i.val=v.val at hv
    exact h.trans hv
  by_cases h51 : v.val<832
  · let i : Fin 16 := ⟨v.val-816,by omega⟩
    have he : (⟨816+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_51 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 816+i.val=v.val at hv
    exact h.trans hv
  by_cases h52 : v.val<848
  · let i : Fin 16 := ⟨v.val-832,by omega⟩
    have he : (⟨832+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_52 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 832+i.val=v.val at hv
    exact h.trans hv
  by_cases h53 : v.val<864
  · let i : Fin 16 := ⟨v.val-848,by omega⟩
    have he : (⟨848+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_53 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 848+i.val=v.val at hv
    exact h.trans hv
  by_cases h54 : v.val<880
  · let i : Fin 16 := ⟨v.val-864,by omega⟩
    have he : (⟨864+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_54 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 864+i.val=v.val at hv
    exact h.trans hv
  by_cases h55 : v.val<896
  · let i : Fin 16 := ⟨v.val-880,by omega⟩
    have he : (⟨880+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_55 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 880+i.val=v.val at hv
    exact h.trans hv
  by_cases h56 : v.val<912
  · let i : Fin 16 := ⟨v.val-896,by omega⟩
    have he : (⟨896+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_56 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 896+i.val=v.val at hv
    exact h.trans hv
  by_cases h57 : v.val<928
  · let i : Fin 16 := ⟨v.val-912,by omega⟩
    have he : (⟨912+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_57 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 912+i.val=v.val at hv
    exact h.trans hv
  by_cases h58 : v.val<944
  · let i : Fin 16 := ⟨v.val-928,by omega⟩
    have he : (⟨928+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_58 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 928+i.val=v.val at hv
    exact h.trans hv
  by_cases h59 : v.val<960
  · let i : Fin 16 := ⟨v.val-944,by omega⟩
    have he : (⟨944+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_59 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 944+i.val=v.val at hv
    exact h.trans hv
  by_cases h60 : v.val<976
  · let i : Fin 16 := ⟨v.val-960,by omega⟩
    have he : (⟨960+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_60 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 960+i.val=v.val at hv
    exact h.trans hv
  by_cases h61 : v.val<992
  · let i : Fin 16 := ⟨v.val-976,by omega⟩
    have he : (⟨976+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_61 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 976+i.val=v.val at hv
    exact h.trans hv
  by_cases h62 : v.val<1008
  · let i : Fin 16 := ⟨v.val-992,by omega⟩
    have he : (⟨992+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_62 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 992+i.val=v.val at hv
    exact h.trans hv
  by_cases h63 : v.val<1024
  · let i : Fin 16 := ⟨v.val-1008,by omega⟩
    have he : (⟨1008+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_63 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 1008+i.val=v.val at hv
    exact h.trans hv
  by_cases h64 : v.val<1040
  · let i : Fin 16 := ⟨v.val-1024,by omega⟩
    have he : (⟨1024+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
      apply Fin.ext
      dsimp [i]
      omega
    have h := rank_chunk_64 i
    rw [he] at h
    have hv := congrArg Fin.val he
    change 1024+i.val=v.val at hv
    exact h.trans hv
  have hlast : v.val<1054 := v.isLt
  let i : Fin 14 := ⟨v.val-1040,by omega⟩
  have he : (⟨1040+i.val,by have := i.isLt; omega⟩ : Vertex)=v := by
    apply Fin.ext
    dsimp [i]
    omega
  have h := rank_chunk_65 i
  rw [he] at h
  have hv := congrArg Fin.val he
  change 1040+i.val=v.val at hv
  exact h.trans hv
end PlanarHom.ColoringFanMacroCoordinates
