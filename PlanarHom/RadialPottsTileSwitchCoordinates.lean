import PlanarHom.RadialPottsTileCoordinateIndices

/-! NEW exact endpoints of the switched red links, including the innermost
and outermost ring exceptions. -/
namespace PlanarHom.RadialPottsTileCoordinates
open IntegerStraightDrawing RadialPottsTile

def zeroWhite {k : ℕ} (r : Fin k) : White k := ⟨r,0⟩
def oneWhite {k : ℕ} (r : Fin k) : White k := ⟨r,⟨1,by omega⟩⟩

theorem point_zeroWhite {k : ℕ} (r : Fin k) :
    point (.inl (zeroWhite r))=(-(r.val:ℤ),(r.val:ℤ)+1) := by
  have hh := white_point_of_index (zeroWhite r) 0 0 (by simp [zeroWhite]) (by simp [zeroWhite])
  simpa [turn,zeroWhite] using hh

theorem point_oneWhite_at_zero {k : ℕ} (r : Fin k) (hr : r.val=0) :
    point (.inl (oneWhite r))=(1,0) := by
  have hh := white_point_of_index (oneWhite r) 1 0 (by simp [oneWhite]) (by simp [oneWhite,hr])
  simpa [turn,oneWhite,hr] using hh

theorem point_switch_zeroWhite {k : ℕ} (r : Fin k) :
    point (.inl (switch (zeroWhite r)))=
      (-(r.val:ℤ),(r.val:ℤ)+1+(if r.val+1<k then 1 else 0)) := by
  by_cases hr : r.val+1<k
  · have hs : switch (zeroWhite r)=oneWhite ⟨r.val+1,hr⟩ := by
      simp [switch,zeroWhite,oneWhite,hr]
    rw [hs]
    have hh := white_point_of_index (oneWhite ⟨r.val+1,hr⟩) 0 1
      (by simp [oneWhite]) (by simp [oneWhite])
    simpa [turn,oneWhite,hr] using hh
  · have hs : switch (zeroWhite r)=zeroWhite r := by simp [switch,zeroWhite,hr]
    rw [hs,point_zeroWhite]
    simp [hr]

theorem point_switch_oneWhite {k : ℕ} (r : Fin k) :
    point (.inl (switch (oneWhite r)))=(1-(r.val:ℤ),(r.val:ℤ)) := by
  by_cases hr : 0<r.val
  · let p : Fin k := ⟨r.val-1,by have:=r.isLt; omega⟩
    have hs : switch (oneWhite r)=zeroWhite p := by
      simp [switch,oneWhite,zeroWhite,p,hr]
    rw [hs,point_zeroWhite]
    dsimp [p]
    have hc : ((r.val-1:ℕ):ℤ)=(r.val:ℤ)-1 := by omega
    rw [hc]
    congr 1 <;> ring
  · have hr0 : r.val=0 := by omega
    have hs : switch (oneWhite r)=oneWhite r := by simp [switch,oneWhite,hr]
    rw [hs,point_oneWhite_at_zero r hr0]
    simp [hr0]

end PlanarHom.RadialPottsTileCoordinates
