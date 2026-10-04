import PlanarHom.RadialPottsAssemblyCornerOrder
import PlanarHom.PlaneDrawingMap
import PlanarHom.RadialPottsAssemblyCircleCoordinates

/-! Actual cyclic corner drawings at prescribed finite clockwise chart heights,
translated and scaled to the source drawing's genuine vertex circles. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph HardcoreLogicGadgets

def extendHeight {n : ℕ} (height : Fin n→ℝ) (i : ℕ) : ℝ :=
  if hn : 0<n then
    if hi : i<n then height ⟨i,hi⟩ else height ⟨n-1,by omega⟩-(i-(n-1):ℕ)
  else -(i:ℝ)

@[simp] theorem extendHeight_apply {n : ℕ} (height : Fin n→ℝ) (i : Fin n) :
    extendHeight height i.val=height i := by
  have hn : 0<n := Nat.zero_lt_of_lt i.isLt
  simp [extendHeight,hn,i.isLt]

theorem extendHeight_strictAnti {n : ℕ} (height : Fin n→ℝ) (hanti : StrictAnti height) :
    StrictAnti (extendHeight height) := by
  intro a b hab
  by_cases hn : 0<n
  · by_cases ha : a<n
    · by_cases hb : b<n
      · simp only [extendHeight,dif_pos hn,dif_pos ha,dif_pos hb]
        exact hanti hab
      · simp only [extendHeight,dif_pos hn,dif_pos ha,dif_neg hb]
        have ha' : (⟨a,ha⟩ : Fin n)≤⟨n-1,by omega⟩ := by change a≤n-1; omega
        have hh := hanti.antitone ha'
        have ht : (0:ℝ)<(b-(n-1):ℕ) := by exact_mod_cast (show 0<b-(n-1) by omega)
        linarith
    · have hb : ¬b<n := by omega
      simp only [extendHeight,dif_pos hn,dif_neg ha,dif_neg hb]
      have hh : (a-(n-1):ℕ)<b-(n-1) := by omega
      have hreal : ((a-(n-1):ℕ):ℝ)<(b-(n-1):ℕ) := by exact_mod_cast hh
      linarith
  · simp only [extendHeight,dif_neg hn]
    have hh : (a:ℝ)<b := by exact_mod_cast hab
    linarith

namespace CornerOrder

def finiteDrawing (n k : ℕ) (height : Fin (n*(2*k))→ℝ) (hanti : StrictAnti height) :
    PlaneDrawing (graph n k) :=
  clockwiseDrawing n k (extendHeight height) (extendHeight_strictAnti height hanti)

@[simp] theorem finiteDrawing_point (n k : ℕ) (height : Fin (n*(2*k))→ℝ)
    (hanti : StrictAnti height) (v : Fin n×Fin (2*k)) :
    (finiteDrawing n k height hanti).point v=diskMap (0,height (finProdFinEquiv v)) := by
  change diskMap (0,extendHeight height (finProdFinEquiv v).val)=_
  rw [extendHeight_apply]

end CornerOrder

def placeCircle (p : Plane) (r : ℝ) : C(Plane,Plane) where
  toFun q := p+r • q
  continuous_toFun := by fun_prop

theorem placeCircle_injective (p : Plane) {r : ℝ} (hr : r≠0) :
    Function.Injective (placeCircle p r) := by
  intro a b h
  have hh : r • a=r • b := add_left_cancel h
  exact (smul_right_injective _ hr) hh

namespace CornerOrder

def placedDrawing (n k : ℕ) (height : Fin (n*(2*k))→ℝ) (hanti : StrictAnti height)
    (p : Plane) (r : ℝ) (hr : 0<r) : PlaneDrawing (graph n k) :=
  mapPlaneDrawing (finiteDrawing n k height hanti) (placeCircle p r)
    (placeCircle_injective p (ne_of_gt hr))

@[simp] theorem placedDrawing_point (n k : ℕ) (height : Fin (n*(2*k))→ℝ)
    (hanti : StrictAnti height) (p : Plane) (r : ℝ) (hr : 0<r) (v : Fin n×Fin (2*k)) :
    (placedDrawing n k height hanti p r hr).point v=
      p+r • diskMap (0,height (finProdFinEquiv v)) := by
  change placeCircle p r ((finiteDrawing n k height hanti).point v)=_
  rw [finiteDrawing_point]
  rfl

theorem placedDrawing_interior (n k : ℕ) (height : Fin (n*(2*k))→ℝ)
    (hanti : StrictAnti height) (p : Plane) (r : ℝ) (hr : 0<r)
    (e : Fin n×Fin k) (t : I) (ht : Inside t) :
    rayLength ((placedDrawing n k height hanti p r hr).curve e t-p)<r := by
  let H := extendHeight height
  let F := finiteDrawing n k height hanti
  have hh : H (rank ((graph n k).src e))≠H (rank ((graph n k).dst e)) := by
    apply (extendHeight_strictAnti height hanti).injective.ne
    rcases rank_endpoints e with he | he <;> rw [he.1,he.2]
    · exact ne_of_lt (lo_lt_hi e)
    · exact ne_of_gt (lo_lt_hi e)
  have hinside := diskArch_inside _ _ hh t ht
  have hlen : rayLength (F.curve e t)<1 := by
    have hs := rayLength_sq (F.curve e t)
    have hn := rayLength_nonneg (F.curve e t)
    change (F.curve e t).1^2+(F.curve e t).2^2<1 at hinside
    nlinarith
  change rayLength (p+r • (F.curve e t)-p)<r
  rw [add_sub_cancel_left,rayLength_smul,abs_of_pos hr]
  nlinarith

end CornerOrder
end PlanarHom.RadialPottsAssemblyGeometry
