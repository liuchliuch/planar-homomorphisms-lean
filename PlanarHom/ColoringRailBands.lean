import PlanarHom.RoutingCellSeparation

/-! Expanded, possibly sheared rail bands for three-color macro ports. Primary
signal positions stay on the original grid; the two palette ports sit just above
each primary. The expanded bands have genuine positive-width gaps on both ends,
including the fanout followed by downward-sloping passive wires. -/
noncomputable section
open Set
namespace PlanarHom.PositiveBlockProgram
open MultiGraph

def CellShape.leftLo : CellShape → ℕ
  | .wireBottom => 1
  | _ => 0

def CellShape.leftHi : CellShape → ℕ
  | .wireBottom | .cross => 1
  | .test => 2
  | _ => 0

def CellShape.rightLo : CellShape → ℕ
  | .wireBottom | .wireDown => 1
  | _ => 0

def CellShape.rightHi : CellShape → ℕ
  | .wireBottom | .wireDown | .cross | .fan => 1
  | .test => 2
  | _ => 0

def Cell.ColorBandBefore (a b : Cell) : Prop :=
  a.column<b.column ∨ a.column=b.column ∧
    a.row+a.shape.leftHi<b.row+b.shape.leftLo ∧
    a.row+a.shape.rightHi<b.row+b.shape.rightLo

/-- Row-coordinate band at horizontal fraction t. Coordinates are normalized;
actual macro drawings are scaled by a fixed common positive integer. -/
def Cell.colorBand (c : Cell) : Set Plane := {p |
  (c.column:ℝ)<p.1 ∧ p.1<(c.column:ℝ)+1 ∧
  (c.row:ℝ)+(1-(p.1-c.column))*c.shape.leftLo+(p.1-c.column)*c.shape.rightLo-1/4 < -p.2 ∧
  -p.2 < (c.row:ℝ)+(1-(p.1-c.column))*c.shape.leftHi+(p.1-c.column)*c.shape.rightHi+1/4}

/-- Both endpoint rail ranges being separated by an integer step gives a
uniform half-row gap throughout the affine band, not just at its boundary. -/
theorem Cell.ColorBandBefore.disjoint {a b : Cell} (h : a.ColorBandBefore b) :
    Disjoint a.colorBand b.colorBand := by
  apply Set.disjoint_left.mpr
  intro p ha hb
  rcases ha with ⟨hax0,hax1,hay0,hay1⟩
  rcases hb with ⟨hbx0,hbx1,hby0,hby1⟩
  rcases h with h | ⟨hc,hl,hr⟩
  · have hn : a.column+1≤b.column := by omega
    have hn' : (a.column:ℝ)+1≤b.column := by exact_mod_cast hn
    linarith
  · have hl' : (a.row:ℝ)+a.shape.leftHi+1≤(b.row:ℝ)+b.shape.leftLo := by exact_mod_cast hl
    have hr' : (a.row:ℝ)+a.shape.rightHi+1≤(b.row:ℝ)+b.shape.rightLo := by exact_mod_cast hr
    have hcol : (a.column:ℝ)=b.column := by exact_mod_cast hc
    rw [←hcol] at hby0
    have ht0 : 0<p.1-a.column := by linarith
    have ht1 : 0<1-(p.1-a.column) := by linarith
    have hleft := mul_nonneg ht1.le (sub_nonneg.mpr hl')
    have hright := mul_nonneg ht0.le (sub_nonneg.mpr hr')
    nlinarith

def colorBoundaryPoint (position : ℕ × ℕ) (channel : Fin 3) : Plane :=
  ((position.1:ℝ),-(position.2:ℝ)+(channel.val:ℝ)/16)

theorem colorBoundaryPoint_injective : Function.Injective
    (fun p : (ℕ × ℕ) × Fin 3 => colorBoundaryPoint p.1 p.2) := by
  rintro ⟨⟨c,r⟩,k⟩ ⟨⟨d,s⟩,j⟩ he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp [colorBoundaryPoint] at hx hy
  have hc : c=d := by exact_mod_cast hx
  have hk := k.isLt
  have hj := j.isLt
  have hki : (k.val:ℝ)<3 := by exact_mod_cast hk
  have hji : (j.val:ℝ)<3 := by exact_mod_cast hj
  have hkn : (0:ℝ)≤k.val := by positivity
  have hjn : (0:ℝ)≤j.val := by positivity
  have hrs : r<s+1 := by exact_mod_cast (show (r:ℝ)<(s:ℝ)+1 by nlinarith)
  have hsr : s<r+1 := by exact_mod_cast (show (s:ℝ)<(r:ℝ)+1 by nlinarith)
  have hr : r=s := by omega
  subst s
  have hkj : (k.val:ℝ)=j.val := by linarith
  have hk' : k=j := Fin.ext (by exact_mod_cast hkj)
  subst d
  subst j
  rfl

theorem colorBoundaryPoint_outside (c : Cell) (pos : ℕ × ℕ) (channel : Fin 3) :
    colorBoundaryPoint pos channel∉c.colorBand := by
  rintro ⟨hx0,hx1,_⟩
  dsimp [colorBoundaryPoint] at hx0 hx1
  have hlo : c.column<pos.1 := by exact_mod_cast hx0
  have hhi : pos.1<c.column+1 := by exact_mod_cast hx1
  omega

end PlanarHom.PositiveBlockProgram
