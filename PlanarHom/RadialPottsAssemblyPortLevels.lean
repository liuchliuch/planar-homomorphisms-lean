import PlanarHom.RadialPottsAssemblyUnitSquare
import PlanarHom.RadialPottsAssemblyRowFans

/-! Exact agreement of the drawn tile's terminal positions with the oriented
clockwise finite port rows used for actual circular routing. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open RadialPottsTile MultiGraph

def levelNumerator {k : ℕ} (i : Fin (2*k)) : ℕ := i.val+1+(if k ≤ i.val then 1 else 0)

theorem levelNumerator_bounds {k : ℕ} (i : Fin (2*k)) :
    0<levelNumerator i ∧ levelNumerator i<2*(k+1) := by
  have hi := i.isLt
  unfold levelNumerator
  split_ifs <;> omega

def portLevel {k : ℕ} (i : Fin (2*k)) : I :=
  ⟨(levelNumerator i:ℝ)/(2*((k:ℝ)+1)),by
    have hi := levelNumerator_bounds i
    have hd : (0:ℝ)<2*((k:ℝ)+1) := by positivity
    constructor
    · positivity
    · apply (div_le_one hd).mpr
      exact_mod_cast hi.2.le⟩

theorem portLevel_inside {k : ℕ} (i : Fin (2*k)) : Inside (portLevel i) := by
  have hi := levelNumerator_bounds i
  have hd : (0:ℝ)<2*((k:ℝ)+1) := by positivity
  constructor
  · exact div_pos (by exact_mod_cast hi.1) hd
  · apply (div_lt_one hd).mpr
    exact_mod_cast hi.2

theorem portLevel_strictMono (k : ℕ) : StrictMono (@portLevel k) := by
  intro a b hab
  change (levelNumerator a:ℝ)/(2*((k:ℝ)+1))<(levelNumerator b:ℝ)/(2*((k:ℝ)+1))
  apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
  have hh : levelNumerator a<levelNumerator b := by
    have h : a.val<b.val := hab
    unfold levelNumerator
    split_ifs <;> omega
  exact_mod_cast hh

def portIndex {k : ℕ} (s : Fin 4) (a : Fin k) : Fin (2*k) :=
  if s.val%2=0 then ⟨a.val,by omega⟩ else ⟨k+a.val,by omega⟩

/-- The literal bar terminal, in longitudinal/transverse coordinates. Its
source end reverses exactly the same level order as the true outgoing dart. -/
theorem square_port_level {k : ℕ} (s : Fin 4) (a : Fin k) :
    (squareDrawing k).point (.inr (s,a))=
      (if decide (2≤s.val) then 0 else 1,
        (orientedLevel portLevel (decide (2≤s.val)) (portIndex s a):ℝ)) := by
  rw [square_port_point]
  have ha := a.isLt
  have hk : k≤k+a.val := by omega
  have hn : (k:ℝ)+1≠0 := by positivity
  fin_cases s <;> apply Prod.ext
  all_goals simp [orientedLevel,portIndex,portLevel,levelNumerator,ha.not_ge,hk,
    unitInterval.coe_symm_eq,Nat.cast_add,Nat.cast_one]
  all_goals field_simp <;> ring

end PlanarHom.RadialPottsAssemblyGeometry
