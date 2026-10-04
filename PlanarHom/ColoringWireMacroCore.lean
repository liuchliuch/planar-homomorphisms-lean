import PlanarHom.ColoringNetworkComponentCount
import PlanarHom.RoutingCellDrawings

/-! Concrete connected palette-link tree of the finite wire macro. All links
are literal gadgets and all source occurrences retain their actual variable. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringWireMacroCore
open ColoringPaletteNetwork ParsimoniousNorOneInThree PlanarColoringClause
set_option maxHeartbeats 6000000

def occurrence : Fin 5 → Fin 3 → Fin 7 := ![![3,2,0],![3,1,2],![5,4,3],![4,6,3],![6,4,5]]
def left : Fin 4 → Fin 5 × Fin 3 := ![(0,0),(0,2),(2,2),(2,0)]
def right : Fin 4 → Fin 5 × Fin 3 := ![(1,2),(2,1),(3,1),(4,1)]

def graph := ColoringPaletteNetwork.graph occurrence left right

theorem cover : ∀ v,∃ c k,occurrence c k=v := by decide

theorem component_link (l : Fin 4) :
    component left right (left l).1=component left right (right l).1 := Quot.sound ⟨l,rfl,rfl⟩

theorem component_root (c : Fin 5) : component left right c=component left right 0 := by
  fin_cases c
  · rfl
  · exact (component_link 0).symm
  · exact (component_link 1).symm
  · exact ((component_link 2).symm).trans ((component_link 1).symm)
  · exact ((component_link 3).symm).trans ((component_link 1).symm)

theorem coherent : Coherent occurrence left right := by
  intro c d _ _ _
  exact (component_root c).trans (component_root d).symm

instance : Subsingleton (Component left right) := ⟨by
  intro a b
  induction a using Quot.inductionOn with | h c =>
    induction b using Quot.inductionOn with | h d =>
      exact (component_root c).trans (component_root d).symm⟩

instance : Nonempty (Component left right) := ⟨component left right 0⟩

theorem component_count : Nat.card (Component left right)=1 := Nat.card_unique

theorem clause_order (a : Fin 7 → Bool) (c : Fin 5) :
    ExactlyOne (a (occurrence c 0)) (a (occurrence c 1)) (a (occurrence c 2)) ↔
      ExactlyOne (a (PositiveEqualityDrawing.occurrence c 0)) (a (PositiveEqualityDrawing.occurrence c 1)) (a (PositiveEqualityDrawing.occurrence c 2)) := by
  fin_cases c

  · change ((a 3).toNat+(a 2).toNat+(a 0).toNat=1) ↔ ((a 0).toNat+(a 2).toNat+(a 3).toNat=1)
    omega
  · change ((a 3).toNat+(a 1).toNat+(a 2).toNat=1) ↔ ((a 1).toNat+(a 2).toNat+(a 3).toNat=1)
    omega
  · change ((a 5).toNat+(a 4).toNat+(a 3).toNat=1) ↔ ((a 4).toNat+(a 5).toNat+(a 3).toNat=1)
    omega
  · change ((a 4).toNat+(a 6).toNat+(a 3).toNat=1) ↔ ((a 4).toNat+(a 6).toNat+(a 3).toNat=1)
    omega
  · change ((a 6).toNat+(a 4).toNat+(a 5).toNat=1) ↔ ((a 5).toNat+(a 4).toNat+(a 6).toNat=1)
    omega
theorem source_spec (a : Fin 7 → Bool) :
    (∀ c,ExactlyOne (a (occurrence c 0)) (a (occurrence c 1)) (a (occurrence c 2))) ↔
      Satisfies PositiveEqualityDrawing.formula a := by
  simp only [clause_order]
  rw [PositiveEqualityDrawing.formula]
  simp [Satisfies,PositiveEqualityDrawing.occurrence,List.mem_ofFn,Fin.forall_fin_succ]

theorem coloring_count : ProperColoringPottsReduction.properColoringCount graph 3=
    6*Nat.card (Solutions occurrence) := by
  rw [graph,ColoringPaletteNetwork.component_coloring_count occurrence left right cover coherent,
    component_count,pow_one]

end PlanarHom.ColoringWireMacroCore
