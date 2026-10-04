import PlanarHom.ColoringNetworkComponentCount
import PlanarHom.RoutingCellDrawings

/-! Concrete connected palette-link tree of the finite cross macro. All links
are literal gadgets and all source occurrences retain their actual variable. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringCrossMacroCore
open ColoringPaletteNetwork ParsimoniousNorOneInThree PlanarColoringClause
set_option maxHeartbeats 6000000

def occurrence : Fin 12 → Fin 3 → Fin 17 := ![![5,6,0],![1,7,5],![7,4,6],![1,8,9],![8,2,10],![9,10,4],![2,11,12],![13,11,3],![4,12,13],![14,15,3],![16,14,0],![4,15,16]]
def left : Fin 11 → Fin 12 × Fin 3 := ![(0,0),(0,1),(1,0),(2,0),(3,1),(4,1),(5,1),(6,1),(7,2),(8,2),(9,0)]
def right : Fin 11 → Fin 12 × Fin 3 := ![(1,1),(2,1),(3,2),(5,2),(4,2),(6,2),(8,0),(7,0),(9,1),(11,0),(10,0)]

def graph := ColoringPaletteNetwork.graph occurrence left right

theorem cover : ∀ v,∃ c k,occurrence c k=v := by decide

theorem component_link (l : Fin 11) :
    component left right (left l).1=component left right (right l).1 := Quot.sound ⟨l,rfl,rfl⟩

theorem component_root (c : Fin 12) : component left right c=component left right 0 := by
  fin_cases c
  · rfl
  · exact (component_link 0).symm
  · exact (component_link 1).symm
  · exact ((component_link 2).symm).trans ((component_link 0).symm)
  · exact (((component_link 4).symm).trans ((component_link 2).symm)).trans ((component_link 0).symm)
  · exact ((component_link 3).symm).trans ((component_link 1).symm)
  · exact ((((component_link 5).symm).trans ((component_link 4).symm)).trans ((component_link 2).symm)).trans ((component_link 0).symm)
  · exact (((((component_link 7).symm).trans ((component_link 5).symm)).trans ((component_link 4).symm)).trans ((component_link 2).symm)).trans ((component_link 0).symm)
  · exact (((component_link 6).symm).trans ((component_link 3).symm)).trans ((component_link 1).symm)
  · exact ((((((component_link 8).symm).trans ((component_link 7).symm)).trans ((component_link 5).symm)).trans ((component_link 4).symm)).trans ((component_link 2).symm)).trans ((component_link 0).symm)
  · exact (((((((component_link 10).symm).trans ((component_link 8).symm)).trans ((component_link 7).symm)).trans ((component_link 5).symm)).trans ((component_link 4).symm)).trans ((component_link 2).symm)).trans ((component_link 0).symm)
  · exact ((((component_link 9).symm).trans ((component_link 6).symm)).trans ((component_link 3).symm)).trans ((component_link 1).symm)

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

theorem clause_order (a : Fin 17 → Bool) (c : Fin 12) :
    ExactlyOne (a (occurrence c 0)) (a (occurrence c 1)) (a (occurrence c 2)) ↔
      ExactlyOne (a (PositiveCrossoverDrawing.occurrence c 0)) (a (PositiveCrossoverDrawing.occurrence c 1)) (a (PositiveCrossoverDrawing.occurrence c 2)) := by
  fin_cases c

  · change ((a 5).toNat+(a 6).toNat+(a 0).toNat=1) ↔ ((a 0).toNat+(a 6).toNat+(a 5).toNat=1)
    omega
  · change ((a 1).toNat+(a 7).toNat+(a 5).toNat=1) ↔ ((a 1).toNat+(a 7).toNat+(a 5).toNat=1)
    omega
  · change ((a 7).toNat+(a 4).toNat+(a 6).toNat=1) ↔ ((a 4).toNat+(a 6).toNat+(a 7).toNat=1)
    omega
  · change ((a 1).toNat+(a 8).toNat+(a 9).toNat=1) ↔ ((a 1).toNat+(a 9).toNat+(a 8).toNat=1)
    omega
  · change ((a 8).toNat+(a 2).toNat+(a 10).toNat=1) ↔ ((a 2).toNat+(a 10).toNat+(a 8).toNat=1)
    omega
  · change ((a 9).toNat+(a 10).toNat+(a 4).toNat=1) ↔ ((a 4).toNat+(a 9).toNat+(a 10).toNat=1)
    omega
  · change ((a 2).toNat+(a 11).toNat+(a 12).toNat=1) ↔ ((a 2).toNat+(a 12).toNat+(a 11).toNat=1)
    omega
  · change ((a 13).toNat+(a 11).toNat+(a 3).toNat=1) ↔ ((a 3).toNat+(a 13).toNat+(a 11).toNat=1)
    omega
  · change ((a 4).toNat+(a 12).toNat+(a 13).toNat=1) ↔ ((a 4).toNat+(a 12).toNat+(a 13).toNat=1)
    omega
  · change ((a 14).toNat+(a 15).toNat+(a 3).toNat=1) ↔ ((a 3).toNat+(a 15).toNat+(a 14).toNat=1)
    omega
  · change ((a 16).toNat+(a 14).toNat+(a 0).toNat=1) ↔ ((a 0).toNat+(a 16).toNat+(a 14).toNat=1)
    omega
  · change ((a 4).toNat+(a 15).toNat+(a 16).toNat=1) ↔ ((a 4).toNat+(a 15).toNat+(a 16).toNat=1)
    omega
theorem source_spec (a : Fin 17 → Bool) :
    (∀ c,ExactlyOne (a (occurrence c 0)) (a (occurrence c 1)) (a (occurrence c 2))) ↔
      Satisfies PositiveCrossoverDrawing.formula a := by
  simp only [clause_order]
  rw [PositiveCrossoverDrawing.formula]
  simp [Satisfies,PositiveCrossoverDrawing.occurrence,List.mem_ofFn,Fin.forall_fin_succ]

theorem coloring_count : ProperColoringPottsReduction.properColoringCount graph 3=
    6*Nat.card (Solutions occurrence) := by
  rw [graph,ColoringPaletteNetwork.component_coloring_count occurrence left right cover coherent,
    component_count,pow_one]

end PlanarHom.ColoringCrossMacroCore
