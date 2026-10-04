import PlanarHom.ColoringNetworkComponentCount
import PlanarHom.RoutingCellDrawings

/-! Concrete connected palette-link tree of the finite test macro. All links
are literal gadgets and all source occurrences retain their actual variable. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringTestMacroCore
open ColoringPaletteNetwork ParsimoniousNorOneInThree PlanarColoringClause
set_option maxHeartbeats 6000000

def occurrence : Fin 1 → Fin 3 → Fin 3 := ![![1,0,2]]
def left : Fin 0 → Fin 1 × Fin 3 := fun l => l.elim0
def right : Fin 0 → Fin 1 × Fin 3 := fun l => l.elim0

def graph := ColoringPaletteNetwork.graph occurrence left right

theorem cover : ∀ v,∃ c k,occurrence c k=v := by decide

theorem component_link (l : Fin 0) :
    component left right (left l).1=component left right (right l).1 := Quot.sound ⟨l,rfl,rfl⟩

theorem component_root (c : Fin 1) : component left right c=component left right 0 := by
  fin_cases c
  rfl

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

theorem source_spec (a : Fin 3 → Bool) :
    (∀ c,ExactlyOne (a (occurrence c 0)) (a (occurrence c 1)) (a (occurrence c 2))) ↔
      ExactlyOne (a 0) (a 1) (a 2) := by
  simp [occurrence,Fin.forall_fin_succ,ExactlyOne]
  omega

theorem coloring_count : ProperColoringPottsReduction.properColoringCount graph 3=
    6*Nat.card (Solutions occurrence) := by
  rw [graph,ColoringPaletteNetwork.component_coloring_count occurrence left right cover coherent,
    component_count,pow_one]

end PlanarHom.ColoringTestMacroCore
