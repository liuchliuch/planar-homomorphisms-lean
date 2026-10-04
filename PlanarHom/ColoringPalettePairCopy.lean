import PlanarHom.ColoringClausePaletteState
import PlanarHom.IntegerStraightDrawing

/-! Actual one- and two-diamond palette copying strips. The outgoing palette
rim edge is absent, so two neighboring macro patches never duplicate a segment
along their shared boundary. Input distinctness alone forces every new vertex.
One diamond reverses the physical pair order; two preserve it. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringPalettePairCopy
open MultiGraph IntegerStraightDrawing PlanarColoringExclusiveCrossing
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace Single

def edgeIndex : Fin 6 → Fin 8 := ![1,3,4,5,6,7]
def graph : MultiGraph (Fin 5) (Fin 6) where
  src e := PlanarColoringExclusiveCrossing.graph.src (edgeIndex e)
  dst e := PlanarColoringExclusiveCrossing.graph.dst (edgeIndex e)
def Proper (col : Fin 5 → Fin 3) : Prop := ∀ e,col (graph.src e)≠col (graph.dst e)

/-- Six literal edges suffice when the incoming palette is distinct. No
outgoing-rim edge or separate outgoing-separation premise is needed. -/
theorem proper_iff (col : Fin 5 → Fin 3) (h : col 0≠col 1) :
    Proper col ↔ col=PlanarColoringExclusiveCrossing.extension (col 0) (col 1) := by
  have finite_check : ∀ a b c d z : Fin 3,a≠b →
      ((b≠c ∧ d≠a ∧ a≠z ∧ b≠z ∧ c≠z ∧ d≠z) ↔
        c=a ∧ d=b ∧ z=third a b) := by decide
  have hp : Proper col ↔
      col 1≠col 2 ∧ col 3≠col 0 ∧ col 0≠col 4 ∧ col 1≠col 4 ∧ col 2≠col 4 ∧ col 3≠col 4 := by
    simp [Proper,graph,edgeIndex,PlanarColoringExclusiveCrossing.graph,Fin.forall_fin_succ]
  rw [hp,finite_check _ _ _ _ _ h]
  constructor
  · rintro ⟨h2,h3,h4⟩
    funext v
    fin_cases v <;> simp [PlanarColoringExclusiveCrossing.extension,h2,h3,h4]
  · intro he
    exact ⟨congrFun he 2,congrFun he 3,congrFun he 4⟩

def point : Fin 5 → Point := ![(0,12),(0,4),(16,4),(16,12),(8,8)]
def certificate : Certificate graph point where
  injective := by decide
  nondegenerate := by decide
  separated := by decide
  avoids := by decide

def drawing : PlaneDrawing graph := IntegerStraightDrawing.drawing certificate
theorem planar : graph.Planar := ⟨drawing⟩

end Single
namespace Double

def leftMap : Fin 5 → Fin 8 := ![0,1,4,5,6]
def rightMap : Fin 5 → Fin 8 := ![4,5,2,3,7]
def sideMap (b : Bool) : Fin 5 → Fin 8 := if b then rightMap else leftMap

def graph : MultiGraph (Fin 8) (Bool × Fin 6) where
  src e := sideMap e.1 (Single.graph.src e.2)
  dst e := sideMap e.1 (Single.graph.dst e.2)
def Proper (col : Fin 8 → Fin 3) : Prop := ∀ e,col (graph.src e)≠col (graph.dst e)

def extension (a b : Fin 3) : Fin 8 → Fin 3 := ![a,b,a,b,a,b,third a b,third a b]

theorem proper_split (col : Fin 8 → Fin 3) : Proper col ↔
    Single.Proper (col ∘ leftMap) ∧ Single.Proper (col ∘ rightMap) := by
  constructor
  · intro h
    exact ⟨fun e => h (false,e),fun e => h (true,e)⟩
  · rintro ⟨hl,hr⟩ ⟨b,e⟩
    cases b
    · exact hl e
    · exact hr e

theorem proper_iff (col : Fin 8 → Fin 3) (h : col 0≠col 1) :
    Proper col ↔ col=extension (col 0) (col 1) := by
  constructor
  · intro hp
    have hs := (proper_split col).mp hp
    have hl := (Single.proper_iff (col ∘ leftMap) h).mp hs.1
    have h4 : col 4=col 0 := congrFun hl 2
    have h5 : col 5=col 1 := congrFun hl 3
    have h6 : col 6=third (col 0) (col 1) := congrFun hl 4
    have hsep : (col ∘ rightMap) 0≠(col ∘ rightMap) 1 := by
      change col 4≠col 5
      rwa [h4,h5]
    have hr := (Single.proper_iff (col ∘ rightMap) hsep).mp hs.2
    have h2 : col 2=col 4 := congrFun hr 2
    have h3 : col 3=col 5 := congrFun hr 3
    have h7 : col 7=third (col 4) (col 5) := congrFun hr 4
    funext v
    fin_cases v <;> simp [extension,h2,h3,h4,h5,h6,h7]
  · intro he
    rw [he,proper_split]
    have hleft : extension (col 0) (col 1) ∘ leftMap=
        PlanarColoringExclusiveCrossing.extension (col 0) (col 1) := by
      funext v; fin_cases v <;> rfl
    have hright : extension (col 0) (col 1) ∘ rightMap=
        PlanarColoringExclusiveCrossing.extension (col 0) (col 1) := by
      funext v; fin_cases v <;> rfl
    rw [hleft,hright]
    constructor <;> exact (Single.proper_iff _ h).mpr rfl

def point : Fin 8 → Point := ![(0,12),(0,4),(16,12),(16,4),(8,6),(8,10),(4,8),(12,8)]
def certificate : Certificate graph point where
  injective := by decide
  nondegenerate := by decide
  separated := by decide
  avoids := by decide

def drawing : PlaneDrawing graph := IntegerStraightDrawing.drawing certificate
theorem planar : graph.Planar := ⟨drawing⟩

end Double
end PlanarHom.ColoringPalettePairCopy
