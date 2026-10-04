import PlanarHom.RadialPottsLongMatching
import PlanarHom.RadialPottsTwoMatchings

/-! NEW reconstruction: literal occurrence assembly of the all-k radial tiles.
Only paired boundary ports are identified. Every white vertex and edge remains
an individually indexed occurrence, including on source loops and parallels. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph.Medial
abbrev Dart (E : Type) := E × Bool
end PlanarHom.MultiGraph.Medial

namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile
variable {E : Type} {k : ℕ}

abbrev Vertex (E : Type) (k : ℕ) := (E × White k) ⊕ (Medial.Dart E × Fin k)

def sideOfBits (b c : Bool) : Fin 4 := if b then (if c then 3 else 2) else (if c then 1 else 0)
def endBit (s : Fin 4) : Bool := decide (2≤s.val)
def oddBit (s : Fin 4) : Bool := decide (s.val%2=1)

@[simp] theorem endBit_sideOfBits (b c : Bool) : endBit (sideOfBits b c)=b := by cases b <;> cases c <;> decide
@[simp] theorem oddBit_sideOfBits (b c : Bool) : oddBit (sideOfBits b c)=c := by cases b <;> cases c <;> decide
@[simp] theorem sideOfBits_bits (s : Fin 4) : sideOfBits (endBit s) (oddBit s)=s := by fin_cases s <;> decide

def reverseLane (a : Fin k) : Fin k := ⟨k-1-a.val,by have := a.isLt; omega⟩
@[simp] theorem reverseLane_twice (a : Fin k) : reverseLane (reverseLane a)=a := by
  apply Fin.ext
  dsimp [reverseLane]
  have := a.isLt
  omega

def portImage (rotation : Equiv.Perm (Medial.Dart E)) (e : E) (p : Port k) : Medial.Dart E × Fin k :=
  if oddBit p.1 then ((e,endBit p.1),p.2) else (rotation.symm (e,endBit p.1),reverseLane p.2)

def portPreimage (rotation : Equiv.Perm (Medial.Dart E)) (w : Medial.Dart E × Fin k) (b : Bool) : E × Port k :=
  if b then (w.1.1,(sideOfBits w.1.2 true,w.2))
  else ((rotation w.1).1,(sideOfBits (rotation w.1).2 false,reverseLane w.2))

def portFiberEquiv (rotation : Equiv.Perm (Medial.Dart E)) :
    (E × Port k) ≃ ((Medial.Dart E × Fin k) × Bool) where
  toFun p := (portImage rotation p.1 p.2,oddBit p.2.1)
  invFun p := portPreimage rotation p.1 p.2
  left_inv p := by
    rcases p with ⟨e,s,a⟩
    by_cases hc : oddBit s=true
    · have hs := sideOfBits_bits s
      simp only [hc] at hs
      simp [portImage,portPreimage,hc,hs]
    · have hc' : oddBit s=false := Bool.eq_false_iff.mpr hc
      have hs := sideOfBits_bits s
      simp only [hc'] at hs
      simp [portImage,portPreimage,hc',hs]
  right_inv p := by
    rcases p with ⟨⟨d,a⟩,b⟩
    cases b <;> simp [portImage,portPreimage]

@[simp] theorem portImage_preimage (rotation : Equiv.Perm (Medial.Dart E))
    (w : Medial.Dart E × Fin k) (b : Bool) :
    portImage rotation (portPreimage rotation w b).1 (portPreimage rotation w b).2=w :=
  congrArg Prod.fst ((portFiberEquiv rotation).apply_symm_apply (w,b))

def embed (rotation : Equiv.Perm (Medial.Dart E)) (e : E) : RadialPottsTile.Vertex k → Vertex E k
  | .inl w => .inl (e,w)
  | .inr p => .inr (portImage rotation e p)

def graph (rotation : Equiv.Perm (Medial.Dart E)) (k : ℕ) :
    MultiGraph (Vertex E k) (E × RadialPottsTile.Edge k) where
  src p := embed rotation p.1 ((RadialPottsTile.graph k).src p.2)
  dst p := embed rotation p.1 ((RadialPottsTile.graph k).dst p.2)

def longGraph (rotation : Equiv.Perm (Medial.Dart E)) (k : ℕ) :
    MultiGraph (Vertex E k) (E × Long k) where
  src p := embed rotation p.1 (.inl (longLeft p.2))
  dst p := embed rotation p.1 (longRight p.2)

def longShortEquiv (E : Type) (k : ℕ) :
    ((E × Long k) ⊕ (E × (HalfShort k × Bool))) ≃ (E × RadialPottsTile.Edge k) where
  toFun p := match p with | .inl (e,f) => (e,.inl f) | .inr (e,f) => (e,.inr f)
  invFun p := match p.2 with | .inl f => .inl (p.1,f) | .inr f => .inr (p.1,f)
  left_inv p := by rcases p with ⟨e,f⟩ | ⟨e,f⟩ <;> rfl
  right_inv p := by rcases p with ⟨e,f | f⟩ <;> rfl

variable [Fintype E]

theorem card_vertices (k : ℕ) : Fintype.card (Vertex E k)=
    4*k^2*Fintype.card E+2*k*Fintype.card E := by
  simp only [Vertex,Fintype.card_sum,Fintype.card_prod,card_white,Medial.Dart,Fintype.card_bool,Fintype.card_fin]
  ring

theorem card_long (k : ℕ) : Fintype.card (E × Long k)=2*k*(k+1)*Fintype.card E := by
  rw [Fintype.card_prod,RadialPottsTile.card_long]
  ring

theorem card_short (k : ℕ) : Fintype.card (E × (HalfShort k × Bool))=4*k^2*Fintype.card E := by
  rw [Fintype.card_prod,RadialPottsTile.card_short]
  ring
end PlanarHom.RadialPotts.Assembly
