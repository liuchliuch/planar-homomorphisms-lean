import PlanarHom.RadialPottsOnionGraphs
import Mathlib.Algebra.Group.Fin.Basic

/-! A literal quarter-turn sends the unswitched red onion to the blue onion.
Both occurrence labels and vertices are bijected, preserving ordered incidence.
All definitions include the empty onion. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPottsTile.OnionBoundary

/-- The blue onion has the same long occurrences and the complementary shorts. -/
def blueGraph (k : ℕ) := withShort (@oddWhite k) (@nextWhite k)

/-- One clockwise side step. -/
def rotateSide : Fin 4 ≃ Fin 4 := Equiv.addRight 1

/-- A quarter-turn advances ring `r` by its odd side length `2*r+1`. -/
def rotateWhite (k : ℕ) : White k ≃ White k :=
  Equiv.sigmaCongrRight fun r =>
    letI : NeZero (8*r.val+4) := ⟨by omega⟩
    Equiv.addRight ⟨2*r.val+1, by omega⟩

def rotatePort (k : ℕ) : Port k ≃ Port k :=
  Equiv.prodCongr rotateSide (Equiv.refl _)

def rotateVertex (k : ℕ) : Vertex k ≃ Vertex k :=
  Equiv.sumCongr (rotateWhite k) (rotatePort k)

def rotateLong (k : ℕ) : Long k ≃ Long k :=
  Equiv.sigmaCongrRight fun _ => Equiv.prodCongr rotateSide (Equiv.refl _)

/-- Red start `2*h` turns into blue start `2*(h+r)+1`. -/
def rotateHalfShort (k : ℕ) : HalfShort k ≃ HalfShort k :=
  Equiv.sigmaCongrRight fun r =>
    letI : NeZero (4*r.val+2) := ⟨by omega⟩
    Equiv.addRight ⟨r.val, by omega⟩

def rotateEdge (k : ℕ) : (Long k ⊕ HalfShort k) ≃ (Long k ⊕ HalfShort k) :=
  Equiv.sumCongr (rotateLong k) (rotateHalfShort k)

@[simp] theorem rotateSide_val (s : Fin 4) :
    (rotateSide s).val=(s.val+1)%4 := rfl

@[simp] theorem rotateSide_zero : rotateSide 0=1 := rfl
@[simp] theorem rotateSide_one : rotateSide 1=2 := rfl
@[simp] theorem rotateSide_two : rotateSide 2=3 := rfl
@[simp] theorem rotateSide_three : rotateSide 3=0 := rfl

@[simp] theorem rotateSide_symm_zero : rotateSide.symm 0=3 := rfl
@[simp] theorem rotateSide_symm_one : rotateSide.symm 1=0 := rfl
@[simp] theorem rotateSide_symm_two : rotateSide.symm 2=1 := rfl
@[simp] theorem rotateSide_symm_three : rotateSide.symm 3=2 := rfl

@[simp] theorem rotateWhite_ring {k : ℕ} (w : White k) :
    (rotateWhite k w).1=w.1 := rfl

@[simp] theorem rotateWhite_index {k : ℕ} (w : White k) :
    (rotateWhite k w).2.val=(w.2.val+(2*w.1.val+1))%(8*w.1.val+4) := rfl

@[simp] theorem rotateHalfShort_ring {k : ℕ} (e : HalfShort k) :
    (rotateHalfShort k e).1=e.1 := rfl

@[simp] theorem rotateHalfShort_index {k : ℕ} (e : HalfShort k) :
    (rotateHalfShort k e).2.val=(e.2.val+e.1.val)%(4*e.1.val+2) := rfl

@[simp] theorem rotateVertex_white {k : ℕ} (w : White k) :
    rotateVertex k (.inl w)=.inl (rotateWhite k w) := rfl

@[simp] theorem rotateVertex_port {k : ℕ} (s : Fin 4) (a : Fin k) :
    rotateVertex k (.inr (s,a))=.inr (rotateSide s,a) := rfl

@[simp] theorem rotateVertex_symm_white {k : ℕ} (w : White k) :
    (rotateVertex k).symm (.inl w)=.inl ((rotateWhite k).symm w) := rfl

@[simp] theorem rotateVertex_symm_port {k : ℕ} (s : Fin 4) (a : Fin k) :
    (rotateVertex k).symm (.inr (s,a))=.inr (rotateSide.symm s,a) := rfl

/-- Side-local coordinates rotate by one side, with their offset unchanged. -/
@[simp] theorem rotateWhite_whiteAt {k : ℕ} (r : Fin k) (s : Fin 4)
    (t : ℕ) (ht : t ≤ 2*r.val) :
    rotateWhite k (whiteAt r s t ht)=whiteAt r (rotateSide s) t ht := by
  apply white_ext
  · rfl
  · rw [rotateWhite_index]
    dsimp [whiteAt]
    fin_cases s <;> norm_num <;> (try simp only [Nat.mul_add, Nat.mul_one]) <;>
      (first | rw [Nat.mod_eq_of_lt (by omega)]
             | rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]) <;> omega

@[simp] theorem rotateWhite_longLeft {k : ℕ} (e : Long k) :
    rotateWhite k (longLeft e)=longLeft (rotateLong k e) := by
  exact rotateWhite_whiteAt e.1 e.2.1 (2*e.2.2.val) (by have := e.2.2.isLt; omega)

@[simp] theorem rotateVertex_longRight {k : ℕ} (e : Long k) :
    rotateVertex k (longRight e)=longRight (rotateLong k e) := by
  by_cases h : e.1.val+1<k
  · simp only [longRight, rotateLong, Equiv.sigmaCongrRight_apply, Equiv.prodCongr_apply,
      h, dite_true]
    simp only [Nat.add_assoc]
    change Sum.inl (rotateWhite k (whiteAt ⟨e.1.val+1,h⟩ e.2.1
      (2*e.2.2.val+1) (by have := e.2.2.isLt; dsimp; omega))) =
      Sum.inl (whiteAt ⟨e.1.val+1,h⟩ (rotateSide e.2.1)
        (2*e.2.2.val+1) (by have := e.2.2.isLt; dsimp; omega))
    rw [rotateWhite_whiteAt]
  · simp only [longRight, rotateLong, Equiv.sigmaCongrRight_apply, Equiv.prodCongr_apply,
      h, dite_false]
    rfl

/-- The rotated initial endpoint is the initial endpoint of its blue occurrence. -/
@[simp] theorem rotateWhite_evenWhite {k : ℕ} (e : HalfShort k) :
    rotateWhite k (evenWhite e)=oddWhite (rotateHalfShort k e) := by
  apply white_ext
  · rfl
  · rw [rotateWhite_index]
    change (2*e.2.val+(2*e.1.val+1))%(8*e.1.val+4) =
      2*((e.2.val+e.1.val)%(4*e.1.val+2))+1
    have he := e.2.isLt
    by_cases h : e.2.val+e.1.val<4*e.1.val+2
    · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_sub_mod (show 8*e.1.val+4 ≤ 2*e.2.val+(2*e.1.val+1) by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (show 4*e.1.val+2 ≤ e.2.val+e.1.val by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega

/-- The next endpoint also rotates correctly, including wrap-around at index zero. -/
@[simp] theorem rotateWhite_oddWhite {k : ℕ} (e : HalfShort k) :
    rotateWhite k (oddWhite e)=nextWhite (rotateHalfShort k e) := by
  apply white_ext
  · rfl
  · rw [rotateWhite_index]
    change (2*e.2.val+1+(2*e.1.val+1))%(8*e.1.val+4) =
      (2*((e.2.val+e.1.val)%(4*e.1.val+2))+2)%(8*e.1.val+4)
    have he := e.2.isLt
    by_cases h : e.2.val+e.1.val<4*e.1.val+2
    · rw [Nat.mod_eq_of_lt h]
      congr 1
      omega
    · rw [Nat.mod_eq_sub_mod (show 8*e.1.val+4 ≤ 2*e.2.val+1+(2*e.1.val+1) by omega),
        Nat.mod_eq_sub_mod (show 4*e.1.val+2 ≤ e.2.val+e.1.val by omega),
        Nat.mod_eq_of_lt (show e.2.val+e.1.val-(4*e.1.val+2)<4*e.1.val+2 by omega)]
      congr 1
      omega

/-- Ordered incidence equivalence between the two literal unswitched onions. -/
def rotationIncidenceEquiv (k : ℕ) : (redGraph k).IncidenceEquiv (blueGraph k) where
  vertex := rotateVertex k
  edge := rotateEdge k
  src_eq e := by
    cases e with
    | inl e =>
      exact congrArg Sum.inl (rotateWhite_longLeft e).symm
    | inr e =>
      exact congrArg Sum.inl (rotateWhite_evenWhite e).symm
  dst_eq e := by
    cases e with
    | inl e => exact (rotateVertex_longRight e).symm
    | inr e => exact congrArg Sum.inl (rotateWhite_oddWhite e).symm

/-- Full-edge red connectivity is exactly blue connectivity after the quarter-turn. -/
theorem rotation_connected_iff {k : ℕ} (u v : Vertex k) :
    (redGraph k).componentSetoid Finset.univ u v ↔
      (blueGraph k).componentSetoid Finset.univ (rotateVertex k u) (rotateVertex k v) := by
  constructor
  · exact PottsCentered.component_relation_incidenceEquiv (rotationIncidenceEquiv k)
  · intro h
    have hh := PottsCentered.component_relation_incidenceEquiv
      (rotationIncidenceEquiv k).symm h
    simpa only [rotationIncidenceEquiv, MultiGraph.IncidenceEquiv.symm,
      Equiv.symm_apply_apply] using hh

/-- Inverse transport, with arbitrary blue vertices rather than pre-rotated ones. -/
theorem inverse_rotation_connected_iff {k : ℕ} (u v : Vertex k) :
    (blueGraph k).componentSetoid Finset.univ u v ↔
      (redGraph k).componentSetoid Finset.univ
        ((rotateVertex k).symm u) ((rotateVertex k).symm v) := by
  simpa only [Equiv.apply_symm_apply] using
    (rotation_connected_iff ((rotateVertex k).symm u) ((rotateVertex k).symm v)).symm

/-- Port connectivity transports with the side coordinate advanced modulo four. -/
theorem rotation_port_connected_iff {k : ℕ} (s t : Fin 4) (a b : Fin k) :
    (redGraph k).componentSetoid Finset.univ (.inr (s,a)) (.inr (t,b)) ↔
      (blueGraph k).componentSetoid Finset.univ
        (.inr (rotateSide s,a)) (.inr (rotateSide t,b)) :=
  rotation_connected_iff _ _

end PlanarHom.RadialPottsTile.OnionBoundary
