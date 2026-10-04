import PlanarHom.IntegerStraightDrawing

/-! Actual plane-drawing assembly in pairwise disjoint integer grid boxes.
Ports may be shared on box corners. Internal vertices and open edge curves are
strictly inside their cells, so the gluing proof requires no ribbon theorem. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.GridBoxAssembly
open MultiGraph
abbrev Cell := ℤ × ℤ

def corner : Fin 4 → Cell := ![(0,0),(0,1),(1,1),(1,0)]
def lattice (c : Cell) : Plane := (16*(c.1:ℝ),16*(c.2:ℝ))
def shift (c : Cell) (p : Plane) : Plane := (16*(c.1:ℝ)+p.1,16*(c.2:ℝ)+p.2)
def InsideSquare (p : Plane) : Prop := 0<p.1 ∧ p.1<16 ∧ 0<p.2 ∧ p.2<16
def InCell (c : Cell) (p : Plane) : Prop :=
  16*(c.1:ℝ)<p.1 ∧ p.1<16*((c.1:ℝ)+1) ∧ 16*(c.2:ℝ)<p.2 ∧ p.2<16*((c.2:ℝ)+1)

def shiftMap (c : Cell) : C(Plane,Plane) where
  toFun := shift c
  continuous_toFun := by unfold shift; fun_prop

theorem shift_injective (c : Cell) : Function.Injective (shift c) := by
  intro p q h
  apply Prod.ext
  · have hx := congrArg Prod.fst h; dsimp [shift] at hx; linarith
  · have hy := congrArg Prod.snd h; dsimp [shift] at hy; linarith

theorem lattice_injective : Function.Injective lattice := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [lattice] at hx hy
  apply Prod.ext
  · exact_mod_cast (show (p.1:ℝ)=q.1 by linarith)
  · exact_mod_cast (show (p.2:ℝ)=q.2 by linarith)

theorem shift_inside (c : Cell) (p : Plane) (h : InsideSquare p) : InCell c (shift c p) := by
  rcases h with ⟨hx0,hx1,hy0,hy1⟩
  dsimp [InCell,shift]
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

/-- Two open integer cells can overlap only when their grid coordinates agree. -/
theorem cell_unique (c d : Cell) (p : Plane) (hc : InCell c p) (hd : InCell d p) : c=d := by
  rcases hc with ⟨hcx0,hcx1,hcy0,hcy1⟩
  rcases hd with ⟨hdx0,hdx1,hdy0,hdy1⟩
  have hx : c.1<d.1+1 := by exact_mod_cast (show (c.1:ℝ)<(d.1:ℝ)+1 by linarith)
  have hx' : d.1<c.1+1 := by exact_mod_cast (show (d.1:ℝ)<(c.1:ℝ)+1 by linarith)
  have hy : c.2<d.2+1 := by exact_mod_cast (show (c.2:ℝ)<(d.2:ℝ)+1 by linarith)
  have hy' : d.2<c.2+1 := by exact_mod_cast (show (d.2:ℝ)<(c.2:ℝ)+1 by linarith)
  exact Prod.ext (by omega) (by omega)

/-- Every lattice vertex stays outside every open cell. -/
theorem lattice_not_inside (c b : Cell) : ¬InCell c (lattice b) := by
  rintro ⟨hx0,hx1,_⟩
  dsimp [lattice] at hx0 hx1
  have h0 : c.1<b.1 := by exact_mod_cast (show (c.1:ℝ)<b.1 by linarith)
  have h1 : b.1<c.1+1 := by exact_mod_cast (show (b.1:ℝ)<(c.1:ℝ)+1 by linarith)
  omega

/-- The four terminals are the actual square corners; only internal vertices
and open edge curves must lie strictly within its interior. -/
structure BoxDrawing {W E : Type} (G : MultiGraph (Fin 4 ⊕ W) E) where
  drawing : PlaneDrawing G
  ports : ∀ k,drawing.point (.inl k)=lattice (corner k)
  internal : ∀ w,InsideSquare (drawing.point (.inr w))
  curves : ∀ e t,Inside t → InsideSquare (drawing.curve e t)

variable {C B : Type} {W E : C → Type}
variable (G : ∀ c,MultiGraph (Fin 4 ⊕ W c) (E c))
variable (d : ∀ c,BoxDrawing (G c))
variable (cell : C → Cell) (bpoint : B → Cell) (port : C → Fin 4 → B)

abbrev Vertex := B ⊕ Sigma W
abbrev Edge := Sigma E

def placeVertex (c : C) : Fin 4 ⊕ W c → Vertex (B := B) (W := W)
  | .inl k => .inl (port c k)
  | .inr w => .inr ⟨c,w⟩

def graph : MultiGraph (Vertex (B := B) (W := W)) (Edge (E := E)) where
  src e := placeVertex port e.1 ((G e.1).src e.2)
  dst e := placeVertex port e.1 ((G e.1).dst e.2)

def point : Vertex (B := B) (W := W) → Plane
  | .inl b => lattice (bpoint b)
  | .inr w => shift (cell w.1) ((d w.1).drawing.point (.inr w.2))

variable (hc : Function.Injective cell) (hb : Function.Injective bpoint)
variable (hp : ∀ c k,bpoint (port c k)=((cell c).1+(corner k).1,(cell c).2+(corner k).2))

include hc hb in
theorem point_injective : Function.Injective (point G d cell bpoint) := by
  intro v w he
  cases v with
  | inl b =>
    cases w with
    | inl b' => exact congrArg Sum.inl (hb (lattice_injective he))
    | inr w =>
      have hw := shift_inside (cell w.1) _ ((d w.1).internal w.2)
      change lattice (bpoint b)=shift (cell w.1) _ at he
      rw [←he] at hw
      exact False.elim (lattice_not_inside _ _ hw)
  | inr v =>
    cases w with
    | inl b =>
      have hv := shift_inside (cell v.1) _ ((d v.1).internal v.2)
      change shift (cell v.1) _=lattice (bpoint b) at he
      rw [he] at hv
      exact False.elim (lattice_not_inside _ _ hv)
    | inr w =>
      have hv := shift_inside (cell v.1) _ ((d v.1).internal v.2)
      have hw := shift_inside (cell w.1) _ ((d w.1).internal w.2)
      change shift (cell v.1) _=shift (cell w.1) _ at he
      rw [←he] at hw
      have hcell := hc (cell_unique _ _ _ hv hw)
      rcases v with ⟨c,v⟩
      rcases w with ⟨c',w⟩
      dsimp only at hcell
      subst c'
      have hvw := (d c).drawing.point_injective (shift_injective (cell c) he)
      have heq : v=w := Sum.inr.inj hvw
      subst w
      rfl

include hp in
theorem point_place (c : C) (v : Fin 4 ⊕ W c) :
    point G d cell bpoint (placeVertex port c v)=shift (cell c) ((d c).drawing.point v) := by
  cases v with
  | inl k =>
    simp only [placeVertex,point,(d c).ports,hp,lattice,shift,Int.cast_add]
    congr 1 <;> ring
  | inr w => rfl

/-- Construct the drawing edge by edge, preserving every occurrence and shared
port vertex. No existential planarity premise or geometric oracle is used. -/
def drawing : PlaneDrawing (graph G port) where
  point := point G d cell bpoint
  point_injective := point_injective G d cell bpoint hc hb
  curve e := (shiftMap (cell e.1)).comp ((d e.1).drawing.curve e.2)
  curve_zero e := by
    change shift (cell e.1) ((d e.1).drawing.curve e.2 0)=_
    rw [(d e.1).drawing.curve_zero]
    exact (point_place G d cell bpoint port hp e.1 _).symm
  curve_one e := by
    change shift (cell e.1) ((d e.1).drawing.curve e.2 1)=_
    rw [(d e.1).drawing.curve_one]
    exact (point_place G d cell bpoint port hp e.1 _).symm
  interior_injective := by
    rintro ⟨c,e⟩ ⟨c',f⟩ s t hs ht he
    change shift (cell c) ((d c).drawing.curve e s)=shift (cell c') ((d c').drawing.curve f t) at he
    have hs' := shift_inside (cell c) _ ((d c).curves e s hs)
    have ht' := shift_inside (cell c') _ ((d c').curves f t ht)
    rw [←he] at ht'
    have hcc := hc (cell_unique _ _ _ hs' ht')
    subst c'
    obtain ⟨hef,hst⟩ := (d c).drawing.interior_injective e f s t hs ht (shift_injective (cell c) he)
    exact ⟨by subst f; rfl,hst⟩
  interior_avoids := by
    rintro ⟨c,e⟩ t ht (b | ⟨c',w⟩) he
    · change shift (cell c) ((d c).drawing.curve e t)=lattice (bpoint b) at he
      have hs := shift_inside (cell c) _ ((d c).curves e t ht)
      rw [he] at hs
      exact lattice_not_inside _ _ hs
    · change shift (cell c) ((d c).drawing.curve e t)=shift (cell c') ((d c').drawing.point (.inr w)) at he
      have hs := shift_inside (cell c) _ ((d c).curves e t ht)
      have hw := shift_inside (cell c') _ ((d c').internal w)
      rw [←he] at hw
      have hcc := hc (cell_unique _ _ _ hs hw)
      subst c'
      exact (d c).drawing.interior_avoids e t ht (.inr w) (shift_injective (cell c) he)

include d cell bpoint hc hb hp in
theorem planar : (graph G port).Planar := ⟨drawing G d cell bpoint port hc hb hp⟩

end PlanarHom.GridBoxAssembly
