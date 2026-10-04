import PlanarHom.IntegerStraightDrawing
import PlanarHom.ParsimoniousOneInThreeCrossover

/-! Literal four-port positive-exact-one crossover. Its 12 clauses and 36
incidence occurrences have a checked integer straight-line square drawing. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.PositiveCrossoverDrawing
open MultiGraph ParsimoniousNorOneInThree IntegerStraightDrawing
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

/-- Ports 0,1,2,3 run counterclockwise around the square; 4 is shared EQV. -/
def clauses : Fin 12 → Clause (Fin 17) := ![
  (0,6,5),(1,7,5),(4,6,7),
  (1,9,8),(2,10,8),(4,9,10),
  (2,12,11),(3,13,11),(4,12,13),
  (3,15,14),(0,16,14),(4,15,16)]

def formula : Formula (Fin 17) := List.ofFn clauses

def occurrence (c : Fin 12) : Fin 3 → Fin 17 :=
  ![(clauses c).1,(clauses c).2.1,(clauses c).2.2]

def incidence : MultiGraph (Fin 17 ⊕ Fin 12) (Fin 12 × Fin 3) where
  src e := .inl (occurrence e.1 e.2)
  dst e := .inr e.1

/-- Every coordinate is an integer; the drawing occupies [0,16]². -/
def variablePoint : Fin 17 → Point := ![
  (0,0),(0,16),(16,16),(16,0),(8,8),
  (2,8),(3,7),(3,9),(8,14),(7,13),(9,13),
  (14,8),(13,9),(13,7),(8,2),(9,3),(7,3)]

def clausePoint : Fin 12 → Point := ![
  (2,6),(2,10),(4,8),(6,14),(10,14),(8,12),
  (14,10),(14,6),(12,8),(10,2),(6,2),(8,4)]

def point : Fin 17 ⊕ Fin 12 → Point := Sum.elim variablePoint clausePoint

/-- Fully checked finite geometry, not a diagram-based planarity assumption. -/
def certificate : Certificate incidence point where
  injective := by decide
  nondegenerate := by decide
  separated := by decide
  avoids := by decide

/-- Actual continuous curves with injective, mutually disjoint open interiors. -/
def drawing : PlaneDrawing incidence := IntegerStraightDrawing.drawing certificate

theorem planar : incidence.Planar := ⟨drawing⟩

def auxiliaryIndex : Fin 4 → Fin 3 → Fin 17 :=
  ![![5,6,7],![8,9,10],![11,12,13],![14,15,16]]

/-- Clause incidence and the previously checked Boolean gadget are literal. -/
theorem satisfies_crossover (assignment : Fin 17 → Bool) :
    Satisfies formula assignment ↔ Crossover (assignment 0) (assignment 1) (assignment 2) (assignment 3) (assignment 4)
      (fun k j => assignment (auxiliaryIndex k j)) := by
  simp [Satisfies,formula,clauses,Crossover,Gate,auxiliaryIndex,
    List.ofFn_succ,and_assoc]

/-- Opposite boundary ports agree and all 13 inner values are unique. -/
theorem satisfies_iff (assignment : Fin 17 → Bool) :
    Satisfies formula assignment ↔ assignment 2=assignment 0 ∧ assignment 3=assignment 1 ∧ assignment 4=decide (assignment 0=assignment 1) ∧
      (fun k j => assignment (auxiliaryIndex k j))=crossoverAuxiliary (assignment 0) (assignment 1) := by
  rw [satisfies_crossover,crossover_iff]

/-- Boundary port placement is fixed, available to concrete grid assembly. -/
theorem port_points :
    drawing.point (.inl 0)=(0,0) ∧ drawing.point (.inl 1)=(0,16) ∧
    drawing.point (.inl 2)=(16,16) ∧ drawing.point (.inl 3)=(16,0) := by
  norm_num [drawing,IntegerStraightDrawing.drawing,point,variablePoint,toPlane,Matrix.cons_val_two,Matrix.cons_val_three]

/-- Every vertex other than the four named ports is strictly inside the box. -/
theorem inner_points : ∀ v : Fin 17 ⊕ Fin 12,
    v≠.inl 0 → v≠.inl 1 → v≠.inl 2 → v≠.inl 3 →
      0<(point v).1 ∧ (point v).1<16 ∧ 0<(point v).2 ∧ (point v).2<16 := by decide

/-- The open part of every segment lies strictly inside the square, so separate
box interiors give the global nonintersection invariant. -/
theorem curves_inside (e : Fin 12 × Fin 3) (t : I) (ht : Inside t) :
    0<(drawing.curve e t).1 ∧ (drawing.curve e t).1<16 ∧
    0<(drawing.curve e t).2 ∧ (drawing.curve e t).2<16 := by
  have hs : 0≤(point (incidence.src e)).1 ∧ (point (incidence.src e)).1≤16 ∧
      0≤(point (incidence.src e)).2 ∧ (point (incidence.src e)).2≤16 := by
    have h : ∀ v : Fin 17,0≤(variablePoint v).1 ∧ (variablePoint v).1≤16 ∧
        0≤(variablePoint v).2 ∧ (variablePoint v).2≤16 := by decide
    exact h (occurrence e.1 e.2)
  have hd : 0<(point (incidence.dst e)).1 ∧ (point (incidence.dst e)).1<16 ∧
      0<(point (incidence.dst e)).2 ∧ (point (incidence.dst e)).2<16 := by
    have h : ∀ c : Fin 12,0<(clausePoint c).1 ∧ (clausePoint c).1<16 ∧
        0<(clausePoint c).2 ∧ (clausePoint c).2<16 := by decide
    exact h e.1
  rcases hs with ⟨hsx0,hsx1,hsy0,hsy1⟩
  rcases hd with ⟨hdx0,hdx1,hdy0,hdy1⟩
  have hsx0' : (0:ℝ)≤(point (incidence.src e)).1 := by exact_mod_cast hsx0
  have hsx1' : ((point (incidence.src e)).1:ℝ)≤16 := by exact_mod_cast hsx1
  have hsy0' : (0:ℝ)≤(point (incidence.src e)).2 := by exact_mod_cast hsy0
  have hsy1' : ((point (incidence.src e)).2:ℝ)≤16 := by exact_mod_cast hsy1
  have hdx0' : (0:ℝ)<(point (incidence.dst e)).1 := by exact_mod_cast hdx0
  have hdx1' : ((point (incidence.dst e)).1:ℝ)<16 := by exact_mod_cast hdx1
  have hdy0' : (0:ℝ)<(point (incidence.dst e)).2 := by exact_mod_cast hdy0
  have hdy1' : ((point (incidence.dst e)).2:ℝ)<16 := by exact_mod_cast hdy1
  dsimp [drawing,IntegerStraightDrawing.drawing,IntegerStraightDrawing.curve,affine,toPlane]
  rcases ht with ⟨ht0,ht1⟩
  constructor
  · nlinarith [mul_nonneg (show 0≤1-(t:ℝ) by linarith) hsx0',mul_pos ht0 hdx0']
  constructor
  · nlinarith [mul_nonneg (show 0≤1-(t:ℝ) by linarith) (show 0≤16-((point (incidence.src e)).1:ℝ) by linarith),
      mul_pos ht0 (show 0<16-((point (incidence.dst e)).1:ℝ) by linarith)]
  constructor
  · nlinarith [mul_nonneg (show 0≤1-(t:ℝ) by linarith) hsy0',mul_pos ht0 hdy0']
  · nlinarith [mul_nonneg (show 0≤1-(t:ℝ) by linarith) (show 0≤16-((point (incidence.src e)).2:ℝ) by linarith),
      mul_pos ht0 (show 0<16-((point (incidence.dst e)).2:ℝ) by linarith)]

end PlanarHom.PositiveCrossoverDrawing
