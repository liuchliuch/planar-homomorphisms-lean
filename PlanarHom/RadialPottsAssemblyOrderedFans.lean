import PlanarHom.RadialPottsAssemblyRibbonGerms
import PlanarHom.RadialPottsAssemblyGeneralRows
import PlanarHom.PlanarityLRContourPermutation
import PlanarHom.RadialPottsAssemblyPortLevels

/-! One actual ribbon narrowing works simultaneously at every computed
vertex row, including both ends of loops and every separate occurrence. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph MultiGraph.Kasteleyn Polygonal PlanarityLRRealization
open MultiGraph.PolygonalDrawing

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {d : PolygonalDrawing G}


def fanPort (S : d.TwoSidedStripData) (ray : Dart E→Plane)
    (F : ∀ a,S.EndpointFan true a (ray a)) (width : ℝ) {k : ℕ}
    (a : Dart E) (j : Fin (2*k)) : Plane :=
  (F a).direction (width*(orientedLevel portLevel a.2 j:ℝ))

/-- Geometry is taken from the literal endpoint fans. The only row premises
are numerical ray inequalities, discharged for actual computed rows below. -/
theorem exists_uniform_clockwise_fan_width
    (S : d.TwoSidedStripData) (ray : Dart E→Plane)
    (F : ∀ a,S.EndpointFan true a (ray a)) (rows : RotationRows G)
    (hne : ∀ a,(ray a).1≠0)
    (hrows : ∀ v,(rows.row v).Pairwise (fun a b => ClockwiseRayOrder (ray a) (ray b))) (k : ℕ) :
    ∃ width : ℝ,0<width ∧ width<1 ∧
      (∀ a (s : I),((F a).direction (width*(s:ℝ))).1≠0) ∧
      (∀ v,StrictAnti (fun z : Fin ((rows.row v).length*(2*k)) =>
        let p := finProdFinEquiv.symm z
        circleHeight (fanPort S ray F width ((rows.row v).get p.1) p.2))) := by
  let B : Dart E→Plane := fun a => (F a).scale • ray a
  let N : Dart E→Plane := fun a => S.width • S.signedNormal true (F a).tip
  have hB : ∀ a,(B a).1≠0 := by
    intro a
    exact mul_ne_zero (ne_of_gt (F a).scale_pos) (hne a)
  obtain ⟨w,hw,hw1,hx,hcross⟩ := exists_narrow_fans B N hB
    (fun a b => cross (B a) (B b)<0) (fun _ _ h => h)
  have hdir : ∀ a s,(F a).direction (w*s)=fanVector (B a) (N a) w s := by
    intro a s
    rfl
  refine ⟨w,hw,hw1,?_,?_⟩
  · intro a s h
    have hh := hx a s
    rw [← hdir] at hh
    rw [h,mul_zero] at hh
    exact lt_irrefl _ hh
  · intro v
    let xs := rows.row v
    let A : Fin xs.length→Dart E := xs.get
    let BD : Fin xs.length→Plane := B ∘ A
    let NN : Fin xs.length→Plane := N ∘ A
    have hrow : ∀ i j : Fin xs.length,i<j→ClockwiseRayOrder (BD i) (BD j) := by
      intro i j hij
      have hh := List.pairwise_iff_getElem.mp (hrows v) i.val j.val i.isLt j.isLt hij
      exact clockwiseRayOrder_smul _ _ (F (A i)).scale_pos (F (A j)).scale_pos hh
    have hside : ∀ i : Fin xs.length,if (A i).2 then 0<cross (BD i) (NN i)
        else cross (BD i) (NN i)<0 := by
      intro i
      have hh := (F (A i)).normal_side
      change (if true=(A i).2 then 0<cross (ray (A i)) (NN i) else cross (ray (A i)) (NN i)<0) at hh
      change if (A i).2 then 0<cross ((F (A i)).scale • ray (A i)) (NN i)
        else cross ((F (A i)).scale • ray (A i)) (NN i)<0
      cases hb : (A i).2 <;> simp only [hb,Bool.true_eq_false,if_false,if_true,cross_smul_left] at hh ⊢
      · exact mul_neg_of_pos_of_neg (F (A i)).scale_pos hh
      · exact mul_pos (F (A i)).scale_pos hh
    have hlocal := row_ports_clockwise_general BD NN (fun i => (A i).2) portLevel
      (portLevel_strictMono k) (fun i => hB (A i)) hside hrow w hw
      (fun i s => hx (A i) s) (by
        intro i j hij s t
        exact hcross (A i) (A j) hij s t)
    exact hlocal.2

end PlanarHom.RadialPottsAssemblyGeometry
