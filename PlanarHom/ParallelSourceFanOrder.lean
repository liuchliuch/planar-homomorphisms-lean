import PlanarHom.ParallelSourceRows
import PlanarHom.ParallelSourcePolygonalDrawing
import PlanarHom.RadialPottsAssemblyCircleWires

/-! Ordered parallel-copy germs in actual source ribbons. The same small
positive width works at every endpoint; copy indices increase at sources and
decrease at targets, exactly as in the materialized inherited rows. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.ParallelSource
open MultiGraph MultiGraph.Kasteleyn Polygonal PlanarityLRRealization
open MultiGraph.PolygonalDrawing RadialPottsAssemblyGeometry
variable {V E : Type} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G}

 def copyLevel {t : ℕ} (i : Fin t) : I := unitInterval.symm (RibbonDrawing.level i)

 theorem copyLevel_strictAnti (t : ℕ) : StrictAnti (@copyLevel t) := by
  intro i j hij
  have ht : (0:ℝ)<t := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hji : (i.val:ℝ)<j.val := by exact_mod_cast hij
  have hd := div_lt_div_of_pos_right hji ht
  change 1-(j.val:ℝ)/t<1-(i.val:ℝ)/t
  linarith

 theorem copyLevel_injective (t : ℕ) : Function.Injective (@copyLevel t) :=
  (copyLevel_strictAnti t).injective

 def narrowedLevel {t : ℕ} (w : ℝ) (hw : 0<w) (hw1 : w<1) (i : Fin t) : I :=
  narrowMap w hw hw1 (copyLevel i)

 theorem narrowedLevel_injective {t : ℕ} (w : ℝ) (hw : 0<w) (hw1 : w<1) :
    Function.Injective (narrowedLevel (t:=t) w hw hw1) :=
  (narrowMap_injective w hw hw1).comp (copyLevel_injective t)

 def copyRay (S : d.TwoSidedStripData) (ray : Dart E→Plane)
    (F : ∀a,S.EndpointFan true a (ray a)) {t : ℕ}
    (w : ℝ) (a : Dart (E×Fin t)) : Plane :=
  (F (baseDart a)).direction (w*(copyLevel a.1.2:ℝ))

 theorem fan_same_halfPlane (x y z : ℝ) (hy : 0<x*y) (hz : 0<x*z) : 0<y*z := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hyy : y<0 := by nlinarith
    have hzz : z<0 := by nlinarith
    exact mul_pos_of_neg_of_neg hyy hzz
  · subst x; simp at hy
  · have hyy : 0<y := by nlinarith
    have hzz : 0<z := by nlinarith
    exact mul_pos hyy hzz

 theorem same_copy_order (S : d.TwoSidedStripData) (ray : Dart E→Plane)
    (F : ∀a,S.EndpointFan true a (ray a)) {t : ℕ} (w : ℝ) (hw : 0<w)
    (hx : ∀a (s : I),0<((F a).scale • ray a).1*((F a).direction (w*s)).1)
    (a : Dart E) (i j : Fin t) (hij : i<j) :
    ClockwiseRayOrder (copyRay S ray F w (copyDart a i)) (copyRay S ray F w (copyDart a j)) := by
  have hi := hx a (copyLevel (orientedIndex a.2 i))
  have hj := hx a (copyLevel (orientedIndex a.2 j))
  have hp := fan_same_halfPlane _ _ _ hi hj
  change ClockwiseRayOrder ((F a).direction (w*(copyLevel (orientedIndex a.2 i):ℝ)))
    ((F a).direction (w*(copyLevel (orientedIndex a.2 j):ℝ)))
  refine Or.inl ⟨hp,?_⟩
  rw [(F a).cross_direction]
  have hs := (F a).normal_side
  cases hb : a.2
  · have hrev : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
    have hlev := copyLevel_strictAnti t hrev
    have hr : (copyLevel i.rev:ℝ)<(copyLevel j.rev:ℝ) := hlev
    simp only [hb,Bool.true_eq_false,if_false] at hs
    simp only [hb,orientedIndex,Bool.false_eq_true,if_false]
    exact mul_neg_of_pos_of_neg (mul_pos (F a).scale_pos (by nlinarith)) hs
  · have hlev := copyLevel_strictAnti t hij
    have hr : (copyLevel j:ℝ)<(copyLevel i:ℝ) := hlev
    simp only [hb,if_true] at hs
    simp only [hb,orientedIndex,if_true]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (F a).scale_pos (by nlinarith)) hs

 theorem different_copy_order (S : d.TwoSidedStripData) (ray : Dart E→Plane)
    (F : ∀a,S.EndpointFan true a (ray a)) {t : ℕ} (w : ℝ)
    (hx : ∀a (s : I),0<((F a).scale • ray a).1*((F a).direction (w*s)).1)
    (hc : ∀a b,cross ((F a).scale • ray a) ((F b).scale • ray b)<0→∀s u : I,
      cross ((F a).direction (w*s)) ((F b).direction (w*u))<0)
    (a b : Dart E) (h : ClockwiseRayOrder (ray a) (ray b)) (i j : Fin t) :
    ClockwiseRayOrder (copyRay S ray F w (copyDart a i)) (copyRay S ray F w (copyDart b j)) := by
  have hh := clockwiseRayOrder_smul _ _ (F a).scale_pos (F b).scale_pos h
  have hi := hx a (copyLevel (orientedIndex a.2 i))
  have hj := hx b (copyLevel (orientedIndex b.2 j))
  change ClockwiseRayOrder ((F a).direction (w*(copyLevel (orientedIndex a.2 i):ℝ)))
    ((F b).direction (w*(copyLevel (orientedIndex b.2 j):ℝ)))
  rcases hh with hh | hh
  · left
    constructor
    · rcases mul_pos_iff.mp hh.1 with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · apply mul_pos <;> nlinarith
      · apply mul_pos_of_neg_of_neg <;> nlinarith
    · exact hc a b hh.2 _ _
  · right
    constructor <;> nlinarith

 theorem exists_parallel_fan_width [DecidableEq (Dart E)]
    (S : d.TwoSidedStripData) (ray : Dart E→Plane)
    (F : ∀a,S.EndpointFan true a (ray a)) (R : RotationRows G)
    (hne : ∀a,(ray a).1≠0)
    (hrows : ∀v,(R.row v).Pairwise (fun a b=>ClockwiseRayOrder (ray a) (ray b))) (t : ℕ) :
    ∃w : ℝ,0<w ∧ w<1 ∧ (∀a : Dart (E×Fin t),(copyRay S ray F w a).1≠0) ∧
      (∀v,((rows R t).row v).Pairwise (fun a b=>ClockwiseRayOrder (copyRay S ray F w a) (copyRay S ray F w b))) := by
  let B : Dart E→Plane := fun a => (F a).scale • ray a
  let N : Dart E→Plane := fun a => S.width • S.signedNormal true (F a).tip
  have hb : ∀a,(B a).1≠0 := fun a => mul_ne_zero (ne_of_gt (F a).scale_pos) (hne a)
  obtain ⟨w,hw,hw1,hx,hcross⟩ := exists_narrow_fans B N hb
    (fun a b=>cross (B a) (B b)<0) (fun _ _ h=>h)
  have hxx : ∀a (s : I),0<((F a).scale • ray a).1*((F a).direction (w*s)).1 := hx
  have hcc : ∀a b,cross ((F a).scale • ray a) ((F b).scale • ray b)<0→∀s u : I,
      cross ((F a).direction (w*s)) ((F b).direction (w*u))<0 := hcross
  refine ⟨w,hw,hw1,?_,?_⟩
  · intro a ha
    have hh := hxx (baseDart a) (copyLevel a.1.2)
    change 0<_*(copyRay S ray F w a).1 at hh
    rw [ha,mul_zero] at hh
    exact lt_irrefl _ hh
  · intro v
    apply List.pairwise_flatMap.mpr
    constructor
    · intro a _
      apply List.pairwise_map.mpr
      exact (List.pairwise_lt_finRange t).imp (fun hij => same_copy_order S ray F w hw hxx a _ _ hij)
    · exact (hrows v).imp (by
        intro a b hab x hx y hy
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
        exact different_copy_order S ray F w hxx hcc a b hab i j)
end PlanarHom.ParallelSource
