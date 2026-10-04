import PlanarHom.RotationFaceCutRegionCycles
import PlanarHom.FinitePermutationCycleProducts
import PlanarHom.OccurrenceKasteleynBoundarySigns

/-! NEW cancellation of internal occurrence pairs in a literal derived face cut.
All permutations and products are taken on actual selected darts. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {A : Finset E} {root : Dart E}
variable (C : R.FaceCut A root)

def InternalEdge (e : E) : Prop := e∉A ∧ C.side (e,true)=true

def internalCount : ℕ := (Finset.univ.filter C.InternalEdge).card

def insideReverse : Equiv.Perm (Dart E) := partialReverse E (fun e=>decide (C.InternalEdge e))

theorem internal_side (a : Dart E) (he : a.1∉A) : C.InternalEdge a.1 ↔ C.side a=true := by
  rcases a with ⟨e,b⟩
  cases b
  · rw [show C.side (e,false)=C.side (e,true) from C.side_reverse_of_notMem (e,true) he]
    simp [InternalEdge,he]
  · simp [InternalEdge,he]

@[simp] theorem side_insideReverse (a : Dart E) : C.side (C.insideReverse a)=C.side a := by
  by_cases he : C.InternalEdge a.1
  · change C.side (if decide (C.InternalEdge a.1) then reversePerm E a else a)=_
    rw [decide_eq_true he,if_pos rfl]
    exact C.side_reverse_of_notMem a he.1
  · simp [insideReverse,partialReverse,he]

theorem insideReverse_support (a : Dart E) (ha : C.insideReverse a≠a) : C.side a=true := by
  by_cases he : C.InternalEdge a.1
  · exact (C.internal_side a he.1).mp he
  · exact False.elim (ha (by simp [insideReverse,partialReverse,he]))

def selectedInsideReverse : Equiv.Perm {a : Dart E // C.side a=true} :=
  C.insideReverse.subtypePerm (fun a=>by rw [C.side_insideReverse])

def selectedFace : Equiv.Perm {a : Dart E // C.side a=true} :=
  R.facePerm.subtypePerm (fun a=>by rw [C.side_facePerm])

theorem selectedFace_eq : C.selectedFace=C.selectedInsideReverse.trans C.selectedContour := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  change R.facePerm a.val=C.cutContour (C.insideReverse a.val)
  by_cases he : a.val.1∈A
  · have hi : ¬C.InternalEdge a.val.1 := fun h=>h.1 he
    have hr : C.insideReverse a.val=a.val := by simp [insideReverse,partialReverse,hi]
    rw [hr,C.cutContour_boundary a.val he]
  · have hi : C.InternalEdge a.val.1 := (C.internal_side a.val he).mpr a.property
    have hr : C.insideReverse a.val=reversePerm E a.val := by simp [insideReverse,partialReverse,hi]
    rw [hr,C.cutContour_nonboundary (reversePerm E a.val) (by exact he)]
    rfl

theorem sign_insideReverse : Equiv.Perm.sign C.insideReverse=(-1:ℤˣ)^C.internalCount := by
  have hp : C.insideReverse=Equiv.prodCongrRight
      (fun e : E=>if C.InternalEdge e then Equiv.swap false true else Equiv.refl Bool) := by
    apply Equiv.ext
    intro a
    rcases a with ⟨e,b⟩
    by_cases h : C.InternalEdge e <;> cases b <;> simp [insideReverse,partialReverse,h,reversePerm]
  rw [hp]
  have ht := Equiv.Perm.sign_prodCongrRight
    (fun e : E=>if C.InternalEdge e then Equiv.swap false true else Equiv.refl Bool)
  have ht' : Equiv.Perm.sign (Equiv.prodCongrRight
    (fun e : E=>if C.InternalEdge e then Equiv.swap false true else Equiv.refl Bool))=
      ∏e : E,Equiv.Perm.sign (if C.InternalEdge e then Equiv.swap false true else Equiv.refl Bool) := by
    convert ht using 1
    congr
    exact Subsingleton.elim _ _
  rw [ht']
  have hs : ∀e : E,Equiv.Perm.sign (if C.InternalEdge e then Equiv.swap false true else Equiv.refl Bool)=
      if C.InternalEdge e then (-1:ℤˣ) else 1 := by
    intro e
    split_ifs <;> simp [Equiv.Perm.sign_swap (by decide : (false:Bool)≠true)]
  simp_rw [hs]
  rw [←Finset.prod_filter]
  simp [internalCount]

theorem sign_selectedInsideReverse : Equiv.Perm.sign C.selectedInsideReverse=(-1:ℤˣ)^C.internalCount := by
  rw [selectedInsideReverse,Equiv.Perm.sign_subtypePerm C.insideReverse _ C.insideReverse_support,
    C.sign_insideReverse]

def cutBoundaryProduct (orientation : E→Bool) : ℤ :=
  ∏e : E,if e∈A then (if C.side (e,true) then dartSign orientation (e,true) else dartSign orientation (e,false)) else 1

theorem selected_product (orientation : E→Bool) :
    (∏a : {a : Dart E // C.side a=true},dartSign orientation a.val)=
      (-1:ℤ)^C.internalCount*C.cutBoundaryProduct orientation := by
  rw [←Finset.prod_subtype (Finset.univ.filter (fun a : Dart E=>C.side a=true)) (by simp)]
  rw [Finset.prod_filter,Fintype.prod_prod_type]
  have hpair : ∀e : E,(∏b : Bool,if C.side (e,b)=true then dartSign orientation (e,b) else 1)=
      (if C.InternalEdge e then (-1:ℤ) else 1)*
      (if e∈A then (if C.side (e,true) then dartSign orientation (e,true) else dartSign orientation (e,false)) else 1) := by
    intro e
    have hc := C.crosses e
    change (C.side (e,true) ^^ C.side (e,false))=decide (e∈A) at hc
    by_cases he : e∈A <;> cases ht : C.side (e,true) <;> cases hf : C.side (e,false) <;>
      simp_all [Fintype.prod_bool,InternalEdge,dartSign]
    all_goals cases orientation e <;> norm_num
  simp_rw [hpair]
  rw [Finset.prod_mul_distrib,←Finset.prod_filter]
  simp only [Finset.prod_const,internalCount,cutBoundaryProduct]

theorem selected_card : Fintype.card {a : Dart E // C.side a=true}=2*C.internalCount+A.card := by
  rw [Fintype.card_subtype,Finset.card_filter,Fintype.sum_prod_type]
  have hpair : ∀e : E,(∑b : Bool,if C.side (e,b)=true then (1:ℕ) else 0)=
      2*(if C.InternalEdge e then 1 else 0)+(if e∈A then 1 else 0) := by
    intro e
    have hc := C.crosses e
    change (C.side (e,true) ^^ C.side (e,false))=decide (e∈A) at hc
    rw [Fintype.sum_bool]
    by_cases he : e∈A <;> cases ht : C.side (e,true) <;> cases hf : C.side (e,false) <;>
      simp_all [InternalEdge]
  simp_rw [hpair]
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  have hi : (∑e : E,if C.InternalEdge e then (1:ℕ) else 0)=C.internalCount := by
    rw [internalCount,Finset.card_filter]
  rw [hi]
  simp

/-- Internal opposite darts cancel exactly the internal reversal sign. -/
theorem cutBoundaryProduct_eq_sign (orientation : E→Bool)
    (hfaces : FinitePermutationCycles.CycleProductLaw C.selectedFace (fun a=>dartSign orientation a.val)) :
    C.cutBoundaryProduct orientation=(Equiv.Perm.sign C.selectedContour : ℤ) := by
  have hp := FinitePermutationCycles.product_eq_sign C.selectedFace (fun a=>dartSign orientation a.val) hfaces
  rw [C.selected_product orientation,C.selectedFace_eq,Equiv.Perm.sign_trans,
    C.sign_selectedInsideReverse] at hp
  norm_cast at hp
  have hn : (-1:ℤ)^C.internalCount≠0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hn
  simpa only [mul_comm] using hp

set_option maxHeartbeats 1000000 in
/-- Restrict the actual full face equations to the derived side, which excludes
its normalized omitted face. -/
theorem selectedFace_productLaw_of_except (orientation : E→Bool)
    (hfaces : ∀q : R.Face,q≠R.faceOf root →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1)) :
    FinitePermutationCycles.CycleProductLaw C.selectedFace (fun a=>dartSign orientation a.val) := by
  unfold selectedFace
  refine FinitePermutationCycles.cycleProductLaw_subtype R.facePerm (dartSign orientation)
    (fun a=>C.side a=true) (fun a=>by
      change C.side (R.facePerm a)=true ↔ C.side a=true
      rw [C.side_facePerm]) ?_
  intro q hq
  apply hfaces q
  intro he
  obtain ⟨a,ha,hclass⟩ := hq
  have hroot : R.faceOf a=R.faceOf root := hclass.trans he
  have hs : C.side a=false := by
    rw [side,hroot,C.root_false]
  rw [hs] at ha
  contradiction

end PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
