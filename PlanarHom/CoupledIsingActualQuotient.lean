import PlanarHom.CoupledIsingCharacterMap
import PlanarHom.BinaryCharacterExponential
import PlanarHom.WeightedStructureTransport
import PlanarHom.Quotient

/-! Literal coupled-Ising actual-row quotient and its exact positive fiber
weights. No graph reduction, hardness premise, or quotient promise is supplied. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.CoupledIsing
open BinaryCharacters Structures
variable {n m:ℕ}

def interaction (a:Fin m→Space n) (J:Fin m→ℝ) : Matrix (Space n) (Space n) ℝ :=
  BinaryCharacters.interaction (fun r=>functional (a r)) J

def quotientInteraction (a:Fin m→Space n) (J:Fin m→ℝ) : Matrix (ImageSpace a) (ImageSpace a) ℝ :=
  BinaryCharacters.interaction (coordinate a) J

theorem symmetric (a:Fin m→Space n) (J:Fin m→ℝ) (x y:Space n) :
    interaction a J x y=interaction a J y x := interaction_symmetric _ _ _ _

theorem pullback (a:Fin m→Space n) (J:Fin m→ℝ) (x y:Space n) :
    interaction a J x y=quotientInteraction a J (toImage a x) (toImage a y) := rfl

theorem quotient_rows_injective (a:Fin m→Space n) (ha:Function.Injective a)
    (J:Fin m→ℝ) (hJ:∀r,J r≠0) : Function.Injective (quotientInteraction a J) := by
  intro x y h
  apply Subtype.ext
  funext r
  exact ((BinaryCharacters.equal_rows_iff (coordinate a) (coordinate_injective a ha) J hJ x y).mp h) r

theorem rows_iff (a:Fin m→Space n) (ha:Function.Injective a)
    (J:Fin m→ℝ) (hJ:∀r,J r≠0) (x y:Space n) :
    interaction a J x=interaction a J y ↔ toImage a x=toImage a y := by
  constructor
  · intro h
    apply quotient_rows_injective a ha J hJ
    funext z
    obtain ⟨v,rfl⟩:=toImage_surjective a z
    exact congrFun h v
  · intro h
    funext z
    rw [pullback,pullback,h]

def rowQuotientMap (a:Fin m→Space n) (ha:Function.Injective a)
    (J:Fin m→ℝ) (hJ:∀r,J r≠0) : Quotient (Twins.rowSetoid (interaction a J))→ImageSpace a :=
  Quotient.lift (toImage a) (fun x y h=>(rows_iff a ha J hJ x y).mp (funext h))

def rowQuotientEquiv (a:Fin m→Space n) (ha:Function.Injective a)
    (J:Fin m→ℝ) (hJ:∀r,J r≠0) : Quotient (Twins.rowSetoid (interaction a J))≃ImageSpace a :=
  Equiv.ofBijective (rowQuotientMap a ha J hJ) ⟨by
    intro x y
    induction x using Quotient.inductionOn with
    | h x=>
      induction y using Quotient.inductionOn with
      | h y=>
        intro h
        exact Quotient.sound (congrFun ((rows_iff a ha J hJ x y).mpr h)),by
    intro z
    obtain ⟨x,hx⟩:=toImage_surjective a z
    exact ⟨Quotient.mk _ x,hx⟩⟩

@[simp] theorem rowQuotientEquiv_mk (a:Fin m→Space n) (ha:Function.Injective a)
    (J:Fin m→ℝ) (hJ:∀r,J r≠0) (x:Space n) :
    rowQuotientEquiv a ha J hJ (Quotient.mk _ x)=toImage a x := rfl

def aggregatedWeight (a:Fin m→Space n) (w:Space n→ℝ) (z:ImageSpace a) : ℝ :=
  ∑x:{x//toImage a x=z},w x.val

theorem aggregatedWeight_positive (a:Fin m→Space n) (w:Space n→ℝ) (hw:∀x,0 < w x)
    (z:ImageSpace a) : 0 < aggregatedWeight a w z := by
  obtain ⟨x,hx⟩:=toImage_surjective a z
  haveI:Nonempty {x//toImage a x=z}:=⟨⟨x,hx⟩⟩
  exact Finset.sum_pos (fun i hi=>hw i.val) Finset.univ_nonempty

theorem quotientMatrix_transport (a:Fin m→Space n) (ha:Function.Injective a)
    (J:Fin m→ℝ) (hJ:∀r,J r≠0) (z t:ImageSpace a) :
    Twins.quotientMatrix (interaction a J) (symmetric a J)
      ((rowQuotientEquiv a ha J hJ).symm z) ((rowQuotientEquiv a ha J hJ).symm t)=
      quotientInteraction a J z t := by
  have hh:∀x y,Twins.quotientMatrix (interaction a J) (symmetric a J) x y=
      quotientInteraction a J (rowQuotientEquiv a ha J hJ x) (rowQuotientEquiv a ha J hJ y) := by
    intro x y
    induction x using Quotient.inductionOn with
    | h x=>
      induction y using Quotient.inductionOn with
      | h y=>rfl
  simpa only [Equiv.apply_symm_apply] using hh
    ((rowQuotientEquiv a ha J hJ).symm z) ((rowQuotientEquiv a ha J hJ).symm t)

theorem quotientWeight_transport (a:Fin m→Space n) (ha:Function.Injective a)
    (J:Fin m→ℝ) (hJ:∀r,J r≠0) (w:Space n→ℝ) (z:ImageSpace a) :
    Twins.quotientWeight (interaction a J) w ((rowQuotientEquiv a ha J hJ).symm z)=aggregatedWeight a w z := by
  let e:=rowQuotientEquiv a ha J hJ
  let ef:{x//Quotient.mk (Twins.rowSetoid (interaction a J)) x=e.symm z}≃{x//toImage a x=z}:=
    Equiv.subtypeEquivRight (fun x=>e.apply_eq_iff_eq_symm_apply.symm)
  exact Fintype.sum_equiv ef _ _ (fun _=>rfl)

theorem weighted_class_iff_quotient (a:Fin m→Space n) (ha:Function.Injective a)
    (J:Fin m→ℝ) (hJ:∀r,J r≠0) (w:Space n→ℝ) :
    PositiveVertexWeightClass (interaction a J) w (symmetric a J) ↔
      WeightedClass (quotientInteraction a J) (aggregatedWeight a w) := by
  let e:=(rowQuotientEquiv a ha J hJ).symm
  have hm:(fun i j=>Twins.quotientMatrix (interaction a J) (symmetric a J) (e i) (e j))=quotientInteraction a J:=
    funext (fun i=>funext (quotientMatrix_transport a ha J hJ i))
  have hw:(fun i=>Twins.quotientWeight (interaction a J) w (e i))=aggregatedWeight a w:=
    funext (quotientWeight_transport a ha J hJ w)
  constructor
  · intro h
    have h':=h.equiv e
    rwa [hm,hw] at h'
  · intro h
    apply WeightedClass.of_equiv e
    rwa [hm,hw]

end PlanarHom.CoupledIsing
