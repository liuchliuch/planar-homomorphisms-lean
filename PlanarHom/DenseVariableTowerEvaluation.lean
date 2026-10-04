import PlanarHom.DenseVariableBasisTower
import PlanarHom.RationalVariableAdjoin
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-! NEW evaluation of the concrete rational-variable tower at an actual
finite algebraically independent family. Its image is exactly the generated
intermediate field, and all original coefficients are fixed. -/
noncomputable section
open Classical
open scoped Polynomial
namespace PlanarHom.DenseVariableBasis
attribute [local instance] Polynomial.algebra

 def fractionMap {F A:Type} [Field F] [Field A] (e:F≃+*A) :
    FractionRing F[X]≃+*FractionRing A[X] :=
  IsFractionRing.ringEquivOfRingEquiv (Polynomial.mapEquiv e)

 theorem fractionMap_coefficient {F A:Type} [Field F] [Field A] (e:F≃+*A) (r:F) :
    fractionMap e (algebraMap F (FractionRing F[X]) r)=
      algebraMap A (FractionRing A[X]) (e r) := by
  change fractionMap e (algebraMap F[X] (FractionRing F[X]) (Polynomial.C r))=_
  rw [fractionMap,IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp only [Polynomial.mapEquiv_apply,Polynomial.map_C]
  rfl

variable {F E:Type} [Field F] [Field E] [Algebra F E]

 theorem exists_evaluation_equiv (b:ℕ) (y:Fin b→E) (hy:AlgebraicIndependent F y) :
    ∃i:Tower F b≃+*IntermediateField.adjoin F (Set.range y),
      ∀r:F,(i (embedding F b r):E)=algebraMap F E r := by
  induction b with
  | zero=>
    have hs:IntermediateField.adjoin F (Set.range y)=⊥:=by simp
    let i: F≃ₐ[F]IntermediateField.adjoin F (Set.range y):=
      (IntermediateField.botEquiv F E).symm.trans (IntermediateField.equivOfEq hs.symm)
    refine ⟨i.toRingEquiv,?_⟩
    intro r
    exact congrArg Subtype.val (i.commutes r)
  | succ b ih=>
    let x:Fin b→E:=fun i=>y i.castSucc
    have hx:AlgebraicIndependent F x:=hy.comp Fin.castSucc (Fin.castSucc_injective b)
    obtain ⟨i,hi⟩:=ih x hx
    let A:=IntermediateField.adjoin F (Set.range x)
    have ht:Transcendental A (y (Fin.last b)):=by
      apply IntermediateField.transcendental_adjoin_iff.mpr
      have hh:=hy.transcendental_adjoin (s:=Set.range (Fin.castSucc:Fin b→Fin (b+1)))
        (i:=Fin.last b) (by simp)
      rw [←Set.range_comp' y (Fin.castSucc:Fin b→Fin (b+1))] at hh
      exact hh
    have hrange:Set.range y=Set.range x∪{y (Fin.last b)}:=by
      ext z
      constructor
      · rintro ⟨j,rfl⟩
        refine Fin.lastCases ?_ (fun k=>?_) j
        · exact Or.inr rfl
        · exact Or.inl ⟨k,rfl⟩
      · rintro (⟨j,rfl⟩|rfl)
        · exact ⟨j.castSucc,rfl⟩
        · exact ⟨Fin.last b,rfl⟩
    have hadjoin:(IntermediateField.adjoin A {y (Fin.last b)}).restrictScalars F=
        IntermediateField.adjoin F (Set.range y):=by
      rw [IntermediateField.adjoin_adjoin_left,hrange]
    let j:Tower F (b+1)≃+*IntermediateField.adjoin F (Set.range y):=
      ((fractionMap i).trans (RationalVariableBasis.evaluateEquiv (y (Fin.last b)) ht)).trans
        (IntermediateField.equivOfEq hadjoin).toRingEquiv
    refine ⟨j,?_⟩
    intro r
    change (RationalVariableBasis.evaluateEquiv (y (Fin.last b)) ht
      (fractionMap i (algebraMap (Tower F b) (FractionRing (Tower F b)[X]) (embedding F b r))):E)=_
    rw [fractionMap_coefficient,RationalVariableBasis.evaluateEquiv_coefficient]
    exact hi r

 def evaluationEquiv {b:ℕ} (y:Fin b→E) (hy:AlgebraicIndependent F y) :
    Tower F b≃+*IntermediateField.adjoin F (Set.range y) :=
  (exists_evaluation_equiv b y hy).choose

 theorem evaluationEquiv_coefficient {b:ℕ} (y:Fin b→E) (hy:AlgebraicIndependent F y) (r:F) :
    (evaluationEquiv y hy (embedding F b r):E)=algebraMap F E r :=
  (exists_evaluation_equiv b y hy).choose_spec r

 def evaluationEmbedding {b:ℕ} (y:Fin b→E) (hy:AlgebraicIndependent F y) : Tower F b→+*E :=
  (IntermediateField.adjoin F (Set.range y)).subtype.comp (evaluationEquiv y hy).toRingHom

 theorem evaluationEmbedding_coefficient {b:ℕ} (y:Fin b→E) (hy:AlgebraicIndependent F y) (r:F) :
    evaluationEmbedding y hy (embedding F b r)=algebraMap F E r :=
  evaluationEquiv_coefficient y hy r

 theorem evaluationEmbedding_range {b:ℕ} (y:Fin b→E) (hy:AlgebraicIndependent F y) :
    Set.range (evaluationEmbedding y hy)=(IntermediateField.adjoin F (Set.range y):Set E) := by
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    exact (evaluationEquiv y hy a).property
  · intro hz
    obtain ⟨a,ha⟩:=(evaluationEquiv y hy).surjective ⟨z,hz⟩
    exact ⟨a,congrArg Subtype.val ha⟩

end PlanarHom.DenseVariableBasis
