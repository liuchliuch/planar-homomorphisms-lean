import PlanarHom.FixedSubfieldRepresentationChoices
import PlanarHom.FixedSubfieldDescentAssembly
import PlanarHom.DenseVariableTowerEvaluation

/-! NEW: general prescribed-subfield descent. The relative transcendence basis,
compatible rational-variable tower and finite ambient basis are constructed from
the fixed presentations. The conversion program is the actual compiled
presentation-change/trace/coefficient chain. -/
noncomputable section
open Classical
namespace PlanarHom.GeneralFixedSubfieldDescent
open DensePolynomial Complexity DenseVariableBasis FixedSubfieldRepresentationChoices
variable {d e c f : ℕ} {K F : Type} [Field K] [Field F]
  [Algebra (RationalFunction d) K] [Algebra (RationalFunction c) F]

theorem exists_conversion
    (source : Module.Basis (Fin e) (RationalFunction d) K)
    (target : Module.Basis (Fin f) (RationalFunction c) F) (embed : F →+* K) :
    ∃ convert : FixedRealExtension.Code d e → FixedRealExtension.Code c f,
      FP (FixedRealExtension.encoding d e) (FixedRealExtension.encoding c f) convert ∧
      ∀ a, FixedRealExtension.Valid d a → ∀ z : F, FixedRealExtension.value source a = embed z →
        FixedRealExtension.Valid c (convert a) ∧ FixedRealExtension.value target (convert a) = z := by
  letI : Algebra F K := embed.toAlgebra
  obtain ⟨b,y,hy,hfd⟩ := exists_relative_family source embed
  let L := Tower F b
  let A := IntermediateField.adjoin F (Set.range y)
  let equiv : L ≃+* A := evaluationEquiv y hy.1
  letI : Algebra L A := equiv.toRingHom.toAlgebra
  letI : Algebra L K := (A.subtype.comp equiv.toRingHom).toAlgebra
  letI : IsScalarTower L A K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : FiniteDimensional L A := Module.Finite.of_surjective (Algebra.linearMap L A) equiv.surjective
  letI : FiniteDimensional A K := hfd
  letI : FiniteDimensional L K := Module.Finite.trans A K
  letI : Algebra (RationalFunction (c+b)) L := towerAlgebra c F b
  letI : Algebra (RationalFunction (c+b)) K :=
    ((algebraMap L K).comp (algebraMap (RationalFunction (c+b)) L)).toAlgebra
  letI : IsScalarTower (RationalFunction (c+b)) L K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : CharZero L := sourceCharZero (c+b) L
  let auxiliary : Module.Basis (Fin f) (RationalFunction (c+b)) L := towerBasis target b
  let convert := FixedSubfieldDescentAssembly.run source auxiliary
  refine ⟨convert,FixedSubfieldDescentAssembly.fp_run source auxiliary,?_⟩
  intro a ha z hz
  refine ⟨FixedSubfieldDescentAssembly.run_valid source auxiliary a,?_⟩
  have hcoefficient : algebraMap L K (embedding F b z) = embed z :=
    evaluationEmbedding_coefficient y hy.1 z
  exact FixedSubfieldDescentAssembly.run_value source target auxiliary (embedding F b)
    (tower_compatible target b) a z (hz.trans hcoefficient.symm)

end PlanarHom.GeneralFixedSubfieldDescent
