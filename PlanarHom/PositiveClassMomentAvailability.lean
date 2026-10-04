-- Recovered proof bodies; the identical endpoint-unary call uses the new sameReduction API.
import PlanarHom.PositiveClassMomentRigidity
import PlanarHom.PositiveUnaryPowerJointAvailability
import PlanarHom.WeightedGramAvailability
import PlanarHom.EndpointUnaryGauge

/-! Actual retained-language realization of the class-moment matrix. The
unit-background premise is essential: before background removal, the internal
path vertex contributes the original weight, and the core is C diag(w) C.
The positive unary is a named existing label; this module does not assume
that a weighted source automatically provides the same unary with unit weight. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PositiveClassMomentRigidity
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage Complexity Complexity.MixedCode
open FiniteLanguageAliases PositiveUnaryRationalPowers PositiveWeightRemoval
variable {q bt ut : ℕ}

theorem square_algebraic (C : Matrix (Fin q) (Fin q) ℝ)
    (hC : ∀ i j,IsAlgebraic ℚ (C i j)) : ∀ i j,IsAlgebraic ℚ ((C*C) i j) := by
  intro i j
  change IsAlgebraic ℚ (∑ k,C i k*C k j)
  suffices ∀ s : Finset (Fin q),IsAlgebraic ℚ (∑ k∈s,C i k*C k j) by simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (isAlgebraic_zero : IsAlgebraic ℚ (0:ℝ))
  | @insert a s ha hs =>
    simp only [Finset.sum_insert ha]
    exact (hC i a |>.mul (hC a j)).add hs

theorem momentSquare_algebraic (C : Matrix (Fin q) (Fin q) ℝ)
    (hC : ∀ i j,IsAlgebraic ℚ (C i j)) (μ : Fin q → ℝ)
    (hμ : ∀ i,0≤μ i) (hμa : ∀ i,IsAlgebraic ℚ (μ i)) :
    ∀ i j,IsAlgebraic ℚ (momentSquare C μ i j) := by
  intro i j
  rw [momentSquare,PositiveRealCore.decorated_entry]
  exact ((BooleanPDNormalization.isAlgebraic_sqrt (hμ i) (hμa i)).mul
    (square_algebraic C hC i j)).mul
    (BooleanPDNormalization.isAlgebraic_sqrt (hμ j) (hμa j))

/-- A two-edge path and two endpoint square-root unaries give the literal
moment square, retaining arbitrary fixed binary and unary companions. All
canonical field changes and added-label elimination are actual reductions. -/
theorem momentSquare_append_available (L : RealLanguage q bt ut)
    (hunit : ∀ i,L.weights i=1) (old : Fin bt) (selected : Fin ut)
    (hμ : ∀ i,0<L.unaries selected i) :
    Nonempty (PromisePolyTimeTuringReduction
      (L.appendBinary (momentSquare (L.matrices old) (L.unaries selected))
        (momentSquare_algebraic _ (L.matrices_algebraic old) _
          (fun i=>(hμ i).le) (L.unaries_algebraic selected))).problem L.problem) := by
  obtain ⟨K,h₀,hK,v,hv,_,_,_⟩ := exists_fixed_power_overfield L.field
    (L.unariesK selected) hμ (1/2 : ℚ)
  letI : FiniteDimensional ℚ K := hK
  let bK := Module.finBasis ℚ K
  let MF : Fin bt → Matrix (Fin q) (Fin q) K :=
    fun l i j=>IntermediateField.inclusion h₀ (L.matricesK l i j)
  let UF : Fin (ut+1) → Fin q → K :=
    appendOne (fun l i=>IntermediateField.inclusion h₀ (L.unariesK l i)) v
  let wF : Fin q → K := fun i=>IntermediateField.inclusion h₀ (L.weightsK i)
  have hv' : ∀ i,(v i:ℝ)=Real.sqrt (L.unaries selected i) := by
    intro i
    rw [hv i,Real.sqrt_eq_rpow]
    norm_num
  have hw : wF=fun _=>1 := by
    funext i
    exact Subtype.ext (hunit i)
  let S := gramCoreField (MF old) wF 1
  have hs : ∀ i j,(S i j:ℝ)=(L.matrices old*L.matrices old) i j := by
    intro i j
    simp [S,gramCoreField,hw,Matrix.mul_apply,MF]
  let N := EndpointUnaryGauge.decorated S v v
  have hn : ∀ i j,(N i j:ℝ)=momentSquare (L.matrices old) (L.unaries selected) i j := by
    intro i j
    simp only [N,EndpointUnaryGauge.decorated,IntermediateField.coe_mul,hs,hv',
      momentSquare,PositiveRealCore.decorated_entry]
  let A := appendOne (appendOne MF S) N
  let rb : Fin (bt+1) → Fin (bt+1+1) :=
    Fin.addCases (fun k=>Fin.castAdd 1 (Fin.castAdd 1 k)) (fun _=>Fin.last (bt+1))
  let T := L.appendBinary (momentSquare (L.matrices old) (L.unaries selected))
    (momentSquare_algebraic _ (L.matrices_algebraic old) _
      (fun i=>(hμ i).le) (L.unaries_algebraic selected))
  have present := T.presentationDescentReduction K bK (A ∘ rb)
    (UF ∘ Fin.castAdd 1) wF (by
      intro l
      refine Fin.addCases (fun k=>?_) (fun k=>?_) l
      · intro i j
        simp only [Function.comp_apply,A,rb,Fin.addCases_left,appendOne_old,T,appendBinary,MF]
        rfl
      · intro i j
        have hk : k=(0:Fin 1) := Subsingleton.elim _ _
        subst k
        simp only [Function.comp_apply,rb,Fin.addCases_right]
        rw [show Fin.natAdd bt (0:Fin 1)=Fin.last bt from Fin.ext rfl]
        simpa only [A,T,appendBinary,appendOne_aux] using hn i j)
    (by intro l i; simp only [Function.comp_apply,UF,appendOne_old]; rfl)
    (fun _=>rfl)
  have aliases := (binaryRelabelReduction bK rb A (UF ∘ Fin.castAdd 1) wF).trans
    (unaryRelabelReduction bK (Fin.castAdd 1) A UF wF)
  have gauge := EndpointUnaryGauge.sameReduction bK (appendOne MF S) UF wF
    (Fin.last bt) (Fin.last ut)
  simp only [appendOne_aux,UF] at gauge
  have gram := gramAppendReduction bK MF UF wF old 1
  have power := appendedPowerReduction L.basis bK h₀ L.matricesK L.unariesK L.weightsK
    selected hμ (1/2 : ℚ) v hv
  exact ⟨present.trans (aliases.trans (gauge.trans (gram.trans power)))⟩

end PlanarHom.PositiveClassMomentRigidity
