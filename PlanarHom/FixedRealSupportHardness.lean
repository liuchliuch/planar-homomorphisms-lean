import PlanarHom.FixedRealZeroOneQuotient
import PlanarHom.RealRationalOracleDescent
import PlanarHom.FixedRealSignedTransforms
import PlanarHom.ZeroOneGramBlockClassification
import PlanarHom.ZeroOneGramMatching
import PlanarHom.ZeroOneReducedMatchingLift
import PlanarHom.ZeroOneDifunctionalComponents
import PlanarHom.PositivePottsFoundationClosed

/-! NEW A.9 hard direction. The actual zero-one support is quotiented by actual
identical rows, positive weights are summed, zero classes are removed by the
checked component/root program, and A.8 removes the weights. Hardness comes
from the established integer-valued algebraic zero-one endpoint. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealSupportHardness
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open FixedRealComponents ActualTwins RootedRestriction ZeroOneBasicStructure
open FixedRealApproximation ZeroOneGramBlockClassification ZeroOneGramMatching
variable {n e q:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K) (φ:K→+*ℝ)

theorem zeroOne_basic_of_not_hard (A:Matrix (Fin q) (Fin q) K)
    (hs:∀i j,A i j=A j i) (w:Fin q→K) (hw:∀i,0<φ (w i))
    (h01:∀i j,A i j=0 ∨ A i j=1)
    (hnot:¬RepresentedBit.SharpPHard (problem basis (fun _:Fin 1=>A) (fun i:Fin 0=>i.elim0) w)) :
    ∀c:(colorSupport (fun i j=>φ (A i j)) (fun i j=>congrArg φ (hs i j))).ConnectedComponent,
      BasicZeroOneComponent (fun i j:c.supp=>φ (A i.val j.val)) := by
  letI : CharZero K := φ.charZero
  let B:=reducedMatrix A hs
  have hB01:∀i j,B i j=0 ∨ B i j=1 := by
    intro i j
    rw [show B i j=A (representative A hs i) (representative A hs j) from reducedMatrix_eq_representatives A hs i j]
    exact h01 _ _
  let N:Matrix (Fin (reducedCount A hs)) (Fin (reducedCount A hs)) ℚ:=
    fun i j=>if B i j=0 then 0 else 1
  have hN:∀i j,(N i j:K)=B i j := by
    intro i j
    rcases hB01 i j with h|h <;> simp [N,h]
  let L:=rationalLanguage N
  have hL:(L.matrices 0)=(fun i j=>φ (B i j)) := by
    funext i j
    simpa only [map_ratCast] using congrArg φ (hN i j)
  have hsymm:∀i j,L.matrices 0 i j=L.matrices 0 j i := by
    intro i j
    rw [hL]
    exact congrArg φ (reducedMatrix_symmetric A hs i j)
  have hz:∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1 := by
    intro i j
    rw [hL]
    rcases hB01 i j with h|h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  have hnz:∀i,L.matrices 0 i≠0 := by
    rw [hL]
    exact FixedRealTwins.reduced_image_rows_ne_zero φ A hs
  have hinj:Function.Injective (L.matrices 0) := by
    rw [hL]
    exact FixedRealTwins.reduced_image_rows_injective φ A hs
  have redB:=FixedRealTwins.zeroOneReduction basis φ A hs w hw h01
  have redQ:=rationalOracleDescent basis N
  have hm:(fun _:Fin 1=>fun i j=>(N i j:K))=(fun _:Fin 1=>B) := by
    funext l i j
    exact hN i j
  rw [hm] at redQ
  have red:Reduction (ofCanonical L.problem)
      (problem basis (fun _:Fin 1=>A) (fun i:Fin 0=>i.elim0) w) := redQ.trans redB
  have hnL:¬PromisedSharpPHard L.problem := fun h=>hnot ((RepresentedBit.SharpPHard.ofCanonical h).trans red)
  have hb:=source_blocks AlgebraicProductInterpolation.RealLanguage.positivePottsFoundation L
    (fun _=>rfl) hsymm hz hnz hinj hnL
  have hmatch:=neighbors_unique (L.matrices 0) hsymm hz hb
  have hmatchK:∀i j k,B i j≠0→B i k≠0→j=k := by
    intro i j k hij hik
    apply hmatch i j k
    · rw [hL]
      exact (map_ne_zero φ).mpr hij
    · rw [hL]
      exact (map_ne_zero φ).mpr hik
  have hrows:∀i j k,φ (A i j)≠0→φ (A i k)≠0→
      (fun l=>φ (A j l))=(fun l=>φ (A k l)) := by
    intro i j k hij hik
    have h:=ActualTwins.rows_of_reduced_matching A hs hmatchK i j k
      ((map_ne_zero φ).mp hij) ((map_ne_zero φ).mp hik)
    funext l
    exact congrArg φ (congrFun h l)
  apply ZeroOneDifunctionalComponents.component_basic (fun i j=>φ (A i j))
    (fun i j=>congrArg φ (hs i j))
  · intro i j
    rcases h01 i j with h|h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  · exact hrows

theorem theoremA9_hard (M:Matrix (Fin q) (Fin q) K) (hs:∀i j,M i j=M j i)
    (w:Fin q→K) (hw:∀i,0<φ (w i))
    (hbad:∃c:(colorSupport (fun i j=>φ (M i j)) (fun i j=>congrArg φ (hs i j))).ConnectedComponent,
      ¬BasicZeroOneComponent (fun i j:c.supp=>if φ (M i.val j.val)=0 then 0 else 1)) :
    RepresentedBit.SharpPHard (problem basis (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w) := by
  by_contra hn
  let A:=fun i j=>FixedRealSignedTransforms.support (M i j)
  have hsA:∀i j,A i j=A j i := by intro i j;dsimp [A];rw [hs i j]
  have h01:∀i j,A i j=0 ∨ A i j=1 := by
    intro i j
    by_cases h:M i j=0
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  have hr:=FixedRealSignedTransforms.supportReduction φ basis M (fun i:Fin 0=>i.elim0) w
  have hnA:¬RepresentedBit.SharpPHard (problem basis (fun _:Fin 1=>A) (fun i:Fin 0=>i.elim0) w):=
    fun h=>hn (h.trans hr)
  have hb:=zeroOne_basic_of_not_hard basis φ A hsA w hw h01 hnA
  have hg:colorSupport (fun i j=>φ (A i j)) (fun i j=>congrArg φ (hsA i j))=
      colorSupport (fun i j=>φ (M i j)) (fun i j=>congrArg φ (hs i j)) := by
    ext i j
    change (i≠j ∧ φ (A i j)≠0) ↔ (i≠j ∧ φ (M i j)≠0)
    simp only [A,FixedRealSignedTransforms.support_image]
    by_cases h:φ (M i j)=0 <;> simp [h]
  rw [hg] at hb
  obtain ⟨c,hc⟩:=hbad
  apply hc
  simpa only [A,FixedRealSignedTransforms.support_image] using hb c

end PlanarHom.FixedRealSupportHardness
