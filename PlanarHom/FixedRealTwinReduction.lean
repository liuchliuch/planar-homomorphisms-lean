import PlanarHom.FixedRealPrescribedWeightRemoval
import PlanarHom.FixedRealSupportRestriction
import PlanarHom.ActualTwinRemoval
import Mathlib.Algebra.Order.Ring.InjSurj

/-! NEW actual-row quotient and nonzero-row extraction in the represented real
model. Exact quotient weights are summed over genuine row classes. The actual
component/root restriction program preserves every isolated input vertex. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealTwins
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open ActualTwins FixedRealComponents
variable {n e:ℕ} {K C D:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C] [Fintype D]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def homogeneousIdentityReduction (M:Matrix C C K) (w:C→K) (N:Matrix D D K) (v:D→K)
    (he:∀g:MixedCode,∀hg:g.Valid 1 0,
      (g.toMultiGraph hg).partition M w=(g.toMultiGraph hg).partition N v) :
    Reduction (problem basis (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w)
      (problem basis (fun _:Fin 1=>N) (fun i:Fin 0=>i.elim0) v) := by
  apply queryReduction (presentation basis) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
    (PlanarValid 1 0) (PlanarValid 1 0)
    (totalEvaluation (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w)
    (totalEvaluation (fun _:Fin 1=>N) (fun i:Fin 0=>i.elim0) v) id (fp_id MixedCode.encoding)
  · intro g hg;exact hg
  · intro g hg
    simp only [id_eq,totalEvaluation_valid _ _ _ g hg.1,evaluate_homogeneous]
    exact (he g hg.1).symm

def quotientReduction (A:Matrix C C K) (hs:∀i j,A i j=A j i) (w:C→K) :
    Reduction (problem basis (fun _:Fin 1=>Twins.quotientMatrix A hs) (fun i:Fin 0=>i.elim0) (Twins.quotientWeight A w))
      (problem basis (fun _:Fin 1=>A) (fun i:Fin 0=>i.elim0) w) :=
  homogeneousIdentityReduction basis _ _ A w
    (fun g hg=>(Twins.partition_canonicalQuotient (g.toMultiGraph hg) A w hs).symm)

def reindexReduction (M:Matrix D D K) (w:D→K) (f:C≃D) :
    Reduction (problem basis (fun _:Fin 1=>fun i j=>M (f i) (f j)) (fun i:Fin 0=>i.elim0) (fun i=>w (f i)))
      (problem basis (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w) :=
  homogeneousIdentityReduction basis _ _ M w
    (fun g hg=>(g.toMultiGraph hg).partition_reindexColors M w f)

variable [LinearOrder K] [IsStrictOrderedRing K]

def weightedReducedReduction (A:Matrix C C K) (hs:∀i j,A i j=A j i)
    (w:C→K) (hw:∀i,0<w i) :
    Reduction (problem basis (fun _:Fin 1=>reducedMatrix A hs) (fun i:Fin 0=>i.elim0) (reducedWeight A hs w))
      (problem basis (fun _:Fin 1=>A) (fun i:Fin 0=>i.elim0) w) := by
  let R:=Twins.quotientMatrix A hs
  let v:=Twins.quotientWeight A w
  have hR:∀i j,R i j=R j i:=Twins.quotientMatrix_symmetric A hs
  have hv:∀i,0<v i:=Twins.quotientWeight_pos A w hw
  let first:=reindexReduction basis (Twins.nonzeroMatrix R) (fun i:Twins.nonzeroColor R=>v i.val) (reducedIndex A hs)
  let second:=FixedRealRootRestriction.submatrixReduction basis R hR v hv (Twins.nonzeroColor R)
    (Twins.nonzeroColor_colorClosed R hR)
  exact first.trans (second.trans (quotientReduction basis A hs w))

end PlanarHom.FixedRealTwins
