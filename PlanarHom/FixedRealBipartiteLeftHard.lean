import PlanarHom.FixedRealClosedBlockHardness
import PlanarHom.FixedRealSquareRootGramSource
import PlanarHom.BipartiteTensorWeightAvailability

/-! The actual left-side Gram reduction for arbitrary fixed real bipartite
sources. Closed support restriction is performed on ordinary planar inputs;
there is no freely supplied bipartition or target-tractability premise. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealBipartiteLeftHard
open DensePolynomial Complexity FixedRealExtension RepresentedBit FixedRealMixedInterpolation
open RelativeWeightedSpectralField PositiveRealCore BipartiteTensorWeight
variable {n e:ℕ} {F I:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]
  [Fintype I] [DecidableEq I]

def double (B:Matrix I I F) : Matrix (I⊕I) (I⊕I) F := Matrix.fromBlocks 0 B B.transpose 0

def realB (B:Matrix I I F) : Matrix I I ℝ := fun i j=>algebraMap F ℝ (B i j)
def realW (w:I→F) : I→ℝ := fun i=>algebraMap F ℝ (w i)

def problem (basis:Module.Basis (Fin e) (RationalFunction n) F) (B:Matrix I I F) (μ ν:I→F) : Problem :=
  FixedRealComponents.problem basis (fun _:Fin 1=>double B) (fun l:Fin 0=>l.elim0) (Sum.elim μ ν)

theorem double_real (B:Matrix I I F) (i j:I⊕I) : algebraMap F ℝ (double B i j)=doubleMatrix (realB B) i j := by
  cases i <;> cases j <;> simp [double,doubleMatrix,realB]

theorem left_hard (basis:Module.Basis (Fin e) (RationalFunction n) F)
    (B:Matrix I I F) (μ ν:I→F) (hμ:∀i,0<realW μ i) (hν:∀i,0<realW ν i)
    (hB:IsUnit (realB B))
    (hpd:(leftGram (realB B) (realW μ) (realW ν)).PosDef)
    (hp:∀i j,0<leftGram (realB B) (realW μ) (realW ν) i j)
    (hnon:∃i j,leftGram (realB B) (realW μ) (realW ν) i i≠leftGram (realB B) (realW μ) (realW ν) j j) :
    SharpPHard (problem basis B μ ν) := by
  let order:Fin (Fintype.card (I⊕I))≃I⊕I:=(Fintype.equivFin _).symm
  let M:Matrix (Fin (Fintype.card (I⊕I))) (Fin (Fintype.card (I⊕I))) F:=fun i j=>double B (order i) (order j)
  let w:=fun i=>Sum.elim μ ν (order i)
  have hm:∀i j,realMatrix M i j=doubleMatrix (realB B) (order i) (order j) :=fun i j=>double_real B _ _
  have hwval:∀i,realWeights w i=Sum.elim (realW μ) (realW ν) (order i) := by
    intro i
    change algebraMap F ℝ (Sum.elim μ ν (order i))=_
    cases order i <;> rfl
  have hw:∀i,0<realWeights w i := by
    intro i
    rw [hwval]
    cases order i with | inl x=>exact hμ x | inr x=>exact hν x
  have hs:∀i j,realMatrix M i j=realMatrix M j i := by
    intro i j
    rw [hm,hm]
    exact congrFun (congrFun (doubleMatrix_transpose (realB B)) (order j)) (order i)
  have hnz:∀i,realMatrix M i≠0 := by
    intro i hz
    apply doubleMatrix_rows_nonzero (realB B) hB (order i)
    funext j
    have he:=congrFun hz (order.symm j)
    simpa only [hm,Equiv.apply_symm_apply,Pi.zero_apply] using he
  have hproj:∀i j,i≠j→∀t:ℝ,realMatrix M i≠t • realMatrix M j := by
    intro i j hij t he
    apply doubleMatrix_rows_nonproportional (realB B) hB (order.injective.ne hij) t
    funext k
    have hh:=congrFun he (order.symm k)
    simpa only [hm,Equiv.apply_symm_apply,Pi.smul_apply] using hh
  let P:=FixedRealSquareRootGram.model basis w hw
  let S:=FixedRealSquareRootGram.square basis M w hw
  let GX:=leftGram (realB B) (realW μ) (realW ν)
  let GY:=rightGram (realB B) (realW μ) (realW ν)
  have hd:PositiveRealCore.decorated (realMatrix M) (realWeights w) (realWeights w)=
      (doubleMatrix (PositiveRealCore.decorated (realB B) (realW μ) (realW ν))).submatrix order order := by
    ext i j
    rw [decorated_entry,hm,hwval,hwval]
    rw [←decorated_doubleMatrix]
    exact (decorated_entry _ _ _ (order i) (order j)).symm
  have hSR:(fun i j=>algebraMap P.Carrier ℝ (S i j))=
      (Matrix.fromBlocks GX 0 0 GY).submatrix order order := by
    rw [FixedRealSquareRootGram.square_real,hd,pow_two,Matrix.submatrix_mul_equiv _ _ order order order,
      doubleMatrix_square]
    rfl
  have hentry:∀i j,algebraMap P.Carrier ℝ (S i j)=Matrix.fromBlocks GX 0 0 GY (order i) (order j) :=
    fun i j=>congrFun (congrFun hSR i) j
  have htrans:(Matrix.fromBlocks GX 0 0 GY).transpose=Matrix.fromBlocks GX 0 0 GY := by
    simp [GX,GY,leftGram,rightGram,Matrix.fromBlocks_transpose,Matrix.transpose_mul]
  have hS:∀i j,S i j=S j i := by
    intro i j
    apply (algebraMap P.Carrier ℝ).injective
    rw [hentry,hentry]
    exact congrFun (congrFun htrans (order j)) (order i)
  let X:=leftSupport order
  let coord:=leftCoordinate order
  have hclosed:RootedRestriction.ColorClosed S X := by
    intro i hi j hij
    obtain ⟨x,rfl⟩:=hi
    cases hj:order j with
    | inl y=>exact ⟨y,by change order.symm (Sum.inl y)=j; rw [←hj,Equiv.symm_apply_apply]⟩
    | inr y=>
      apply False.elim
      apply hij
      apply (algebraMap P.Carrier ℝ).injective
      rw [map_zero,hentry]
      simp [hj]
  have hblock:(fun i j=>algebraMap P.Carrier ℝ (FixedRealClosedBlockHardness.block S X i j))=
      Matrix.reindex coord.symm coord.symm GX := by
    ext i j
    change algebraMap P.Carrier ℝ (S _ _)=GX (coord i) (coord j)
    rw [hentry]
    simp only [X,coord,leftCoordinate_value,Matrix.fromBlocks_apply₁₁]
  have hpdB:(show Matrix (Fin (Fintype.card X)) (Fin (Fintype.card X)) ℝ from
      fun i j=>algebraMap P.Carrier ℝ (FixedRealClosedBlockHardness.block S X i j)).PosDef := by
    rw [hblock]
    exact MatrixCoordinateTransport.reindex_posDef coord.symm hpd
  have hpB:∀i j,0<algebraMap P.Carrier ℝ (FixedRealClosedBlockHardness.block S X i j) := by
    intro i j
    rw [congrFun (congrFun hblock i) j]
    exact hp (coord i) (coord j)
  have hnonB:∃i j,FixedRealClosedBlockHardness.block S X i i≠FixedRealClosedBlockHardness.block S X j j := by
    obtain ⟨i,j,hij⟩:=hnon
    refine ⟨coord.symm i,coord.symm j,?_⟩
    intro he
    have he':=congrArg (algebraMap P.Carrier ℝ) he
    rw [congrFun (congrFun hblock (coord.symm i)) (coord.symm i),
      congrFun (congrFun hblock (coord.symm j)) (coord.symm j)] at he'
    exact hij (by simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,Equiv.apply_symm_apply] using he')
  have hhard:=FixedRealClosedBlockHardness.source_hard P.basis (algebraMap P.Carrier ℝ) S hS X hclosed hpdB hpB hnonB
  have hsource:=hhard.trans (FixedRealSquareRootGram.sourceReduction basis (fun _:Fin 1=>M)
    (fun l:Fin 0=>l.elim0) w 0 hs hw hnz hproj)
  exact hsource.trans (FixedRealColorReduction.homogeneous basis order (double B) (Sum.elim μ ν))

end PlanarHom.FixedRealBipartiteLeftHard
