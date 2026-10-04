import PlanarHom.FixedRealRectangularNormalization
import PlanarHom.FixedRealQuotientTransport
import PlanarHom.BipartiteFullTwinFinite
import PlanarHom.RectangularBackgroundWeightedReconstruction

/-! NEW original-source programs for the literal two-sided normalized core
and every weighted row/column moment. Full twins are split by the proved
bipartite side equivalence; the source field and original backgrounds are
never silently identified with a new output presentation. -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical
namespace PlanarHom.FixedRealRectangularCoreSources
open DensePolynomial Complexity RepresentedBit FixedRealActualTwins
open RectangularSourceNormSimulation RectangularBackgroundSourceNormSimulation
open RectangularWeightedNormNormalization RectangularTwinQuotient RectangularBackgroundWeightedReconstruction
variable {n e p s : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K] [Algebra K ℝ]
variable [Nonempty (Fin p)] [Nonempty (Fin s)]

 theorem exists_core_sources (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (V : Matrix (Fin p) (Fin s) K) (hV : ∀ i j,0<algebraMap K ℝ (V i j))
    (μ : Fin p → K) (ν : Fin s → K)
    (hμ : ∀ i,0<algebraMap K ℝ (μ i)) (hν : ∀ j,0<algebraMap K ℝ (ν j)) :
    let VR := fun i j => algebraMap K ℝ (V i j)
    let μR := fun i => algebraMap K ℝ (μ i)
    let νR := fun j => algebraMap K ℝ (ν j)
    let N := normalized VR μR νR
    let P := FixedRealRectangularNormalization.model basis V hV μ ν hμ hν
    ∃ R : Matrix (Rows N) (Columns N) P.Carrier,
    ∃ μm : ℕ → Rows N → P.Carrier, ∃ νm : ℕ → Columns N → P.Carrier,
      (∀ r s,algebraMap P.Carrier ℝ (R r s)=core N r s) ∧
      (∀ m r,algebraMap P.Carrier ℝ (μm m r)=rowMass VR μR νR m r) ∧
      (∀ m s,algebraMap P.Carrier ℝ (νm m s)=columnMass VR μR νR m s) ∧
      ∀ m,Nonempty (Reduction
        (FixedRealComponents.problem P.basis (fun _ : Fin 1 => Matrix.fromBlocks 0 R R.transpose 0)
          (fun l : Fin 0 => l.elim0) (Sum.elim (μm m) (νm m)))
        (FixedRealComponents.problem basis (fun _ : Fin 1 => block V)
          (fun l : Fin 0 => l.elim0) (weights μ ν))) := by
  dsimp only
  let VR := fun i j => algebraMap K ℝ (V i j)
  let μR := fun i => algebraMap K ℝ (μ i)
  let νR := fun j => algebraMap K ℝ (ν j)
  let N := normalized VR μR νR
  let P := FixedRealRectangularNormalization.model basis V hV μ ν hμ hν
  let C := FixedRealRectangularNormalization.matrix basis V hV μ ν hμ hν
  let φ : P.Carrier →+* ℝ := algebraMap P.Carrier ℝ
  have hC : ∀ i j,φ (C i j)=block N i j := by
    intro i j
    exact congrFun (congrFun (FixedRealRectangularNormalization.matrix_real basis V hV μ ν hμ hν) i) j
  have hsC : ∀ i j,C i j=C j i := by
    intro i j
    apply φ.injective
    rw [hC,hC]
    exact block_symm N i j
  have hN : ∀ i j,0<N i j := normalized_pos VR hV μR νR hμ hν
  let a := (rowEquivTo φ C (block N) hC).trans (BipartiteFullTwins.finSideEquiv N hN)
  let Q := Twins.quotientMatrix C hsC
  let D : Matrix (Rows N⊕Columns N) (Rows N⊕Columns N) P.Carrier :=
    fun i j => Q (a.symm i) (a.symm j)
  have hD : ∀ i j,φ (D i j)=BipartiteFullTwins.double (core N) i j := by
    intro i j
    rw [show φ (D i j)=Twins.quotientMatrix (block N) (block_symm N)
      (rowEquivTo φ C (block N) hC (a.symm i)) (rowEquivTo φ C (block N) hC (a.symm j)) from
      quotientMatrix_map_to φ C hsC (block N) (block_symm N) hC (a.symm i) (a.symm j)]
    rw [BipartiteFullTwins.quotientMatrix_finSideEquiv N hN]
    change BipartiteFullTwins.double (core N) (a (a.symm i)) (a (a.symm j))=_
    rw [a.apply_symm_apply,a.apply_symm_apply]
  let R : Matrix (Rows N) (Columns N) P.Carrier := fun r s => D (.inl r) (.inr s)
  have hR : ∀ r s,φ (R r s)=core N r s := fun r s => hD (.inl r) (.inr s)
  have hDb : D=Matrix.fromBlocks 0 R R.transpose 0 := by
    funext i j
    apply φ.injective
    rw [hD]
    cases i <;> cases j <;> simp only [BipartiteFullTwins.double,Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.transpose_apply,Matrix.zero_apply,map_zero,hR]
  let wm : ℕ → Fin (p+s) → P.Carrier := fun m i =>
    P.inclusion (weights μ ν i)*P.inclusion (squareNorm (block V) (weights μ ν) i)^m
  let v : ℕ → Rows N⊕Columns N → P.Carrier := fun m i => Twins.quotientWeight C (wm m) (a.symm i)
  let μm := fun m r => v m (.inl r)
  let νm := fun m s => v m (.inr s)
  have hwm : ∀ m i,φ (wm m i)=weights μR νR i *
      (RectangularBackgroundSourceNormSimulation.norm VR μR νR i)^(2*m) := by
    intro m i
    have h := FixedRealRectangularNormalization.moment_real basis V hV μ ν hμ hν m i
    change φ (wm m i)=algebraMap K ℝ (weights μ ν i)*_ at h
    rw [h]
    congr 1
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;>
      simp only [weights,Fin.addCases_left,Fin.addCases_right,μR,νR]
  have hv : ∀ m i,φ (v m i)=Sum.elim (rowMass VR μR νR m) (columnMass VR μR νR m) i := by
    intro m i
    rw [show φ (v m i)=Twins.quotientWeight (block N) (fun x => φ (wm m x))
      (rowEquivTo φ C (block N) hC (a.symm i)) from
      quotientWeight_map_to φ C (block N) hC (wm m) (a.symm i)]
    simp only [hwm,weights,RectangularBackgroundSourceNormSimulation.norm]
    rw [BipartiteFullTwins.quotientMoment_finSideEquiv N hN]
    change Sum.elim (rowMass VR μR νR m) (columnMass VR μR νR m) (a (a.symm i))=_
    rw [a.apply_symm_apply]
  refine ⟨R,μm,νm,hR,(fun m r => hv m (.inl r)),(fun m s => hv m (.inr s)),?_⟩
  intro m
  have red := (FixedRealActualTwins.reindexReduction P.basis Q (Twins.quotientWeight C (wm m)) a.symm).trans
    ((quotientReduction P.basis C hsC (wm m)).trans
      (FixedRealNormNormalization.normalizedMomentReduction basis (fun _ : Fin 1 => block V)
        (fun l : Fin 0 => l.elim0) (weights μ ν) 0 (block_symm V)
        (FixedRealRectangularNormalization.normSquare_pos V hV μ ν hμ hν) m))
  change Reduction (FixedRealComponents.problem P.basis (fun _ : Fin 1 => D)
    (fun l : Fin 0 => l.elim0) (v m)) _ at red
  have hwv : v m=Sum.elim (μm m) (νm m) := by funext i;cases i <;> rfl
  rw [hDb,hwv] at red
  exact ⟨red⟩

end PlanarHom.FixedRealRectangularCoreSources
