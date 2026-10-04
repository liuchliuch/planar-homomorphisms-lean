import PlanarHom.RectangularNormalizationMomentSource
import PlanarHom.BipartiteFullTwinFinite
import PlanarHom.RectangularBackgroundWeightedReconstruction

/-! The actual field quotient is identified with the fixed real row/column
quotients of the original weighted normalization. The matrix and all moments
use the same equivalence; the two side masses are kept independent. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularSideMomentPresentation
open RectangularTwinQuotient RectangularWeightedNormNormalization
open RectangularSourceNormSimulation (block block_symm realRectangular)
open RectangularBackgroundSourceNormSimulation
open BipartiteFullTwins FiniteFieldQuotientLanguage
variable {p s : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)]
variable {K₀ F : IntermediateField ℚ ℝ}

def sideEquiv (C : Matrix (Fin (p+s)) (Fin (p+s)) F)
    (N : Matrix (Fin p) (Fin s) ℝ) (hN : ∀ i j,0<N i j)
    (hc : ∀ i j,(C i j:ℝ)=block N i j) :
    Quotient (Twins.rowSetoid C) ≃ Rows N⊕Columns N :=
  (realQuotientEquiv C (block N) hc).trans (finSideEquiv N hN)

omit [Nonempty (Fin p)] [Nonempty (Fin s)] in
theorem matrix_sideEquiv (C : Matrix (Fin (p+s)) (Fin (p+s)) F)
    (hs : ∀ i j,C i j=C j i)
    (N : Matrix (Fin p) (Fin s) ℝ) (hN : ∀ i j,0<N i j)
    (hc : ∀ i j,(C i j:ℝ)=block N i j) (a b : Quotient (Twins.rowSetoid C)) :
    (Twins.quotientMatrix C hs a b:ℝ)=
      double (core N) (sideEquiv C N hN hc a) (sideEquiv C N hN hc b) := by
  rw [quotientMatrix_real C hs (block N) (block_symm N) hc]
  exact quotientMatrix_finSideEquiv N hN _ _

theorem moment_sideEquiv (h₀ : K₀≤F)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j,0<(V i j:ℝ))
    (μ : Fin p→K₀) (ν : Fin s→K₀) (hμ : ∀ i,0<(μ i:ℝ)) (hν : ∀ j,0<(ν j:ℝ))
    (C : Matrix (Fin (p+s)) (Fin (p+s)) F)
    (hc : ∀ i j,(C i j:ℝ)=block
      (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))) i j)
    (m : ℕ) (z : Quotient (Twins.rowSetoid C)) :
    ((Twins.quotientWeight C (fun c=>IntermediateField.inclusion h₀ (weights μ ν c)*
      (IntermediateField.inclusion h₀ (squareNorm (block V) (weights μ ν) c))^m) z:F):ℝ)=
    Sum.elim
      (RectangularBackgroundWeightedReconstruction.rowMass (realRectangular V)
        (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m)
      (RectangularBackgroundWeightedReconstruction.columnMass (realRectangular V)
        (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m)
      (sideEquiv C _ (normalized_pos _ hV _ _ hμ hν) hc z) := by
  rw [quotient_moment_real h₀ V μ ν (fun i=>(hμ i).le) (fun j=>(hν j).le) C hc m z]
  have hw : (fun c=>((weights μ ν c:K₀):ℝ))=
      Fin.addCases (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) := by
    funext c
    refine Fin.addCases (fun i=>?_) (fun j=>?_) c <;> simp [weights]
  simp only [show ∀ c, ((weights μ ν c:K₀):ℝ)=Fin.addCases (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) c from fun c=>congrFun hw c,RectangularBackgroundSourceNormSimulation.norm]
  exact quotientMoment_finSideEquiv _ (normalized_pos _ hV _ _ hμ hν)
    (fun i=>(μ i:ℝ)) (rowNorm (realRectangular V) (fun j=>(ν j:ℝ)))
    (fun j=>(ν j:ℝ)) (columnNorm (realRectangular V) (fun i=>(μ i:ℝ))) m
    (realQuotientEquiv C _ hc z)

open Complexity Complexity.MixedCode AlgebraicProductInterpolation

def sideIndex (N : Matrix (Fin p) (Fin s) ℝ) :
    Fin (Fintype.card (Rows N⊕Columns N)) ≃ Rows N⊕Columns N :=
  (Fintype.equivFin _).symm

def fieldIndex (C : Matrix (Fin (p+s)) (Fin (p+s)) F)
    (N : Matrix (Fin p) (Fin s) ℝ) (hN : ∀ i j,0<N i j)
    (hc : ∀ i j,(C i j:ℝ)=block N i j) :
    Fin (Fintype.card (Rows N⊕Columns N)) ≃ Quotient (Twins.rowSetoid C) :=
  (sideIndex N).trans (sideEquiv C N hN hc).symm

/-- A fixed real side chart, rather than a fresh field-dependent quotient chart. -/
def language {d : ℕ} (basis : Module.Basis (Fin d) ℚ F)
    (C : Matrix (Fin (p+s)) (Fin (p+s)) F) (hs : ∀ i j,C i j=C j i)
    (N : Matrix (Fin p) (Fin s) ℝ) (hN : ∀ i j,0<N i j)
    (hc : ∀ i j,(C i j:ℝ)=block N i j) (w : Fin (p+s)→F) :
    RealLanguage (Fintype.card (Rows N⊕Columns N)) 1 0 := by
  letI : FiniteDimensional ℚ F := FiniteDimensional.of_fintype_basis basis
  let e := fieldIndex C N hN hc
  exact {
    matrices:=fun _ i j=>(Twins.quotientMatrix C hs (e i) (e j):ℝ)
    unaries:=fun l=>l.elim0
    weights:=fun i=>((Twins.quotientWeight C w (e i):F):ℝ)
    matrices_algebraic:=fun _ i j=>(IsAlgebraic.of_finite ℚ
      (Twins.quotientMatrix C hs (e i) (e j))).algHom F.val
    unaries_algebraic:=fun l=>l.elim0
    weights_algebraic:=fun i=>(IsAlgebraic.of_finite ℚ
      (Twins.quotientWeight C w (e i))).algHom F.val }

def reduction {d : ℕ} (basis : Module.Basis (Fin d) ℚ F)
    (C : Matrix (Fin (p+s)) (Fin (p+s)) F) (hs : ∀ i j,C i j=C j i)
    (N : Matrix (Fin p) (Fin s) ℝ) (hN : ∀ i j,0<N i j)
    (hc : ∀ i j,(C i j:ℝ)=block N i j) (w : Fin (p+s)→F) :
    PromisePolyTimeTuringReduction (language basis C hs N hN hc w).problem
      (evaluationProblem basis (fun _:Fin 1=>Twins.quotientMatrix C hs)
        (fun l:Fin 0=>l.elim0) (Twins.quotientWeight C w)) :=
  ((language basis C hs N hN hc w).presentationDescentReduction F basis
    (fun _ i j=>Twins.quotientMatrix C hs (fieldIndex C N hN hc i) (fieldIndex C N hN hc j))
    (fun l:Fin 0=>l.elim0) (fun i=>Twins.quotientWeight C w (fieldIndex C N hN hc i))
    (fun _ _ _=>rfl) (fun l=>l.elim0) (fun _=>rfl)).trans
      (ActualTwins.reindexReduction basis (Twins.quotientMatrix C hs)
        (Twins.quotientWeight C w) (fieldIndex C N hN hc))

theorem language_matrix {d : ℕ} (basis : Module.Basis (Fin d) ℚ F)
    (C : Matrix (Fin (p+s)) (Fin (p+s)) F) (hs : ∀ i j,C i j=C j i)
    (N : Matrix (Fin p) (Fin s) ℝ) (hN : ∀ i j,0<N i j)
    (hc : ∀ i j,(C i j:ℝ)=block N i j) (w : Fin (p+s)→F) (i j) :
    (language basis C hs N hN hc w).matrices 0 i j=
      double (core N) (sideIndex N i) (sideIndex N j) := by
  change (Twins.quotientMatrix C hs (fieldIndex C N hN hc i) (fieldIndex C N hN hc j):ℝ)=_
  rw [matrix_sideEquiv C hs N hN hc]
  simp only [fieldIndex,Equiv.trans_apply,Equiv.apply_symm_apply]

theorem language_moment {d : ℕ} (basis : Module.Basis (Fin d) ℚ F) (h₀ : K₀≤F)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j,0<(V i j:ℝ))
    (μ : Fin p→K₀) (ν : Fin s→K₀) (hμ : ∀ i,0<(μ i:ℝ)) (hν : ∀ j,0<(ν j:ℝ))
    (C : Matrix (Fin (p+s)) (Fin (p+s)) F) (hs : ∀ i j,C i j=C j i)
    (hc : ∀ i j,(C i j:ℝ)=block
      (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))) i j)
    (m : ℕ) (i) :
    (language basis C hs _ (normalized_pos _ hV _ _ hμ hν) hc
      (fun c=>IntermediateField.inclusion h₀ (weights μ ν c)*
        (IntermediateField.inclusion h₀ (squareNorm (block V) (weights μ ν) c))^m)).weights i=
    Sum.elim
      (RectangularBackgroundWeightedReconstruction.rowMass (realRectangular V)
        (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m)
      (RectangularBackgroundWeightedReconstruction.columnMass (realRectangular V)
        (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m)
      (sideIndex _ i) := by
  change ((Twins.quotientWeight C _ (fieldIndex C _ _ hc i):F):ℝ)=_
  rw [moment_sideEquiv h₀ V hV μ ν hμ hν C hc]
  apply congrArg (Sum.elim
    (RectangularBackgroundWeightedReconstruction.rowMass (realRectangular V)
      (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m)
    (RectangularBackgroundWeightedReconstruction.columnMass (realRectangular V)
      (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m))
  exact (sideEquiv C _ (normalized_pos _ hV _ _ hμ hν) hc).apply_symm_apply _

/-- Every fixed moment is an actual original-source program, in one common
real side chart whose colors do not depend on the selected implementation field. -/
theorem exists_moment_language {d : ℕ} (basis : Module.Basis (Fin d) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j,0<(V i j:ℝ))
    (μ : Fin p→K₀) (ν : Fin s→K₀) (hμ : ∀ i,0<(μ i:ℝ)) (hν : ∀ j,0<(ν j:ℝ))
    (m : ℕ) :
    ∃ L : RealLanguage (Fintype.card
        (Rows (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)))⊕
         Columns (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))))) 1 0,
      (∀ i j,L.matrices 0 i j=double
        (core (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))))
        (sideIndex _ i) (sideIndex _ j)) ∧
      (∀ i,L.weights i=Sum.elim
        (RectangularBackgroundWeightedReconstruction.rowMass (realRectangular V)
          (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m)
        (RectangularBackgroundWeightedReconstruction.columnMass (realRectangular V)
          (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) m) (sideIndex _ i)) ∧
      Nonempty (PromisePolyTimeTuringReduction L.problem
        (evaluationProblem basis (fun _:Fin 1=>block V) (fun l:Fin 0=>l.elim0) (weights μ ν))) := by
  obtain ⟨F,h₀,e,bF,C,hs,hc,hr⟩ := exists_rectangular_quotient_moment_sources
    basis V hV μ ν hμ hν (fun _:Fin 1=>m)
  have hc' := fun i j=>congrFun (congrFun hc i) j
  let N := normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))
  have hN : ∀ i j,0<N i j := normalized_pos _ hV _ _ hμ hν
  let w := fun c=>IntermediateField.inclusion h₀ (weights μ ν c)*
    (IntermediateField.inclusion h₀ (squareNorm (block V) (weights μ ν) c))^m
  refine ⟨language bF C hs N hN hc' w,language_matrix bF C hs N hN hc' w,?_,?_⟩
  · exact language_moment bF h₀ V hV μ ν hμ hν C hs hc' m
  · obtain ⟨r⟩ := hr 0
    exact ⟨(reduction bF C hs N hN hc' w).trans r⟩

end PlanarHom.RectangularSideMomentPresentation
