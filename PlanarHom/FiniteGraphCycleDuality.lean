import PlanarHom.PottsRandomCluster
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic

/-! NEW finite primal/dual cycle-cut exactness. Connected incidence matrices
have the proved rank vertex-count minus one. Boundary compatibility therefore
gives the universal Euler upper bound, and equality forces every primal cycle
to be the boundary of an actual dual vertex subset over ZMod 2. -/
noncomputable section
open scoped BigOperators
open Matrix Module
namespace PlanarHom.MultiGraph
variable {V E F K : Type*} [Fintype V] [Fintype E] [Fintype F] [Field K]

def coboundaryMatrix (K : Type*) [Field K] (G : MultiGraph V E) : Matrix E V K := by
  classical
  exact fun e v => (if G.src e=v then 1 else 0)-(if G.dst e=v then 1 else 0)

theorem coboundaryMatrix_apply (G : MultiGraph V E) (f : V → K) (e : E) :
    (G.coboundaryMatrix K).mulVec f e=f (G.src e)-f (G.dst e) := by
  classical
  simp [coboundaryMatrix,Matrix.mulVec,dotProduct,sub_mul,ite_mul,Finset.sum_sub_distrib]

def constantLinear (K V : Type*) [Field K] : K →ₗ[K] (V → K) where
  toFun k _ := k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coboundary_ker_eq_constants (G : MultiGraph V E) (root : V)
    (hconn : ∀ u v, G.componentSetoid Finset.univ u v) :
    LinearMap.ker (G.coboundaryMatrix K).mulVecLin=LinearMap.range (constantLinear K V) := by
  classical
  ext f
  constructor
  · intro hf
    have hedge : G.EdgeConstant Finset.univ f := by
      intro e he
      have hh := congrFun (show (G.coboundaryMatrix K).mulVec f=0 from hf) e
      rw [G.coboundaryMatrix_apply] at hh
      exact sub_eq_zero.mp hh
    refine ⟨f root,?_⟩
    funext v
    exact G.edgeConstant_respects Finset.univ f hedge (hconn root v)
  · rintro ⟨k,rfl⟩
    change (G.coboundaryMatrix K).mulVec (fun _ => k)=0
    funext e
    rw [G.coboundaryMatrix_apply]
    simp

theorem coboundary_rank_add_one (G : MultiGraph V E) (root : V)
    (hconn : ∀ u v, G.componentSetoid Finset.univ u v) :
    (G.coboundaryMatrix K).rank+1=Fintype.card V := by
  have hinj : Function.Injective (constantLinear K V) := by
    intro x y h
    exact congrFun h root
  have hr : finrank K (LinearMap.range (constantLinear K V))=1 := by
    rw [LinearMap.finrank_range_of_inj hinj,Module.finrank_self]
  have hn := (G.coboundaryMatrix K).mulVecLin.finrank_range_add_finrank_ker
  rw [G.coboundary_ker_eq_constants root hconn,hr,Module.finrank_pi] at hn
  exact hn

/-- Actual signed face-boundary compatibility expressed as a matrix identity. -/
def CycleDualCompatible (G : MultiGraph V E) (D : MultiGraph F E) : Prop :=
  (G.coboundaryMatrix K).transpose * D.coboundaryMatrix K=0

theorem dual_range_le_primal_kernel (G : MultiGraph V E) (D : MultiGraph F E)
    (hclosed : CycleDualCompatible (K:=K) G D) :
    LinearMap.range (D.coboundaryMatrix K).mulVecLin ≤ LinearMap.ker (G.coboundaryMatrix K).transpose.mulVecLin := by
  rintro x ⟨f,rfl⟩
  change (G.coboundaryMatrix K).transpose.mulVec ((D.coboundaryMatrix K).mulVec f)=0
  rw [Matrix.mulVec_mulVec,hclosed]
  simp

/-- Universal connected orientable-map Euler upper bound, derived from the
literal primal and dual incidences rather than an assumed surface theorem. -/
theorem cycleDual_euler_le (G : MultiGraph V E) (D : MultiGraph F E) (root : V) (face : F)
    (hG : ∀ u v, G.componentSetoid Finset.univ u v)
    (hD : ∀ u v, D.componentSetoid Finset.univ u v)
    (hclosed : CycleDualCompatible (K:=K) G D) :
    Fintype.card V+Fintype.card F≤Fintype.card E+2 := by
  have hgr := G.coboundary_rank_add_one (K:=K) root hG
  have hdr := D.coboundary_rank_add_one (K:=K) face hD
  have hle := Submodule.finrank_mono (G.dual_range_le_primal_kernel D hclosed)
  have hn := (G.coboundaryMatrix K).transpose.mulVecLin.finrank_range_add_finrank_ker
  change (G.coboundaryMatrix K).transpose.rank+_=finrank K (E → K) at hn
  rw [Matrix.rank_transpose,Module.finrank_pi] at hn
  change (D.coboundaryMatrix K).rank≤_ at hle
  omega

/-- At the actual sphere Euler equality, every primal cycle has an actual
face potential whose dual coboundary is precisely that cycle. -/
theorem cycleDual_exact_of_euler (G : MultiGraph V E) (D : MultiGraph F E) (root : V) (face : F)
    (hG : ∀ u v, G.componentSetoid Finset.univ u v)
    (hD : ∀ u v, D.componentSetoid Finset.univ u v)
    (hclosed : CycleDualCompatible (K:=K) G D)
    (heuler : Fintype.card V+Fintype.card F=Fintype.card E+2) :
    LinearMap.range (D.coboundaryMatrix K).mulVecLin=LinearMap.ker (G.coboundaryMatrix K).transpose.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq (G.dual_range_le_primal_kernel D hclosed)
  have hgr := G.coboundary_rank_add_one (K:=K) root hG
  have hdr := D.coboundary_rank_add_one (K:=K) face hD
  have hn := (G.coboundaryMatrix K).transpose.mulVecLin.finrank_range_add_finrank_ker
  change (G.coboundaryMatrix K).transpose.rank+_=finrank K (E → K) at hn
  rw [Matrix.rank_transpose,Module.finrank_pi] at hn
  change (D.coboundaryMatrix K).rank=_
  omega

theorem exists_normalized_dual_potential (G : MultiGraph V E) (D : MultiGraph F E) (root : V) (face : F)
    (hG : ∀ u v, G.componentSetoid Finset.univ u v)
    (hD : ∀ u v, D.componentSetoid Finset.univ u v)
    (hclosed : CycleDualCompatible (K:=K) G D)
    (heuler : Fintype.card V+Fintype.card F=Fintype.card E+2)
    (cycle : E → K) (hcycle : (G.coboundaryMatrix K).transpose.mulVec cycle=0) :
    ∃ f : F → K, f face=0 ∧ (D.coboundaryMatrix K).mulVec f=cycle := by
  have hm : cycle∈LinearMap.range (D.coboundaryMatrix K).mulVecLin := by
    rw [G.cycleDual_exact_of_euler D root face hG hD hclosed heuler]
    exact hcycle
  obtain ⟨f,hf⟩ := hm
  refine ⟨fun x => f x-f face,sub_self _,?_⟩
  funext e
  rw [D.coboundaryMatrix_apply]
  have hh := congrFun hf e
  change (D.coboundaryMatrix K).mulVec f e=cycle e at hh
  rw [D.coboundaryMatrix_apply] at hh
  exact (by linear_combination hh)

end PlanarHom.MultiGraph
