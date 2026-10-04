import PlanarHom.Structures
import PlanarHom.TractableEvaluation

/-! NEW literal generic-field bipartite rank-two matrix definition. -/
namespace PlanarHom.BipartiteRankTwoTractability
variable {K : Type*} [Zero K] [Mul K] {k l : ℕ}

def matrix (a : Fin k → K) (b : Fin l → K) : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) K
  | .inl i, .inr j => a i*b j
  | .inr j, .inl i => a i*b j
  | _,_ => 0

@[simp] theorem matrix_inl_inr (a : Fin k → K) (b : Fin l → K) (i : Fin k) (j : Fin l) :
    matrix a b (.inl i) (.inr j)=a i*b j := rfl
@[simp] theorem matrix_inr_inl (a : Fin k → K) (b : Fin l → K) (i : Fin k) (j : Fin l) :
    matrix a b (.inr j) (.inl i)=a i*b j := rfl
@[simp] theorem matrix_inl_inl (a : Fin k → K) (b : Fin l → K) (i j : Fin k) :
    matrix a b (.inl i) (.inl j)=0 := rfl
@[simp] theorem matrix_inr_inr (a : Fin k → K) (b : Fin l → K) (i j : Fin l) :
    matrix a b (.inr i) (.inr j)=0 := rfl

theorem matrix_symmetric (a : Fin k → K) (b : Fin l → K) : ∀i j,matrix a b i j=matrix a b j i := by
  intro i j
  cases i <;> cases j <;> rfl
end PlanarHom.BipartiteRankTwoTractability
