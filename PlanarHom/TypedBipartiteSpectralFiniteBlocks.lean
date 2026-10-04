import PlanarHom.TypedBipartiteSpectralBlocks
import PlanarHom.TypedBipartiteSpectralSampling
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Finite numeric coordinates for the same-side sampling compiler. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteSpectral
variable {q y : ℕ} {K : Type} [Field K]

def leftEmbedding : Fin q → Fin (q+y) := Fin.castAdd y

def retractLeft (x₀ : Fin q) : Fin (q+y) → Fin q :=
  fun c=>Sum.elim id (fun _=>x₀) (finSumFinEquiv.symm c)

@[simp] theorem retractLeft_left (x₀ x : Fin q) :
    retractLeft (y:=y) x₀ (leftEmbedding x)=x := by
  change Sum.elim id (fun _ : Fin y=>x₀)
    (finSumFinEquiv.symm (finSumFinEquiv (.inl x)))=x
  simp

def zeroExtendFin (A : Matrix (Fin q) (Fin q) K) : Matrix (Fin (q+y)) (Fin (q+y)) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (zeroExtend (Y:=Fin y) A)

@[simp] theorem zeroExtendFin_left (A : Matrix (Fin q) (Fin q) K) (i j : Fin q) :
    zeroExtendFin (y:=y) A (leftEmbedding i) (leftEmbedding j)=A i j := by
  change zeroExtend A (finSumFinEquiv.symm (finSumFinEquiv (.inl i)))
    (finSumFinEquiv.symm (finSumFinEquiv (.inl j)))=A i j
  simp

theorem zeroExtendFin_support (A : Matrix (Fin q) (Fin q) K) :
    ∀ c,c∉Set.range (leftEmbedding (y:=y)) → ∀ d,zeroExtendFin A c d=0 := by
  intro c hc d
  obtain ⟨c,rfl⟩ := finSumFinEquiv.surjective c
  rcases c with c|c
  · exact (hc ⟨c,rfl⟩).elim
  · simp [zeroExtendFin,Matrix.reindex_apply]

theorem zeroExtendFin_pow (A : Matrix (Fin q) (Fin q) K) (n : ℕ) (hn : 0<n) :
    zeroExtendFin (y:=y) A^n=zeroExtendFin (y:=y) (A^n) := by
  change (Matrix.reindexAlgEquiv K K finSumFinEquiv (zeroExtend A))^n=
    Matrix.reindexAlgEquiv K K finSumFinEquiv (zeroExtend (A^n))
  rw [← map_pow,zeroExtend_pow _ n hn]

/-- The duplicated completion agrees on X with the supported source powers.
No relation at an unused ambient entry is needed by a typed query. -/
theorem repeatEntries_power_on_X (A : Matrix (Fin q) (Fin q) K) (x₀ : Fin q)
    (n : ℕ) (hn : 0<n) (i j : Fin q) :
    repeatEntries (retractLeft (y:=y) x₀) (A^n) (leftEmbedding i) (leftEmbedding j)=
      (zeroExtendFin (y:=y) A^n) (leftEmbedding i) (leftEmbedding j) := by
  rw [zeroExtendFin_pow _ n hn,zeroExtendFin_left]
  simp [repeatEntries]

end PlanarHom.TypedBipartiteSpectral
