import PlanarHom.EffectiveSpectralTransfer
import PlanarHom.FixedVectorMachines

/-! Effective sampling can repeat genuine X entries at unused positions.
Repeating entries adds no product identities. In particular this never adjoins
a dummy eigenvalue or a new constant coordinate to the tested alphabet. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.TypedBipartiteSpectral
open Complexity Complexity.MixedCode ExponentProductTables ExponentProductSemantics
variable {K : Type} [Field K] {t s q k : ℕ}

/-- Equal-length compatibility is stable under repeating existing coordinates. -/
theorem compatibleAt_comp (A B : Fin t → K) (ρ : Fin s → Fin t) (m : ℕ)
    (h : CompatibleAt A B m) : CompatibleAt (A ∘ ρ) (B ∘ ρ) m := by
  intro xs hxs ys hys hn he
  let xw := (expand s xs).map ρ
  let yw := (expand s ys).map ρ
  have hxlen : xw.length=m := by
    simpa only [xw,List.length_map,expand_length xs ((ExponentVectors.mem_weak s m xs).mp hxs).1]
      using ((ExponentVectors.mem_weak s m xs).mp hxs).2
  have hylen : yw.length=m := by
    simpa only [yw,List.length_map,expand_length ys ((ExponentVectors.mem_weak s m ys).mp hys).1]
      using ((ExponentVectors.mem_weak s m ys).mp hys).2
  have hx : WordFrequencies.frequencies xw∈ExponentVectors.weak t m := by
    simpa only [hxlen] using WordFrequencies.frequencies_mem_weak xw
  have hy : WordFrequencies.frequencies yw∈ExponentVectors.weak t m := by
    simpa only [hylen] using WordFrequencies.frequencies_mem_weak yw
  have hval (F : Fin t → K) (zs : List ℕ) :
      value F (WordFrequencies.frequencies ((expand s zs).map ρ))=value (F ∘ ρ) zs := by
    rw [value_frequencies,List.map_map,expand_product]
  have hc := h _ hx _ hy (by simpa only [xw,hval] using hn)
    (by simpa only [xw,yw,hval] using he)
  simpa only [xw,yw,hval] using hc

/-- A retracted matrix uses only entries of the actual X matrix. -/
def repeatEntries (ρ : Fin k → Fin q) (A : Matrix (Fin q) (Fin q) K) :
    Matrix (Fin k) (Fin k) K := A.submatrix ρ ρ

theorem binaryAlphabet_repeatEntries (ρ : Fin k → Fin q) (A : Matrix (Fin q) (Fin q) K) :
    binaryAlphabet (repeatEntries ρ A)=binaryAlphabet A ∘
      (fun e=>finProdFinEquiv (ρ (finProdFinEquiv.symm e).1,ρ (finProdFinEquiv.symm e).2)) := by
  funext e
  simp [binaryAlphabet,repeatEntries]

variable [Algebra ℚ K] {dimension : ℕ}

theorem fp_repeatEntries (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : Fin k → Fin q) :
    FP ((numberFieldEncoding basis).vector (q*q)) ((numberFieldEncoding basis).vector (k*k))
      (fun v e=>v (finProdFinEquiv (ρ (finProdFinEquiv.symm e).1,ρ (finProdFinEquiv.symm e).2))) := by
  apply FixedVectorMachines.fp_assemble
  intro e
  exact FixedVectorMachines.fp_coordinate _ _ _

end PlanarHom.TypedBipartiteSpectral
