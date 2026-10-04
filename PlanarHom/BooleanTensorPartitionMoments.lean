import PlanarHom.BooleanTensorSpectral
import PlanarHom.BooleanSpectralCounts
import PlanarHom.GenericSpectralMoments

/-! Exact matrix-power and retained-coordinate partition moments. Every input
edge occurrence, including a loop or repeated edge, has its own spectral choice.
Unselected constraints, unary factors, and vertex weights stay in the same
possibly signed coefficients. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanTensorPartitionMoments
open Complexity Complexity.MixedCode BooleanTensorSpectral
variable {R : Type} [CommRing R] {d b bt ut : ℕ}

def replace (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) R)
    (selected : Fin bt) (A : Matrix (Fin d→Bool) (Fin d→Bool) R) :
    Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) R:=
  fun l=>if l=selected then A else M l

def rest (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) R)
    (U : Fin ut→(Fin d→Bool)→R) (w:(Fin d→Bool)→R)
    (a u h q : Fin d→R)
    (z : (Fin g.vertices→(Fin d→Bool)) × (Fin (g.markedCount selected.val)→(Fin d→Bool))) : R:=
  GenericSpectralMoments.spectralRest g hg selected M U w (eigenprojector a u h q) z

/-- Actual oracle matrix-power values are moments of the same fixed finite
contraction coefficients, with no positivity or loop-free assumption. -/
theorem evaluate_power (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) R)
    (U : Fin ut→(Fin d→Bool)→R) (w:(Fin d→Bool)→R)
    (c a u h q r : Fin d→R) (hh:∀i,h i+h i=1) (hq:∀i,r i*q i=1)
    (hr:∀i,r i^2=a i^2+u i^2) (n:ℕ) :
    g.evaluate hg (replace M selected ((tensor (fun i=>block (c i) (a i) (u i)))^n)) U w=
      ∑z : (Fin g.vertices→(Fin d→Bool)) × (Fin (g.markedCount selected.val)→(Fin d→Bool)),
        rest g hg selected M U w a u h q z * (∏e,eigenvalue c r (z.2 e))^n := by
  have he : replace M selected ((tensor (fun i=>block (c i) (a i) (u i)))^n)=
      GenericSpectralMoments.spectralLabels M selected (eigenprojector a u h q)
        (fun ε=>(eigenvalue c r ε)^n) := by
    funext l
    simp only [replace,GenericSpectralMoments.spectralLabels]
    split_ifs <;> simp only [tensor_power_expansion c a u h q r hh hq hr n]
  rw [he,GenericSpectralMoments.evaluate_spectral_powers]
  rfl

/-- Retained coordinates use the same coefficient for each complete spectral
choice; all nonretained factors become literal identities. -/
theorem evaluate_retained (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) R)
    (U : Fin ut→(Fin d→Bool)→R) (w:(Fin d→Bool)→R)
    (c a u h q r : Fin d→R) (S : Finset (Fin d))
    (hh:∀i,h i+h i=1) (hq:∀i,r i*q i=1) (hr:∀i,r i^2=a i^2+u i^2) :
    g.evaluate hg (replace M selected (tensor (fun i=>if i∈S then block (c i) (a i) (u i) else 1))) U w=
      ∑z : (Fin g.vertices→(Fin d→Bool)) × (Fin (g.markedCount selected.val)→(Fin d→Bool)),
        rest g hg selected M U w a u h q z *
          (∏e,∏i,if i∈S then branch (c i) (r i) (z.2 e i) else 1) := by
  have he : replace M selected (tensor (fun i=>if i∈S then block (c i) (a i) (u i) else 1))=
      GenericSpectralMoments.spectralLabels M selected (eigenprojector a u h q)
        (fun ε=>∏i,if i∈S then branch (c i) (r i) (ε i) else 1) := by
    funext l
    simp only [replace,GenericSpectralMoments.spectralLabels]
    split_ifs <;> simp only [retained_expansion c a u h q r S hh hq hr]
  rw [he,GenericSpectralMoments.evaluate_spectral_expansion]
  rfl

/-- The selected scalar moment node depends exactly on the finite class counts. -/
theorem eigenvalue_product_counts {m : ℕ} (cls:Fin d→Fin b)
    (c r : Fin b→R) (choice:Fin m→Fin d→Bool) :
    (∏e,eigenvalue (c∘cls) (r∘cls) (choice e))=
      ∏g,(c g+r g)^(BooleanSpectralCounts.total cls m g-BooleanSpectralCounts.count cls choice g)*
        (c g-r g)^BooleanSpectralCounts.count cls choice g := by
  exact BooleanSpectralCounts.product_eq_grouped cls choice (fun g=>c g+r g) (fun g=>c g-r g)

/-- All choices in one retained-count class have precisely one target scalar. -/
theorem retained_product_counts {m : ℕ} (cls:Fin d→Fin b) (g:Fin b)
    (c r : Fin b→R) (choice:Fin m→Fin d→Bool) :
    (∏e,∏i,if cls i=g then branch (c (cls i)) (r (cls i)) (choice e i) else 1)=
      (c g+r g)^(BooleanSpectralCounts.total cls m g-BooleanSpectralCounts.count cls choice g)*
        (c g-r g)^BooleanSpectralCounts.count cls choice g := by
  exact BooleanSpectralCounts.retained_product_eq cls choice (fun g=>c g+r g) (fun g=>c g-r g) g

end PlanarHom.BooleanTensorPartitionMoments
