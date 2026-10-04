import PlanarHom.PottsCenteredSeriesLaw
import PlanarHom.SelectedScalarSemantics

/-! NEW reconstruction: actual numeric selected-edge stretching implements the
centered exponent substitution, with every added vertex normalization paid. -/
noncomputable section
open Classical
namespace PlanarHom.PottsCentered
open Complexity Complexity.MixedCode SelectedScalarSemantics

def twoLabelEntries (q : ℕ) (x y : ℚ) : Fin 2 → Matrix (Fin q) (Fin q) ℚ :=
  fun l => if l.val=0 then entryMatrix q x else entryMatrix q y

def keepShort {g : MixedCode} (hg : g.Valid 2 0) :
    ∀ e∈g.edges,e.2.2≠0 → e.2.2<2 := fun e he _ => (hg.1 e he).2.2

theorem stretch_evaluation (g : MixedCode) (hg : g.Valid 2 0) (q n : ℕ) (x : ℚ) :
    (g.stretchLabel 0 0 n).evaluate (g.stretchLabel_valid hg 0 0 n (by decide) (keepShort hg))
      (fun _ : Fin 2 => entryMatrix q x) (fun u : Fin 0 => u.elim0) (fun _ => 1)=
      (q:ℚ)^(n*g.markedCount 0)*g.evaluate hg (twoLabelEntries q (x^(n+1)) x)
        (fun u : Fin 0 => u.elim0) (fun _ => 1) := by
  have hs := evaluate_stretchLabel g hg 0 n (0 : Fin 2) (keepShort hg)
    (fun _ : Fin 2 => entryMatrix q x) (fun u : Fin 0 => u.elim0)
  have hf : (pathPowerLabels (fun _ : Fin 2 => entryMatrix q x) 0 (0 : Fin 2) n :
      Fin 2 → Matrix (Fin q) (Fin q) ℚ)=
      scaled (twoLabelEntries q (x^(n+1)) x) (0 : Fin 2) ((q:ℚ)^n) := by
    funext l
    fin_cases l <;> simp [pathPowerLabels,scaled,twoLabelEntries,entryMatrix_pow]
  rw [hf,evaluate_scaled,← pow_mul] at hs
  exact hs

/-- The new header is precisely what cancels the scalar of every private path. -/
theorem normalized_stretch_evaluation (g : MixedCode) (hg : g.Valid 2 0)
    (q n : ℕ) (hq : 0<q) (x : ℚ) :
    (q:ℚ)⁻¹^(g.stretchLabel 0 0 n).vertices*
      (g.stretchLabel 0 0 n).evaluate (g.stretchLabel_valid hg 0 0 n (by decide) (keepShort hg))
        (fun _ : Fin 2 => entryMatrix q x) (fun u : Fin 0 => u.elim0) (fun _ => 1)=
      (q:ℚ)⁻¹^g.vertices*g.evaluate hg (twoLabelEntries q (x^(n+1)) x)
        (fun u : Fin 0 => u.elim0) (fun _ => 1) := by
  rw [stretch_evaluation g hg q n x,stretchLabel_vertices]
  have hc : (g.selectedEdges 0).length=g.markedCount 0 := by
    simp [selectedGraph,selectedEdges,markedCount]
  rw [hc]
  have hq0 : (q:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hq
  have he : (q:ℚ)⁻¹^(g.vertices+g.markedCount 0*n)*(q:ℚ)^(n*g.markedCount 0)=
      (q:ℚ)⁻¹^g.vertices := by
    rw [Nat.mul_comm (g.markedCount 0) n,pow_add,inv_pow,inv_pow,mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hq0),mul_one]
  rw [← mul_assoc,he]
end PlanarHom.PottsCentered
