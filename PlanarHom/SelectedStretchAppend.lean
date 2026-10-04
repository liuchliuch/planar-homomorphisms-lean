import PlanarHom.SelectedStretchMachines
import PlanarHom.SelectedStretchSemantics
import PlanarHom.PrescribedDomainAliases

/-! Ready-to-use path queries for one appended auxiliary matrix label. The
output uses precisely the original source alphabet. The length-indexed form
matches the positive interpolation samples `1,...,N`. -/

noncomputable section
namespace PlanarHom.Complexity.MixedCode
open Classical
variable {C R : Type} [Fintype C] [DecidableEq C] [CommSemiring R]

theorem pathPowerLabels_appendOne {b : ℕ} (M : Fin b → Matrix C C R)
    (replacement : Fin b) (n : ℕ) :
    pathPowerLabels (a := b+1) M b replacement n =
      FiniteLanguageAliases.appendOne M (M replacement^(n+1)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [pathPowerLabels, FiniteLanguageAliases.appendOne_aux]
  · change pathPowerLabels M b replacement n (Fin.castAdd 1 j) =
      FiniteLanguageAliases.appendOne M (M replacement^(n+1)) (Fin.castAdd 1 j)
    simp [pathPowerLabels, j.isLt.ne, j.isLt, FiniteLanguageAliases.appendOne_old]

theorem appended_companion_bound {b u : ℕ} (g : MixedCode) (hg : g.Valid (b+1) u) :
    ∀e∈g.edges,e.2.2≠b→e.2.2<b := by
  intro e he hne
  have hb := (hg.1 e he).2.2
  omega

/-- Appended target occurrences become source-C paths; old C occurrences and
every other original binary label remain available and unchanged. -/
theorem evaluate_stretchLabel_appendOne {b u : ℕ} (g : MixedCode)
    (hg : g.Valid (b+1) u) (replacement : Fin b) (n : ℕ)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R) :
    (g.stretchLabel b replacement.val n).evaluate
      (g.stretchLabel_valid hg b replacement.val n replacement.isLt (g.appended_companion_bound hg))
      M U (fun _ => 1) =
    g.evaluate hg (FiniteLanguageAliases.appendOne M (M replacement^(n+1))) U (fun _ => 1) := by
  simpa only [pathPowerLabels_appendOne] using
    g.evaluate_stretchLabel hg b n replacement (g.appended_companion_bound hg) M U

theorem stretchLabelLength_valid {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (selected h : ℕ) (replacement : Fin b)
    (hkeep : ∀e∈g.edges,e.2.2≠selected→e.2.2<b) :
    (g.stretchLabelLength selected replacement.val h).Valid b u :=
  g.stretchLabel_valid hg selected replacement.val (h-1) replacement.isLt hkeep

theorem stretchLabelLength_planar {a b u : ℕ} (g : MixedCode) (hg : g.PlanarValid a u)
    (selected h : ℕ) (replacement : Fin b)
    (hkeep : ∀e∈g.edges,e.2.2≠selected→e.2.2<b) :
    (g.stretchLabelLength selected replacement.val h).PlanarValid b u :=
  g.stretchLabel_planar hg selected replacement.val (h-1) replacement.isLt hkeep

/-- Positive path length is exactly the exponent. At zero the total machine
uses one segment; the semantic theorem deliberately requires positivity. -/
theorem evaluate_stretchLabelLength_appendOne {b u : ℕ} (g : MixedCode)
    (hg : g.Valid (b+1) u) (replacement : Fin b) (h : ℕ) (hh : 1≤h)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R) :
    (g.stretchLabelLength b replacement.val h).evaluate
      (g.stretchLabelLength_valid hg b h replacement (g.appended_companion_bound hg))
      M U (fun _ => 1) =
    g.evaluate hg (FiniteLanguageAliases.appendOne M (M replacement^h)) U (fun _ => 1) := by
  simpa only [stretchLabelLength, Nat.sub_add_cancel hh] using
    g.evaluate_stretchLabel_appendOne hg replacement (h-1) M U

end PlanarHom.Complexity.MixedCode
