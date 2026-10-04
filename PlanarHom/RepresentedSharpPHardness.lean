import PlanarHom.PromisedSharpPHardness
import PlanarHom.RepresentedReductionComposition
import PlanarHom.RepresentedBitFPClosure

/-! NEW: genuine #P hardness for represented-output problems. A single charged
finite oracle machine must work against every valid output representative.
The source is the existing independent accepting-path definition of #P. -/
noncomputable section
namespace PlanarHom.RepresentedBit
open Complexity

def SharpPHard (P : Problem) : Prop :=
  ∀f : Bits → ℕ, SharpP f → Nonempty (Reduction (ofCanonical (countingProblem f)) P)

theorem SharpPHard.ofCanonical {P : PromiseProblem} (h : PromisedSharpPHard P) :
    SharpPHard (ofCanonical P) := by
  intro f hf
  obtain ⟨r⟩ := h f hf
  exact ⟨Reduction.ofCanonical r⟩

theorem SharpPHard.trans {P Q : Problem} (h : SharpPHard P) (r : Reduction P Q) :
    SharpPHard Q := by
  intro f hf
  obtain ⟨s⟩ := h f hf
  exact ⟨s.trans r⟩

theorem SharpPHard.counting_inFP {P : Problem} (h : SharpPHard P) (hp : P.InFP)
    (f : Bits → ℕ) (hf : SharpP f) : (countingProblem f).InFP := by
  obtain ⟨r⟩ := h f hf
  exact (ofCanonical_inFP_iff _).mp (r.inFP hp)

end PlanarHom.RepresentedBit
