import PlanarHom.Corollary32Domains
import PlanarHom.PlanarFaces

/-! The actual two-parallel-edge realization and exact loop-safe weighted
substitution identity used in Corollary 3.2. -/
noncomputable section
namespace PlanarHom.Corollary32
open Complexity Complexity.MixedCode

/-- The two-edge gadget has no internal vertices, so all background weights
remain outside its signature; its terminals are on the actual outer face. -/
theorem square_planar_gadget {C R : Type} [Fintype C] [CommSemiring R]
    (M : Matrix C C R) (w : C → R) :
    TwoTerminal.PlanarEdgeGadget (TwoTerminal.parallelEdges 2) ∧
      TwoTerminal.signature (TwoTerminal.parallelEdges 2) M w = fun i j => M i j ^ 2 :=
  ⟨TwoTerminal.StripDrawing.parallelEdges_planarEdgeGadget 2, TwoTerminal.signature_parallelEdges 2 M w⟩

/-- Every original occurrence, including a loop, has two separate output factors.
No vertices or original unary/background occurrences are added or removed. -/
theorem evaluate_square_expansion {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
    {a u : ℕ} (g : MixedCode) (hg : g.Valid a u) (M : Fin a → Matrix C C K)
    (selected : Fin a) (U : Fin u → C → K) (w : C → K) :
    (g.expandBinaryWords (FiniteLabelWordLookupMachines.finTable (selectedSquareWord selected))).evaluate
      (expandBinaryWords_valid _ hg (FiniteLabelWordLookupMachines.lookup_finTable_lt (selectedSquareWord selected)))
      M U w = g.evaluate hg (selectedSquareLanguage M selected) U w := by
  simpa only [wordMatrices_selectedSquare] using
    evaluate_expandBinaryWords g hg (selectedSquareWord selected) M U w

end PlanarHom.Corollary32
