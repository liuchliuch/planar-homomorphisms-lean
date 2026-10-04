import PlanarHom.ZeroOneDichotomyAssembly
import PlanarHom.PositivePottsFoundationClosed

/-! NEW exact unconditional Theorem 7.1 endpoints. The original structural
hypotheses are retained; all-q Potts hardness and accepting-path #P membership
are proved imports, with no foundation or membership premise. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity

theorem theorem71_weighted {q:ℕ}
    (L:RealLanguage q 1 0) (hw:∀i,0<L.weights i)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (h01:∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1) :
    (L.BasicZeroOneSupport hs → L.problem.InFP) ∧
      (¬L.BasicZeroOneSupport hs → PromisedSharpPHard L.problem) :=
  theorem71_weighted_of_potts positivePottsFoundation L hw hs h01

theorem theorem71_unweighted {q:ℕ}
    (L:RealLanguage q 1 0) (hunit:∀i,L.weights i=1)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (h01:∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1) :
    (L.BasicZeroOneSupport hs → L.problem.InFP) ∧
      (¬L.BasicZeroOneSupport hs → PromisedSharpPHard L.problem) ∧
      ∃f:Bits→ℕ,SharpP f ∧ ∀raw,L.problem.valid raw →
        L.problem.value raw=(numberFieldEncoding L.basis).encode (f raw:L.field) :=
  theorem71_unweighted_of_potts positivePottsFoundation L hunit hs h01

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
