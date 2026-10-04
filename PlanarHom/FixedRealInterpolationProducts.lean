import PlanarHom.RepresentedProductTables
import PlanarHom.FixedRealAlphabetPresentation

/-! Concrete fixed-real product-table compiler: word products and semantic
extension equality are both instantiated by their actual bit programs. No
fixed-base product or canonical value-code assumption remains in this layer. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealInterpolationProducts
open DensePolynomial RepresentedBit Complexity
variable {n e t:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

def wordProductMachine (basis:Module.Basis (Fin e) (RationalFunction n) K) (A:Fin t→K) :
    WordProductMachine (FixedRealExtension.presentation basis) A where
  run:=FixedRealAlphabet.natWord (FixedRealAlphabet.data basis A)
  fp:=FixedRealAlphabet.fp_natWord _
  valid:=FixedRealAlphabet.natWord_valid _
  value:=FixedRealAlphabet.natWord_value _

def table (basis:Module.Basis (Fin e) (RationalFunction n) K) (A B:Fin t→K) (m:ℕ) :
    List (RepresentedProductTables.Row (FixedRealExtension.presentation basis)) :=
  RepresentedProductTables.representatives (FixedRealExtension.presentation basis)
    (FixedRealRootRestriction.equalityMachine basis) (wordProductMachine basis A) (wordProductMachine basis B) m

theorem fp_table (basis:Module.Basis (Fin e) (RationalFunction n) K) (A B:Fin t→K) :
    FP BitEncoding.unaryNat (RepresentedProductTables.rowEncoding (FixedRealExtension.presentation basis)).list
      (table basis A B) :=
  RepresentedProductTables.fp_representatives _ _ _ _

theorem table_semantics (basis:Module.Basis (Fin e) (RationalFunction n) K) (A B:Fin t→K) (m:ℕ) :
    (table basis A B m).map (RepresentedProductTables.semanticPair (FixedRealExtension.presentation basis))=
      ExponentProductTables.representatives A B m :=
  RepresentedProductTables.representatives_semantics _ _ _ _ _

end PlanarHom.FixedRealInterpolationProducts
