import PlanarHom.PositiveRealCoreGrams
import PlanarHom.FixedRealEndpointGramReductions
import PlanarHom.FixedRealWeightPowerExtension

/-! A.8 is instantiated with the literal rational exponent one half. Its actual
finite root extension and retained-context programs give the decorated square
as an ordinary planar oracle reduction to the original prescribed source. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealSquareRootGram
open DensePolynomial Complexity FixedRealExtension RepresentedBit FixedRealMixedInterpolation
open FixedRealWeightRemoval RelativeWeightedSpectralField FiniteLanguageAliases
variable {n e q bt ut:ℕ} {F:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]

def model (basis:Module.Basis (Fin e) (RationalFunction n) F) (w:Fin q→F) (hw:∀i,0<realWeights w i) :=
  powerModel basis w hw (fun _:Fin 1=>(1/2:ℚ))

variable (basis:Module.Basis (Fin e) (RationalFunction n) F)

def decorated (M:Matrix (Fin q) (Fin q) F) (w:Fin q→F) (hw:∀i,0<realWeights w i) :
    Matrix (Fin q) (Fin q) (model basis w hw).Carrier :=
  EndpointUnarySource.unaryGauge (fun i j=>(model basis w hw).inclusion (M i j)) ((model basis w hw).powers 0)

def square (M:Matrix (Fin q) (Fin q) F) (w:Fin q→F) (hw:∀i,0<realWeights w i) :
    Matrix (Fin q) (Fin q) (model basis w hw).Carrier := (decorated basis M w hw)^2

theorem root_real (w:Fin q→F) (hw:∀i,0<realWeights w i) (i:Fin q) :
    algebraMap (model basis w hw).Carrier ℝ ((model basis w hw).powers 0 i)=Real.sqrt (realWeights w i) := by
  rw [(model basis w hw).powers_real]
  rw [Real.sqrt_eq_rpow]
  norm_num

def sourceReduction (M:Fin bt→Matrix (Fin q) (Fin q) F) (U:Fin ut→Fin q→F)
    (w:Fin q→F) (old:Fin bt)
    (hs:∀i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw:∀i,0<realWeights w i) (hnonzero:∀i,realMatrix (M old) i≠0)
    (hproj:∀i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j) :
    Reduction (problem (model basis w hw).basis (fun _:Fin 1=>square basis (M old) w hw)
      (fun u:Fin 0=>u.elim0) (fun _=>1)) (problem basis M U w) := by
  let P:=model basis w hw
  let ME:=fun l i j=>P.inclusion (M l i j)
  let UE:=fun l i=>P.inclusion (U l i)
  let wE:=fun i=>P.inclusion (w i)
  let PM:=powerMatrices ME wE P.powers
  let PU:=powerUnaries UE P.powers
  let old':Fin (bt+1+1):=Fin.castAdd 1 (Fin.castAdd 1 old)
  let root':Fin (ut+1):=Fin.natAdd ut 0
  have hm:PM old'=ME old := by
    funext i j
    simp only [PM,powerMatrices,old',appendFamily_old,appendOne_old]
  have hu:PU root'=P.powers 0 := by
    funext i
    simp only [PU,powerUnaries,root',appendFamily_new]
  have hg:=FixedRealEndpointGrams.squareDecorationReduction P.basis PM PU old' root'
  rw [hm,hu] at hg
  exact hg.trans (constructedPowers_joint basis M U w old hs hw hnonzero hproj (fun _:Fin 1=>(1/2:ℚ)))

theorem decorated_real (M:Matrix (Fin q) (Fin q) F) (w:Fin q→F) (hw:∀i,0<realWeights w i) (i j:Fin q) :
    algebraMap (model basis w hw).Carrier ℝ (decorated basis M w hw i j)=
      PositiveRealCore.decorated (realMatrix M) (realWeights w) (realWeights w) i j := by
  simp only [decorated,EndpointUnarySource.unaryGauge,map_mul,root_real,
    (model basis w hw).real_inclusion,PositiveRealCore.decorated_entry]
  rfl

theorem square_real (M:Matrix (Fin q) (Fin q) F) (w:Fin q→F) (hw:∀i,0<realWeights w i) :
    (fun i j=>algebraMap (model basis w hw).Carrier ℝ (square basis M w hw i j))=
      (PositiveRealCore.decorated (realMatrix M) (realWeights w) (realWeights w))^2 := by
  ext i j
  simp only [square,pow_two,Matrix.mul_apply,map_sum,map_mul,decorated_real]

end PlanarHom.FixedRealSquareRootGram
