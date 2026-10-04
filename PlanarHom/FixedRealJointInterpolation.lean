import PlanarHom.FixedRealMixedAliases
import PlanarHom.RepresentedReductionComposition
import PlanarHom.FiniteLanguageJointReductions

/-! Signed joint interpolation over the actual represented fixed-real field.
Auxiliary labels coexist with the entire old language, are eliminated by their
literal interpolation machines, then aliased by an actual structural machine. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealMixedInterpolation
open DensePolynomial FixedRealExtension RepresentedBit ProductCompatibility FiniteLanguageAliases
variable {n e q b u:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def binaryAppendReduction (M:Fin b→Matrix (Fin q) (Fin q) K) (U:Fin u→Fin q→K) (w:Fin q→K)
    (N:Matrix (Fin q) (Fin q) K) (old:Fin b)
    (hzero:∀i j,M old i j=0→N i j=0)
    (hproducts:HasProductMaps (fun p:Fin q×Fin q=>M old p.1 p.2) (fun p=>N p.1 p.2)) :
    Reduction (problem basis (appendOne M N) U w) (problem basis M U w) := by
  have rp:=binaryReduction basis (Fin.last b) (appendOne M (M old)) (appendOne M N) U w
    (fun l hl=>appendOne_eq_of_ne_aux M N (M old) l hl)
    (by simpa only [appendOne_aux] using hzero)
    (by simpa only [appendOne_aux] using compatible_of_hasProductMaps _ _ hproducts)
  have ra:=binaryRelabelReduction basis (aliasAux old) M U w
  have ra':Reduction (problem basis (appendOne M (M old)) U w) (problem basis M U w):=by
    simpa only [comp_aliasAux] using ra
  exact rp.trans ra'

def unaryAppendReduction (M:Fin b→Matrix (Fin q) (Fin q) K) (U:Fin u→Fin q→K) (w:Fin q→K)
    (N:Fin q→K) (old:Fin u) (hzero:∀i,U old i=0→N i=0)
    (hproducts:HasProductMaps (U old) N) :
    Reduction (problem basis M (appendOne U N) w) (problem basis M U w) := by
  have rp:=unaryReduction basis (Fin.last u) M (appendOne U (U old)) (appendOne U N) w
    (fun l hl=>appendOne_eq_of_ne_aux U N (U old) l hl)
    (by simpa only [appendOne_aux] using hzero)
    (by simpa only [appendOne_aux] using compatible_of_hasProductMaps _ _ hproducts)
  have ra:=unaryRelabelReduction basis (aliasAux old) M U w
  have ra':Reduction (problem basis M (appendOne U (U old)) w) (problem basis M U w):=by
    simpa only [comp_aliasAux] using ra
  exact rp.trans ra'

def binaryFinite_joint {r:ℕ} (M:Fin b→Matrix (Fin q) (Fin q) K) (U:Fin u→Fin q→K) (w:Fin q→K)
    (N:Fin r→Matrix (Fin q) (Fin q) K) (old:Fin r→Fin b)
    (hzero:∀j i k,M (old j) i k=0→N j i k=0)
    (hproducts:∀j,HasProductMaps (fun p:Fin q×Fin q=>M (old j) p.1 p.2) (fun p=>N j p.1 p.2))
    (base:Problem) (available:Reduction (problem basis M U w) base) :
    Reduction (problem basis (appendFamily M N) U w) base := by
  induction r with
  | zero=>simpa only [appendFamily_zero] using available
  | succ r ih=>
    have prev:=ih (fun i=>N i.castSucc) (fun i=>old i.castSucc)
      (fun j=>hzero j.castSucc) (fun j=>hproducts j.castSucc)
    have last:=binaryAppendReduction basis (appendFamily M (fun i:Fin r=>N i.castSucc)) U w
      (N (Fin.last r)) (Fin.castAdd r (old (Fin.last r)))
      (by simpa only [appendFamily_old] using hzero (Fin.last r))
      (by simpa only [appendFamily_old] using hproducts (Fin.last r))
    simpa only [←appendFamily_succ] using last.trans prev

def unaryFinite_joint {r:ℕ} (M:Fin b→Matrix (Fin q) (Fin q) K) (U:Fin u→Fin q→K) (w:Fin q→K)
    (N:Fin r→Fin q→K) (old:Fin r→Fin u) (hzero:∀j i,U (old j) i=0→N j i=0)
    (hproducts:∀j,HasProductMaps (U (old j)) (N j))
    (base:Problem) (available:Reduction (problem basis M U w) base) :
    Reduction (problem basis M (appendFamily U N) w) base := by
  induction r with
  | zero=>simpa only [appendFamily_zero] using available
  | succ r ih=>
    have prev:=ih (fun i=>N i.castSucc) (fun i=>old i.castSucc)
      (fun j=>hzero j.castSucc) (fun j=>hproducts j.castSucc)
    have last:=unaryAppendReduction basis M (appendFamily U (fun i:Fin r=>N i.castSucc)) w
      (N (Fin.last r)) (Fin.castAdd r (old (Fin.last r)))
      (by simpa only [appendFamily_old] using hzero (Fin.last r))
      (by simpa only [appendFamily_old] using hproducts (Fin.last r))
    simpa only [←appendFamily_succ] using last.trans prev

/-- Several binary and unary replacement types are jointly available with all
original labels retained. The already-simulated source may have any represented
base oracle; actual nested substitution is part of the resulting machine. -/
def theoremA3_joint {r s:ℕ} (M:Fin b→Matrix (Fin q) (Fin q) K) (U:Fin u→Fin q→K) (w:Fin q→K)
    (N:Fin r→Matrix (Fin q) (Fin q) K) (V:Fin s→Fin q→K)
    (oldM:Fin r→Fin b) (oldU:Fin s→Fin u)
    (hzeroM:∀j i k,M (oldM j) i k=0→N j i k=0)
    (hproductsM:∀j,HasProductMaps (fun p:Fin q×Fin q=>M (oldM j) p.1 p.2) (fun p=>N j p.1 p.2))
    (hzeroU:∀j i,U (oldU j) i=0→V j i=0) (hproductsU:∀j,HasProductMaps (U (oldU j)) (V j))
    (base:Problem) (available:Reduction (problem basis M U w) base) :
    Reduction (problem basis (appendFamily M N) (appendFamily U V) w) base :=
  unaryFinite_joint basis (appendFamily M N) U w V oldU hzeroU hproductsU base
    (binaryFinite_joint basis M U w N oldM hzeroM hproductsM base available)

end PlanarHom.FixedRealMixedInterpolation
