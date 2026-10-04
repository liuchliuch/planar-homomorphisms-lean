import PlanarHom.FixedRealExtensionPresentation
import PlanarHom.ListPredicateMachines

/-! Actual semantic equality of shared-denominator extension codes. Different
valid numerator/denominator representatives compare equal exactly when they
denote the same field element; no canonical field-value encoding is used. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealExtension
open DensePolynomial Complexity PairProjectionMachines ArithmeticCircuitPrimitives
variable {n e:ℕ}

def equality (n e:ℕ) (p:Code n e×Code n e) : Bool :=
  !((List.ofFn (fun i:Fin e=>fractionEq n (p.1.1 i,p.1.2) (p.2.1 i,p.2.2))).any Bool.not)

theorem equality_iff_coordinates (n e:ℕ) (p:Code n e×Code n e) :
    equality n e p=true ↔ ∀i,fractionEq n (p.1.1 i,p.1.2) (p.2.1 i,p.2.2)=true := by
  simp only [equality,Bool.not_eq_true']
  constructor
  · intro h i
    have hh:=(List.any_eq_false.mp h) _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa using hh
  · intro h
    apply List.any_eq_false.mpr
    intro b hb
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hb
    simpa using h i

theorem fp_equality (n e:ℕ) :
    FP ((encoding n e).prod (encoding n e)) BitEncoding.bool (equality n e) := by
  let ec:=encoding n e
  let ep:=DensePolynomial.encoding n
  have ha:=fp_fst ec ec
  have hb:=fp_snd ec ec
  have had:=ha.comp (fp_snd (ep.vector e) ep)
  have hbd:=hb.comp (fp_snd (ep.vector e) ep)
  have hn:FP (ec.prod ec) (BitEncoding.bool.vector e)
      (fun p i=>fractionEq n (p.1.1 i,p.1.2) (p.2.1 i,p.2.2)) := by
    apply FixedVectorMachines.fp_assemble
    intro i
    have hai:=(ha.comp (fp_fst (ep.vector e) ep)).comp (FixedVectorMachines.fp_coordinate ep e i)
    have hbi:=(hb.comp (fp_fst (ep.vector e) ep)).comp (FixedVectorMachines.fp_coordinate ep e i)
    exact ((hai.pair had).pair (hbi.pair hbd)).comp (DensePolynomial.fp_fractionEq n)
  have hl:FP (ec.prod ec) BitEncoding.bool.list
      (fun p=>List.ofFn (fun i=>fractionEq n (p.1.1 i,p.1.2) (p.2.1 i,p.2.2))) :=
    hn.transportOutput (fun _=>rfl)
  exact (hl.comp (ListPredicateMachines.fp_any BitEncoding.bool Bool.not
    (fp_bool_unary BitEncoding.bool Bool.not))).comp (fp_bool_unary BitEncoding.bool Bool.not)

theorem equality_value_iff {K:Type} [Field K] [Algebra (RationalFunction n) K]
    (basis:Module.Basis (Fin e) (RationalFunction n) K) (a b:Code n e)
    (ha:Valid n a) (hb:Valid n b) : equality n e (a,b)=true ↔ value basis a=value basis b := by
  rw [equality_iff_coordinates]
  constructor
  · intro h
    apply congrArg basis.equivFun.symm
    funext i
    exact (fractionEq_value_iff n (a.1 i,a.2) (b.1 i,b.2) ha hb).mp (h i)
  · intro h i
    have he:coordinates n a=coordinates n b:=basis.equivFun.symm.injective h
    exact (fractionEq_value_iff n (a.1 i,a.2) (b.1 i,b.2) ha hb).mpr (congrFun he i)

end PlanarHom.FixedRealExtension
