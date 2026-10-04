import PlanarHom.RadialPottsNumericIncidence
import PlanarHom.RadialPottsOutputMachine
import PlanarHom.PottsMarkedIncidence
import PlanarHom.RadialPottsCoefficientTutte

/-! The actual ordinary radial coefficient query and its exact value. Its graph
is physically assembled, long occurrences are stretched, and labels erased. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPotts.Numeric
open Complexity Assembly MultiGraph RadialPottsTile PottsCentered FinitePermutationCycles PottsTwoStageInterpolation
variable {m k : ℕ}

 def pathPrivateCount (p : Input) : ℕ := 4*p.2.1^2*p.1
 def coefficientDegree (p : Input) : ℕ :=
  (pathPrivateCount p+1)*(2*p.2.1*(p.2.1+1)*p.1)+2*p.2.1^2*p.1
 def query (p : Input) : MixedCode := stretchedCode (output p) (pathPrivateCount p)

 theorem query_valid (rotation : Equiv.Perm (Medial.Dart (Fin m))) :
    (query (input rotation k)).Valid 1 0 := stretchedCode_valid _ (output_valid rotation) _

 theorem query_planar (rotation : Equiv.Perm (Medial.Dart (Fin m)))
    (hp : (Assembly.graph rotation k).Planar) : (query (input rotation k)).PlanarValid 1 0 :=
  stretchedCode_planar _ (output_planar rotation hp) _

 theorem query_polynomial (rotation : Equiv.Perm (Medial.Dart (Fin m))) (q : ℕ) (hq : 0<q) :
    polynomial ((query (input rotation k)).toMultiGraph (query_valid rotation)) q=
      markedPolynomial (Assembly.graph rotation k) q (longEdges (Fin m) k) (4*k^2*m+1) := by
  change polynomial ((stretchedCode (output (input rotation k)) (pathPrivateCount (input rotation k))).toMultiGraph
    (stretchedCode_valid _ (output_valid rotation) _)) q=_
  rw [stretchedCode_polynomial _ (output_valid rotation) q _ hq]
  exact markedPolynomial_incidence (incidenceEquiv rotation) _ _ (longPositions_iff rotation) q _

 theorem shortCount (E : Type) [Fintype E] (k : ℕ) :
    (Finset.univ\longEdges E k).card=4*k^2*Fintype.card E := by
  rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_prod,
    RadialPottsTile.card_edge,longEdges_card]
  rw [show Fintype.card E*(4*k^2+2*k*(k+1))=
    4*k^2*Fintype.card E+2*k*(k+1)*Fintype.card E by ring,Nat.add_sub_cancel]

/-- A genuine full Euler identity for the actual source rotation suffices;
all hereditary selected identities and coefficient semantics are derived. -/
theorem query_coefficient (V : Type) [Fintype V] (G : MultiGraph V (Fin m))
    (rotation : Equiv.Perm (Medial.Dart (Fin m)))
    (hcycles : ∀a b,rotation.SameCycle a b ↔ G.dartVertex a=G.dartVertex b)
    (hsurj : Function.Surjective G.dartVertex)
    (hfull : Fintype.card V+count (subsetBoundary rotation Finset.univ)=m+2*G.componentCount Finset.univ)
    (q : ℕ) (hq : 1<q) (hk : 0<k) :
    (polynomial ((query (input rotation k)).toMultiGraph (query_valid rotation)) q).coeff
      (coefficientDegree (input rotation k))=radialValue G ((q:ℚ)-1) k := by
  rw [query_polynomial rotation q (by omega)]
  have h := marked_coefficient_eq_radialValue G rotation hcycles hsurj (by simpa using hfull)
    q (4*k^2*m+1) hq hk (by rw [shortCount]; simp only [Fintype.card_fin]; omega)
  simpa [coefficientDegree,pathPrivateCount,input,longEdges_card] using h

 theorem fp_pathPrivateCount : FP inputEncoding BitEncoding.unaryNat pathPrivateCount := by
  have hm := PairProjectionMachines.fp_fst BitEncoding.unaryNat (BitEncoding.unaryNat.prod BitEncoding.nat.list)
  have hk := (PairProjectionMachines.fp_snd BitEncoding.unaryNat (BitEncoding.unaryNat.prod BitEncoding.nat.list)).comp
    (PairProjectionMachines.fp_fst BitEncoding.unaryNat BitEncoding.nat.list)
  have hkk := (hk.pair hk).comp UnaryPolynomialMachines.fp_mul
  have hw := ((fp_const inputEncoding BitEncoding.unaryNat 4).pair hkk).comp UnaryPolynomialMachines.fp_mul
  exact ((hw.pair hm).comp UnaryPolynomialMachines.fp_mul).congr
    (fun _ => by simp only [pathPrivateCount,pow_two,Function.comp_apply])

 theorem fp_query : FP inputEncoding MixedCode.encoding query :=
  (fp_pathPrivateCount.pair fp_output).comp fp_stretchedCode
end PlanarHom.RadialPotts.Numeric
