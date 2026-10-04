import PlanarHom.DependentEncodingMachines
import PlanarHom.DependentFieldListMachines
import PlanarHom.MaterializedPowerMachines

/-! Actual uniform powers in bounded-degree materialized dependent fields. -/
noncomputable section
namespace PlanarHom.DependentFieldPowerMachines
open Turing Complexity MachineComposition
open UniformFieldPresentationHeights UniformFieldHeights
variable {X : Type} (ex : BitEncoding X) (K : X → Type)
variable [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
variable (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
local notation "e" => DependentFieldListMachines.fieldEncoding K dimension basis
local notation "ev" => DependentFieldCodecs.sigma ex e
local notation "es" => DependentFieldCodecs.pair ex e

def step (s : Σ x, K x × K x) : Σ x, K x × K x := ⟨s.1,s.2.1,s.2.2*s.2.1⟩

theorem iterate_step (x : X) (a z : K x) (i : ℕ) :
    (step K)^[i] ⟨x,a,z⟩ = ⟨x,a,z*a^i⟩ := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [step, pow_succ, mul_assoc]

theorem fp_step (hmul : FP es ev (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩)) :
    FP es es (step K) := by
  have ha := DependentEncodingMachines.fp_fst ex e e
  have hz := DependentEncodingMachines.fp_snd ex e e
  exact DependentEncodingMachines.fp_pair ex e e ha
    ((DependentEncodingMachines.fp_pair ex e e hz ha).comp hmul)

theorem exists_iteration_bound (c : ℕ) (hc : ∀ x, dimension x ≤ c)
    (hpresentation : FP ex BitEncoding.rat.list (fun x => presentationList (basis x))) :
    ∃ P : Polynomial ℕ, ∀ (n : ℕ) (s : Σ x, K x × K x) (i : ℕ), i ≤ n →
      ((es).encode ((step K)^[i] s)).length ≤ P.eval ((BitEncoding.unaryNat.prod es).encode (n,s)).length := by
  obtain ⟨H,hH⟩ := UniformFieldPresentationFamilies.exists_height_polynomial ex K dimension basis c hc hpresentation
  let Q := (valuePolynomial c).comp (Polynomial.X+H)
  let P := Polynomial.C 4*Polynomial.X+Q+Polynomial.C 2
  refine ⟨P, fun n s i hi => ?_⟩
  rcases s with ⟨x,a,z⟩
  let N := ((BitEncoding.unaryNat.prod es).encode (n,⟨x,a,z⟩)).length
  have hN : N = 2*n+ (2*(ex.encode x).length+(2*((e x).encode a).length+((e x).encode z).length+1)+1)+1 := by
    simp only [N, BitEncoding.prod_length, BitEncoding.unaryNat_length,
      DependentFieldCodecs.pair, DependentFieldCodecs.sigma, List.length_append, BitEncoding.frame_length]
    omega
  have hx : (ex.encode x).length ≤ N := by omega
  have ha : ((e x).encode a).length ≤ N := by omega
  have hz : ((e x).encode z).length ≤ N := by omega
  have hlen : (z :: List.replicate i a).length ≤ N+1 := by simp; omega
  have hcode : ∀ v ∈ z :: List.replicate i a, ((e x).encode v).length ≤ N := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hz
    · simpa only [(List.mem_replicate.mp hv).2] using ha
  have hb := (list_values_encoding_bound (cleared (basis x)) (hc x) (hH x) _ N hlen hcode).1
  have hq : (valuePolynomial c).eval (N+H.eval (ex.encode x).length) ≤ Q.eval N := by
    simp only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
    exact natPolynomial_monotone _ (Nat.add_le_add_left (natPolynomial_monotone H hx) N)
  have hv : ((e x).encode (z*a^i)).length ≤ Q.eval N := by
    simpa only [List.prod_cons,List.prod_replicate] using hb.trans hq
  rw [iterate_step]
  change ((es).encode ⟨x,a,z*a^i⟩).length ≤ P.eval N
  conv_lhs => simp only [DependentFieldCodecs.pair, DependentFieldCodecs.sigma, List.length_append,
    BitEncoding.frame_length, BitEncoding.prod_length]
  change 2*(ex.encode x).length+1+(2*((e x).encode a).length+((e x).encode (z*a^i)).length+1) ≤ P.eval N
  simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

theorem fp_iterate (c : ℕ) (hc : ∀ x, dimension x ≤ c)
    (hpresentation : FP ex BitEncoding.rat.list (fun x => presentationList (basis x)))
    (hmul : FP es ev (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩)) :
    FP (BitEncoding.unaryNat.prod es) es (fun p => (step K)^[p.1] p.2) := by
  obtain ⟨P,hP⟩ := exists_iteration_bound ex K dimension basis c hc hpresentation
  obtain ⟨body⟩ := fp_step ex K dimension basis hmul
  exact ⟨BoundedIterationMachine.computer es (step K) body P hP⟩

/-- The value one is obtained from the supplied effective inclusion in the caller. -/
theorem fp_power (c : ℕ) (hc : ∀ x, dimension x ≤ c)
    (hpresentation : FP ex BitEncoding.rat.list (fun x => presentationList (basis x)))
    (hmul : FP es ev (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩))
    (hone : FP ex ev (fun x => ⟨x,1⟩)) :
    FP (BitEncoding.unaryNat.prod ev) ev (fun p => ⟨p.2.1,p.2.2^p.1⟩) := by
  have hn := PairProjectionMachines.fp_fst BitEncoding.unaryNat ev
  have ha := PairProjectionMachines.fp_snd BitEncoding.unaryNat ev
  have hx := ha.comp (DependentEncodingMachines.fp_parameter ex e)
  have hs := DependentEncodingMachines.fp_pair ex e e ha (hx.comp hone)
  have h := (((hn.pair hs).comp (fp_iterate ex K dimension basis c hc hpresentation hmul)).comp
    (DependentEncodingMachines.fp_snd ex e e))
  exact h.congr (fun p => by
    rcases p with ⟨n,x,a⟩
    change (fun s : Σ x, K x × K x => (⟨s.1,s.2.2⟩ : Σ x, K x)) ((step K)^[n] ⟨x,a,1⟩) = _
    rw [iterate_step]
    simp)

end PlanarHom.DependentFieldPowerMachines
