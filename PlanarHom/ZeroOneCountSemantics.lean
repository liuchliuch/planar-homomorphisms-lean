import PlanarHom.ZeroOneSharpPMembership
import PlanarHom.IncidencePartition
import PlanarHom.EncodingSizeBounds
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! NEW literal natural-count/partition equality and raw answer-size bounds. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.ZeroOneSharpPMembership
open Complexity

theorem count_eq_evaluate {S:Type} [CommSemiring S] (q:ℕ) (R:Relation q) (g:GraphCode) (hg:g.Valid) :
    (count q R g hg:S)=g.evaluate hg (fun i j=>if R i j then 1 else 0) (fun _=>1) := by
  letI : DecidableEq (Fin g.vertices) := Classical.decEq _
  unfold GraphCode.evaluate MultiGraph.partition MultiGraph.assignmentWeight
  simp only [Finset.prod_const_one,one_mul,Fintype.prod_boole]
  simp only [count,Hom,IsHom,Fintype.card_subtype]
  convert (Finset.natCast_card_filter (R:=S) (IsHom q R g hg) Finset.univ) using 1
  · congr 1
    congr 1
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,IsHom]
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hx:IsHom q R g hg x <;> simp [IsHom] at hx ⊢ <;> simp [hx]

theorem totalCount_eq_evaluate {S:Type} [CommSemiring S] (q:ℕ) (R:Relation q)
    (raw:Bits) (g:GraphCode) (hd:GraphCode.encoding.decode raw=some g) (hg:g.Valid) :
    (totalCount q R raw:S)=g.evaluate hg (fun i j=>if R i j then 1 else 0) (fun _=>1) := by
  rw [totalCount_decode q R raw g hd hg]
  exact count_eq_evaluate q R g hg

theorem count_le (q:ℕ) (R:Relation q) (g:GraphCode) (hg:g.Valid) : count q R g hg≤q^g.vertices := by
  have h:=Fintype.card_subtype_le (IsHom q R g hg)
  simpa [count,Hom,Fintype.card_fun] using h

def outputPolynomial (q:ℕ) : Polynomial ℕ := Polynomial.C (14*Nat.size q+1)*(Polynomial.X+1)

theorem totalCount_output_bound (q:ℕ) (R:Relation q) (raw:Bits) :
    (BitEncoding.nat.encode (totalCount q R raw)).length≤(outputPolynomial q).eval raw.length := by
  cases hd:GraphCode.encoding.decode raw with
  | none=>
    simp only [totalCount,hd]
    exact (encodeNat_length_le 0).trans (Nat.zero_le _)
  | some g=>
    by_cases hg:g.Valid
    · rw [totalCount_decode q R raw g hd hg]
      have hc:=EncodingSizeBounds.nat_encoding_length_le_of_le_pow (count_le q R g hg)
      have hv:=GraphCode.raw_size_le raw g hd
      have hm:=Nat.mul_le_mul_left (Nat.size q) (show g.vertices≤14*(raw.length+1) by omega)
      simp only [outputPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one]
      nlinarith
    · simp only [totalCount,hd,dif_neg hg]
      exact (encodeNat_length_le 0).trans (Nat.zero_le _)
end PlanarHom.ZeroOneSharpPMembership
