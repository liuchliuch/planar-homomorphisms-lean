import PlanarHom.SharedChoiceCertificates

/-! Shared coordinate denominators for variable-length products of fixed-size
linear transformations. Every step is linear in the previous numerator and
denominator, so iteration has exponential heights and polynomial bit lengths. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SharedLinearCertificates
open Complexity FieldCoordinateCertificates IntegerCoordinateBounds CanonicalCoordinateHeights
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}

structure Family {I : Type} (f : I → K) where
  cert : ∀ i, Certificate basis (f i)
  same : ∀ i j, (cert i).denominator = (cert j).denominator

namespace Family
variable {I : Type} [Fintype I] {f : I → K}

def Bounded (a : Family (basis:=basis) f) (H : ℕ) : Prop :=
  ∀ i, (a.cert i).Bounded H H

def canonical (f : I → K) : Family (basis:=basis) f where
  cert := SharedChoiceCertificates.common f (fun i => certificate basis (f i))
  same := fun _ _ => rfl

theorem canonical_bounded (f : I → K) (H : ℕ) (hH : 1 ≤ H)
    (hf : ∀ i, (certificate basis (f i)).Bounded H H) :
    (canonical (basis:=basis) f).Bounded (H ^ (Fintype.card I + 1)) :=
  SharedChoiceCertificates.common_bounded f _ H hH hf

omit [Fintype I] in
theorem bounded_mono (a : Family (basis:=basis) f) {H H' : ℕ}
    (ha : a.Bounded H) (h : H ≤ H') : a.Bounded H' :=
  fun i => Certificate.bounded_mono _ (ha i) h h

def congr {g : I → K} (h : f = g) (a : Family (basis:=basis) f) : Family (basis:=basis) g :=
  h ▸ a

def sum (a : Family (basis:=basis) f) (i₀ : I) : Certificate basis (∑ i, f i) where
  denominator := (a.cert i₀).denominator
  denominator_pos := (a.cert i₀).denominator_pos
  numerator := fun k => ∑ i, (a.cert i).numerator k
  spec := by
    intro k
    simp only [map_sum, Finset.sum_apply, Finset.mul_sum, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← a.same i i₀]
    exact (a.cert i).spec k

theorem sum_bounded (a : Family (basis:=basis) f) (i₀ : I) {H : ℕ}
    (ha : a.Bounded H) : (a.sum i₀).Bounded (Fintype.card I * H) H := by
  refine ⟨(ha i₀).1, fun k => ?_⟩
  apply (natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : I, H := Finset.sum_le_sum (fun i _ => (ha i).2 k)
    _ = _ := by simp

end Family

variable {I : Type} [Fintype I] [Nonempty I]

def transition (v : I → K) (m : I × I → K) : I → K :=
  fun i => ∑ j, v j * m (i,j)

def step (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {v : I → K} {m : I × I → K} (a : Family (basis:=basis) v)
    (b : Family (basis:=basis) m) : Family (basis:=basis) (transition v m) where
  cert := fun i => Family.sum {
    cert := fun j => Certificate.mul data (a.cert j) (b.cert (i,j))
    same := fun j j' => by simp only [Certificate.mul, a.same j j', b.same (i,j) (i,j')] }
    (Classical.arbitrary I)
  same := by
    intro i i'
    dsimp only [Family.sum, Certificate.mul]
    rw [b.same (i,Classical.arbitrary I) (i',Classical.arbitrary I)]

theorem step_bounded (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {v : I → K} {m : I × I → K} (a : Family (basis:=basis) v)
    (b : Family (basis:=basis) m) {A B : ℕ} (ha : a.Bounded A) (hb : b.Bounded B) :
    (step data a b).Bounded (Fintype.card I * Certificate.heightConstant data * A * B) := by
  intro i
  have h := Family.sum_bounded (basis:=basis) (f:=fun j => v j * m (i,j)) {
    cert := fun j => Certificate.mul data (a.cert j) (b.cert (i,j))
    same := fun j j' => by simp only [Certificate.mul, a.same j j', b.same (i,j) (i,j')] }
    (Classical.arbitrary I) (fun j => Certificate.bounded_mul_uniform data _ _ (ha j) (hb (i,j)))
  refine Certificate.bounded_mono _ h ?_ ?_
  · exact le_of_eq (by ring)
  · have hc : 1 ≤ Fintype.card I := Fintype.card_pos
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left
      (Certificate.heightConstant data * A * B) hc

/-- The fold never clears an accumulator denominator more than once per step. -/
theorem fold_bounded (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (xs : List (I × I → K)) (B : ℕ)
    (hm : ∀ m ∈ xs, ∃ b : Family (basis:=basis) m, b.Bounded B)
    (v : I → K) (a : Family (basis:=basis) v) (A : ℕ) (ha : a.Bounded A) :
    ∃ c : Family (basis:=basis) (xs.foldl transition v),
      c.Bounded (A * (Fintype.card I * Certificate.heightConstant data * B) ^ xs.length) := by
  induction xs generalizing v a A with
  | nil => simpa using Exists.intro a ha
  | cons m xs ih =>
    obtain ⟨b,hb⟩ := hm m List.mem_cons_self
    have hs := step_bounded data a b ha hb
    obtain ⟨c,hc⟩ := ih (fun t ht => hm t (List.mem_cons_of_mem _ ht)) _ (step data a b)
      _ hs
    refine ⟨c, ?_⟩
    convert hc using 1
    simp only [List.length_cons, pow_succ]
    ring

def heightBase (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (I : Type) [Fintype I] : ℕ := max (MaterializedFieldHeights.heightBase data) (Fintype.card I)

def choiceExponent (I : Type) [Fintype I] : ℕ :=
  Fintype.card I + Fintype.card (I × I) + 2

/-- All coordinates of a materialized linear fold have polynomial bit bounds.
The two size parameters charge the number of steps and each input entry. -/
theorem fold_encoding_bound
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (xs : List (I × I → K)) (v : I → K) (N L : ℕ) (hlen : xs.length ≤ N)
    (hv : ∀ i, ((numberFieldEncoding basis).encode (v i)).length ≤ L)
    (hm : ∀ m ∈ xs, ∀ i, ((numberFieldEncoding basis).encode (m i)).length ≤ L)
    (i : I) :
    ((numberFieldEncoding basis).encode ((xs.foldl transition v) i)).length ≤
      (EncodingSizeBounds.coordinateOutputPolynomial dimension (heightBase data I)
        (heightBase data I)).eval ((choiceExponent I * L + 2) * (N + 1)) := by
  let B := heightBase data I
  let c := choiceExponent I
  have hB : 0 < B := (MaterializedFieldHeights.heightBase_pos data).trans_le (Nat.le_max_left _ _)
  have hcanon : 2 ^ (dimension+1) ≤ B :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))
  have hcard : Fintype.card I ≤ B := Nat.le_max_right _ _
  have hC : Certificate.heightConstant data ≤ B :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))
  have hbase (J : Type) [Fintype J] (f : J → K)
      (hf : ∀ j, ((numberFieldEncoding basis).encode (f j)).length ≤ L)
      (hJ : Fintype.card J + 1 ≤ c) :
      (Family.canonical (basis:=basis) f).Bounded (B ^ (c*L)) := by
    have hc : ∀ j, (certificate basis (f j)).Bounded (B^L) (B^L) := by
      intro j
      exact Certificate.bounded_mono _ (certificate_bounded_by_input basis _ L (hf j))
        (Nat.pow_le_pow_left hcanon _) (Nat.pow_le_pow_left hcanon _)
    apply Family.bounded_mono _ (Family.canonical_bounded f _ (Nat.one_le_pow _ _ hB) hc)
    rw [← pow_mul]
    apply Nat.pow_le_pow_right hB
    nlinarith
  have hav := hbase I v hv (by dsimp [c,choiceExponent]; omega)
  have ham : ∀ m ∈ xs, ∃ a : Family (basis:=basis) m, a.Bounded (B^(c*L)) := by
    intro m hm'
    exact ⟨Family.canonical m,hbase (I×I) m (hm m hm') (by dsimp [c,choiceExponent]; omega)⟩
  obtain ⟨a,ha⟩ := fold_bounded data xs (B^(c*L)) ham v
    (Family.canonical v) _ hav
  have hg : Fintype.card I * Certificate.heightConstant data * B^(c*L) ≤ B^(c*L+2) := by
    calc
      _ ≤ B * B * B^(c*L) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hcard hC)
      _ = _ := by rw [pow_add,pow_two]; ring
  have hh : B^(c*L) * (Fintype.card I * Certificate.heightConstant data * B^(c*L))^xs.length
      ≤ B^((c*L+2)*(N+1)) := by
    calc
      _ ≤ B^(c*L) * (B^(c*L+2))^xs.length :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hg _)
      _ = B^(c*L+(c*L+2)*xs.length) := by rw [←pow_mul,←pow_add]
      _ ≤ _ := Nat.pow_le_pow_right hB (by
        have h := Nat.mul_le_mul_left (c*L+2) hlen
        nlinarith)
  exact Certificate.encoding_length_le (a.cert i) (Certificate.bounded_mono _ (ha i) hh hh)

end PlanarHom.SharedLinearCertificates
