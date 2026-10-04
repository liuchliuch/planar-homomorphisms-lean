import PlanarHom.Boolean

/-! NEW exact finite Boolean Fourier/Gauss algebra over any commutative ring.
The 4^g signed sector reconstruction is an algebraic identity. Connecting its
sector signs to actual Pfaffians requires a separate quadratic sign theorem. -/
namespace PlanarHom.SurfaceBooleanGauss
open scoped BigOperators
variable {K : Type*} [CommRing K]

abbrev Bits (g : ℕ) := Fin g→Bool
abbrev Phase (g : ℕ) := Bits g×Bits g

def bitSign (s x : Bool) : K := if s&&x then -1 else 1

theorem bitSign_symm (s x : Bool) : bitSign (K:=K) s x=bitSign x s := by
  cases s <;> cases x <;> rfl

theorem bitSign_mul_self (s x : Bool) : bitSign (K:=K) s x*bitSign s x=1 := by
  cases s <;> cases x <;> simp [bitSign]

theorem bitSign_orthogonality (s t : Bool) :
    (∑x : Bool,bitSign (K:=K) s x*bitSign t x)=if s=t then 2 else 0 := by
  cases s <;> cases t <;> simp [Fintype.sum_bool,bitSign] <;> ring

def character {g : ℕ} (s x : Bits g) : K := ∏i,bitSign (s i) (x i)

theorem character_symm {g : ℕ} (s x : Bits g) : character (K:=K) s x=character x s := by
  simp only [character,bitSign_symm]

theorem character_mul_self {g : ℕ} (s x : Bits g) : character (K:=K) s x*character s x=1 := by
  simp only [character,←Finset.prod_mul_distrib,bitSign_mul_self,Finset.prod_const_one]

theorem character_orthogonality {g : ℕ} (s t : Bits g) :
    (∑x : Bits g,character (K:=K) s x*character t x)=if s=t then (2:K)^g else 0 := by
  classical
  simp only [character,←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun (i:Fin g) (x:Bool)=>bitSign (K:=K) (s i) x*bitSign (t i) x)]
  simp only [bitSign_orthogonality]
  by_cases h:s=t
  · subst t
    simp
  · simp only [h,↓reduceIte]
    obtain ⟨i,hi⟩ : ∃i,s i≠t i := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The hyperbolic quadratic Gauss transform, including g=0. -/
theorem character_gauss {g : ℕ} (x y : Bits g) :
    (∑u : Bits g,∑v : Bits g,
      character (K:=K) u v*character u x*character v y)=(2:K)^g*character x y := by
  classical
  calc
    _ = ∑u : Bits g,character u x*(∑v : Bits g,character u v*character y v) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [character_symm v y]
      ring
    _ = ∑u : Bits g,character u x*(if u=y then (2:K)^g else 0) := by
      simp_rw [character_orthogonality]
    _ = (2:K)^g*character x y := by simp [character_symm,mul_comm]

/-- Explicit sign of the canonical quadratic refinement indexed by q. -/
def quadraticSign {g : ℕ} (q z : Phase g) : K :=
  character z.1 z.2*character q.1 z.1*character q.2 z.2

def arfSign {g : ℕ} (q : Phase g) : K := character q.1 q.2

theorem sum_arf_quadraticSign {g : ℕ} (z : Phase g) :
    (∑q : Phase g,arfSign (K:=K) q*quadraticSign q z)=(2:K)^g := by
  classical
  rw [Fintype.sum_prod_type]
  unfold arfSign quadraticSign
  calc
    _ = character z.1 z.2*(∑u : Bits g,∑v : Bits g,
        character u v*character u z.1*character v z.2) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = character z.1 z.2*((2:K)^g*character z.1 z.2) := by rw [character_gauss]
    _ = (2:K)^g := by rw [mul_left_comm,character_mul_self,mul_one]

/-- A finite signed transform of an arbitrary actual sector-weight table. -/
def signedSectorSum {g : ℕ} (weights : Phase g→K) (q : Phase g) : K :=
  ∑z : Phase g,quadraticSign q z*weights z

/-- The exact signed 4^g-term reconstruction, with no Pfaffian premise. -/
theorem gauss_reconstruction {g : ℕ} (weights : Phase g→K) :
    (∑q : Phase g,arfSign q*signedSectorSum weights q)=(2:K)^g*(∑z : Phase g,weights z) := by
  classical
  unfold signedSectorSum
  conv_lhs => simp only [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  calc
    _ = ∑z : Phase g,(∑q : Phase g,arfSign q*quadraticSign q z)*weights z := by
      simp only [Finset.sum_mul]
    _ = (2:K)^g*(∑z : Phase g,weights z) := by
      simp only [sum_arf_quadraticSign]
      exact (Finset.mul_sum _ _ _).symm

theorem card_phase (g : ℕ) : Fintype.card (Phase g)=4^g := by
  simp only [Phase,Bits,Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  rw [←Nat.mul_pow]

/-- Normalization uses only the fixed rational factor 2^(-g). -/
theorem normalized_reconstruction {L : Type*} [Field L] [CharZero L]
    {g : ℕ} (weights : Phase g→L) :
    (∑z : Phase g,weights z)=((2:L)^g)⁻¹*(∑q : Phase g,arfSign q*signedSectorSum weights q) := by
  rw [gauss_reconstruction,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:L)≠0)),one_mul]

end PlanarHom.SurfaceBooleanGauss
