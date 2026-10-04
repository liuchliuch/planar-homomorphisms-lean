import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! Joint product separation for an actual biased positive binary interaction.
The extra binary signature is the product of the two one-leaf signatures at
its endpoints. No hardness or interpolation algorithm is assumed here. -/
namespace PlanarHom.BiasedBinaryProductSeparation

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

private theorem two_product_not_lt (a b : F) (ha : 0<a) (hb : 0<b) (hab : a≠b)
    (x y u v : ℕ) (hs : x+y=u+v) (he : a^x*b^y=a^u*b^v) (hy : y<v) : False := by
  let k := v-y
  have hk : 0<k := by dsimp [k]; omega
  have hx : x=u+k := by dsimp [k]; omega
  have hv : v=y+k := by dsimp [k]; omega
  have hc : (a^u*b^y)*a^k=(a^u*b^y)*b^k := by
    calc
      _ = a^(u+k)*b^y := by rw [pow_add]; ring
      _ = a^u*b^(y+k) := by rw [← hx,← hv]; exact he
      _ = _ := by rw [pow_add]; ring
  have hbase : a^u*b^y≠0 := mul_ne_zero (pow_ne_zero _ ha.ne') (pow_ne_zero _ hb.ne')
  exact hab ((pow_left_inj₀ ha.le hb.le (Nat.ne_of_gt hk)).mp (mul_left_cancel₀ hbase hc))

/-- Fixed-length products of two distinct positive values identify both counts. -/
theorem two_product_counts (a b : F) (ha : 0<a) (hb : 0<b) (hab : a≠b)
    (x y u v : ℕ) (hs : x+y=u+v) (he : a^x*b^y=a^u*b^v) : x=u ∧ y=v := by
  have hy : y=v := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact two_product_not_lt a b ha hb hab x y u v hs he h
    · exact two_product_not_lt a b ha hb hab u v x y hs.symm he.symm h
  exact ⟨by omega,hy⟩

@[ext] structure EdgeCounts where
  zeroZero : ℕ
  mixed : ℕ
  oneOne : ℕ
  deriving DecidableEq

namespace EdgeCounts

def total (s : EdgeCounts) : ℕ := s.zeroZero+s.mixed+s.oneOne
def occupiedDegree (s : EdgeCounts) : ℕ := s.mixed+2*s.oneOne

def product (s : EdgeCounts) (a b c : F) : F := a^s.zeroZero*b^s.mixed*c^s.oneOne

def endpointProduct (s : EdgeCounts) (h₀ h₁ : F) : F := s.product (h₀*h₀) (h₀*h₁) (h₁*h₁)

theorem endpointProduct_eq (s : EdgeCounts) (h₀ h₁ : F) :
    s.endpointProduct h₀ h₁=h₀^(2*s.zeroZero+s.mixed)*h₁^s.occupiedDegree := by
  simp only [endpointProduct,product,occupiedDegree,Nat.two_mul,pow_add,mul_pow]
  ring

private theorem product_not_lt (s t : EdgeCounts) (a b c : F)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hdet : a*c≠b^2)
    (hs : s.total=t.total) (hd : s.occupiedDegree=t.occupiedDegree)
    (he : s.product a b c=t.product a b c) (ht : s.oneOne<t.oneOne) : False := by
  let k := t.oneOne-s.oneOne
  have hk : 0<k := by dsimp [k]; omega
  have hz : t.zeroZero=s.zeroZero+k := by dsimp [total,occupiedDegree,k] at *; omega
  have hm : s.mixed=t.mixed+2*k := by dsimp [occupiedDegree,k] at *; omega
  have ho : t.oneOne=s.oneOne+k := by dsimp [k]; omega
  have hp : (a^s.zeroZero*b^t.mixed*c^s.oneOne)*(b^2)^k=
      (a^s.zeroZero*b^t.mixed*c^s.oneOne)*(a*c)^k := by
    calc
      _ = a^s.zeroZero*b^(t.mixed+2*k)*c^s.oneOne := by rw [pow_add,pow_mul]; ring
      _ = a^(s.zeroZero+k)*b^t.mixed*c^(s.oneOne+k) := by
        rw [← hm,← hz,← ho]
        exact he
      _ = _ := by rw [pow_add,pow_add,mul_pow]; ring
  have hn : a^s.zeroZero*b^t.mixed*c^s.oneOne≠0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha.ne') (pow_ne_zero _ hb.ne')) (pow_ne_zero _ hc.ne')
  have hh : b^2=a*c := (pow_left_inj₀ (sq_nonneg b) (mul_pos ha hc).le (Nat.ne_of_gt hk)).mp
    (mul_left_cancel₀ hn hp)
  exact hdet hh.symm

/-- Edge total, occupied degree, and a rank-two positive interaction product
identify every symmetric edge-type count. -/
theorem eq_of_degree_product (s t : EdgeCounts) (a b c : F)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hdet : a*c≠b^2)
    (hs : s.total=t.total) (hd : s.occupiedDegree=t.occupiedDegree)
    (he : s.product a b c=t.product a b c) : s=t := by
  have ho : s.oneOne=t.oneOne := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact product_not_lt s t a b c ha hb hc hdet hs hd he h
    · exact product_not_lt t s a b c ha hb hc hdet hs.symm hd.symm he.symm h
  have hm : s.mixed=t.mixed := by dsimp [occupiedDegree] at hd; omega
  have hz : s.zeroZero=t.zeroZero := by dsimp [total] at hs; omega
  exact EdgeCounts.ext hz hm ho

/-- The actual leaf signature is h=(a+b,b+c). Bias makes its two values
unequal, while nonzero determinant distinguishes the remaining edge statistic. -/
theorem eq_of_joint_products (s t : EdgeCounts) (a b c : F)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hbias : a≠c) (hdet : a*c≠b^2)
    (hs : s.total=t.total) (he : s.product a b c=t.product a b c)
    (hh : s.endpointProduct (a+b) (b+c)=t.endpointProduct (a+b) (b+c)) : s=t := by
  have h₀ : 0<a+b := add_pos ha hb
  have h₁ : 0<b+c := add_pos hb hc
  have hne : a+b≠b+c := by intro h; apply hbias; linarith
  rw [endpointProduct_eq,endpointProduct_eq] at hh
  have hsum : (2*s.zeroZero+s.mixed)+s.occupiedDegree=
      (2*t.zeroZero+t.mixed)+t.occupiedDegree := by dsimp [total,occupiedDegree] at *; omega
  have hd := (two_product_counts (a+b) (b+c) h₀ h₁ hne _ _ _ _ hsum hh).2
  exact eq_of_degree_product s t a b c ha hb hc hdet hs hd he

/-- Consequently joint source products determine every target symmetric binary
product, including a zero entry such as the independent-set/NAND interaction. -/
theorem target_compatible (s t : EdgeCounts) (a b c : F)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hbias : a≠c) (hdet : a*c≠b^2)
    (hs : s.total=t.total) (he : s.product a b c=t.product a b c)
    (hh : s.endpointProduct (a+b) (b+c)=t.endpointProduct (a+b) (b+c))
    (x y z : F) : s.product x y z=t.product x y z := by
  rw [eq_of_joint_products s t a b c ha hb hc hbias hdet hs he hh]

end EdgeCounts
end PlanarHom.BiasedBinaryProductSeparation
