import PlanarHom.BooleanQuadraticGauss

/-! NEW dense quadratic coefficient algebra over the actual two-element field. -/
namespace PlanarHom.BooleanQuadratic
open scoped BigOperators
abbrev F₂ := ZMod 2

def bit (b : Bool) : F₂ := if b then 1 else 0
@[simp] theorem bit_false : bit false=0 := rfl
@[simp] theorem bit_true : bit true=1 := rfl
@[simp] theorem bit_and (a b : Bool) : bit (a && b)=bit a*bit b := by
  cases a <;> cases b <;> simp [bit]
@[simp] theorem bit_xor (a b : Bool) : bit (xor a b)=bit a+bit b := by
  cases a <;> cases b <;> decide

theorem square (x : F₂) : x*x=x := by fin_cases x <;> decide
theorem add_self (x : F₂) : x+x=0 := by fin_cases x <;> decide

def form {V : Type*} (s : Finset V) (c : F₂) (l : V → F₂)
    (a : V → V → F₂) (x : V → F₂) : F₂ :=
  c+(∑i∈s,l i*x i)+∑i∈s,∑j∈s,a i j*x i*x j

def affine {V : Type*} (s : Finset V) (c : F₂) (l x : V → F₂) : F₂ :=
  c+∑i∈s,l i*x i

theorem form_extract {V : Type*} [DecidableEq V] (s : Finset V) (i : V) (hi : i∈s)
    (c : F₂) (l : V → F₂) (a : V → V → F₂) (x : V → F₂) :
    form s c l a x = form (s.erase i) c l a x +
      (l i+a i i)*x i + ∑k∈s.erase i,(a i k+a k i)*x i*x k := by
  unfold form
  rw [←Finset.sum_erase_add s (fun k=>l k*x k) hi]
  rw [←Finset.sum_erase_add s (fun k=>∑j∈s,a k j*x k*x j) hi]
  simp_rw [←Finset.sum_erase_add s (fun j=>a _ j*x _*x j) hi]
  rw [Finset.sum_add_distrib]
  have hdiag : a i i*x i*x i=a i i*x i := by rw [mul_assoc,square]
  rw [hdiag]
  simp only [add_mul,Finset.sum_add_distrib]
  have hcomm : (∑k∈s.erase i,a k i*x k*x i) = ∑k∈s.erase i,a k i*x i*x k := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hcomm]
  ring

/-- Product of two affine rows remains a dense quadratic form. No division or
rank assumption occurs in this coefficient identity. -/
theorem affine_product {V : Type*} (s : Finset V) (c d : F₂) (l m x : V → F₂) :
    affine s c l x * affine s d m x =
      c*d + (∑i∈s,(c*m i+d*l i)*x i) +
        ∑i∈s,∑j∈s,(l i*m j)*x i*x j := by
  have hh : (∑i∈s,l i*x i)*(∑j∈s,m j*x j) =
      ∑i∈s,∑j∈s,l i*m j*x i*x j := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hc : c*(∑i∈s,m i*x i)=∑i∈s,c*m i*x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hd : d*(∑i∈s,l i*x i)=∑i∈s,d*l i*x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [add_mul,Finset.sum_add_distrib]
  rw [←hh,←hc,←hd]
  unfold affine
  ring

/-- The exact residual coefficients after summing an interacting pair. -/
theorem form_add_affine_product {V : Type*} (s : Finset V) (c d e : F₂)
    (l b h : V → F₂) (a : V → V → F₂) (x : V → F₂) :
    form s c l a x + affine s d b x * affine s e h x =
      form s (c+d*e) (fun i=>l i+d*h i+e*b i)
        (fun i j=>a i j+b i*h j) x := by
  rw [affine_product]
  simp only [form,add_mul,Finset.sum_add_distrib]
  ring

/-- Isolate two actual distinct coordinates of an arbitrary dense form. -/
theorem form_extract_pair {V : Type*} [DecidableEq V]
    (s : Finset V) (i j : V) (hi : i∈s) (hj : j∈s) (hij : j≠i)
    (c : F₂) (l : V → F₂) (a : V → V → F₂) (x : V → F₂) :
    let t := (s.erase i).erase j
    form s c l a x = form t c l a x + (a i j+a j i)*x i*x j +
      x i*affine t (l i+a i i) (fun k=>a i k+a k i) x +
      x j*affine t (l j+a j j) (fun k=>a j k+a k j) x := by
  dsimp only
  have hj' : j∈s.erase i := Finset.mem_erase.mpr ⟨hij,hj⟩
  rw [form_extract s i hi,form_extract (s.erase i) j hj']
  rw [←Finset.sum_erase_add (s.erase i) (fun k=>(a i k+a k i)*x i*x k) hj']
  have hs (v : V) :
      (∑k∈(s.erase i).erase j,(a v k+a k v)*x v*x k) =
      x v*(∑k∈(s.erase i).erase j,(a v k+a k v)*x k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs i,hs j]
  unfold affine
  ring

end PlanarHom.BooleanQuadratic
