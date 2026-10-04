import PlanarHom.BiasedBinaryProductSeparation
import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace PlanarHom.BiasedBinaryProductSeparation

namespace EdgeCounts

def ofPairs : List (Bool × Bool) → EdgeCounts
  | [] => ⟨0,0,0⟩
  | (false,false)::xs => let s:=ofPairs xs; ⟨s.zeroZero+1,s.mixed,s.oneOne⟩
  | (false,true)::xs => let s:=ofPairs xs; ⟨s.zeroZero,s.mixed+1,s.oneOne⟩
  | (true,false)::xs => let s:=ofPairs xs; ⟨s.zeroZero,s.mixed+1,s.oneOne⟩
  | (true,true)::xs => let s:=ofPairs xs; ⟨s.zeroZero,s.mixed,s.oneOne+1⟩

@[simp] theorem total_ofPairs (xs : List (Bool × Bool)) : (ofPairs xs).total=xs.length := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨x,y⟩
    cases x <;> cases y <;> simp_all [ofPairs,total] <;> omega
end EdgeCounts

section Products
variable {F : Type*} [Field F]

def pairWeight (a b c : F) : Bool × Bool → F
  | (false,false) => a
  | (false,true) => b
  | (true,false) => b
  | (true,true) => c

def bitWeight (h₀ h₁ : F) (x : Bool) : F := if x then h₁ else h₀

def edgeProduct (xs : List (Bool × Bool)) (a b c : F) : F :=
  (xs.map (pairWeight a b c)).prod

def bitProduct (xs : List Bool) (h₀ h₁ : F) : F :=
  (xs.map (bitWeight h₀ h₁)).prod

def incidenceProduct (xs : List (Bool × Bool)) (h₀ h₁ : F) : F :=
  (xs.map (fun p => bitWeight h₀ h₁ p.1*bitWeight h₀ h₁ p.2)).prod

theorem edgeProduct_eq (xs : List (Bool × Bool)) (a b c : F) :
    edgeProduct xs a b c=(EdgeCounts.ofPairs xs).product a b c := by
  induction xs with
  | nil => simp [edgeProduct,EdgeCounts.ofPairs,EdgeCounts.product]
  | cons p xs ih =>
    rcases p with ⟨x,y⟩
    cases x <;> cases y <;>
      simp_all [edgeProduct,pairWeight,EdgeCounts.ofPairs,EdgeCounts.product,pow_succ] <;> ring

theorem incidenceProduct_eq (xs : List (Bool × Bool)) (h₀ h₁ : F) :
    incidenceProduct xs h₀ h₁=(EdgeCounts.ofPairs xs).endpointProduct h₀ h₁ := by
  rw [EdgeCounts.endpointProduct,← edgeProduct_eq]
  unfold incidenceProduct edgeProduct
  congr 1
  apply List.map_congr_left
  rintro ⟨x,y⟩ _
  cases x <;> cases y <;> simp [pairWeight,bitWeight,mul_comm]

theorem bitProduct_eq (xs : List Bool) (h₀ h₁ : F) :
    bitProduct xs h₀ h₁=h₀^(xs.count false)*h₁^(xs.count true) := by
  induction xs with
  | nil => simp [bitProduct]
  | cons x xs ih =>
    cases x <;> simp_all [bitProduct,bitWeight,pow_succ] <;> ring

@[simp] theorem bit_counts_total (xs : List Bool) :
    xs.count false+xs.count true=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all <;> omega
end Products

section Separation
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The three literal products used by parallel edges, incidence leaves and
marked-vertex leaves identify the edge histogram and both marked counts. -/
theorem list_counts_of_joint_products
    (xs ys : List (Bool × Bool)) (us vs : List Bool) (a b c : F)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hbias : a≠c) (hdet : a*c≠b^2)
    (helen : xs.length=ys.length) (hmlen : us.length=vs.length)
    (he : edgeProduct xs a b c=edgeProduct ys a b c)
    (hi : incidenceProduct xs (a+b) (b+c)=incidenceProduct ys (a+b) (b+c))
    (hm : bitProduct us (a+b) (b+c)=bitProduct vs (a+b) (b+c)) :
    EdgeCounts.ofPairs xs=EdgeCounts.ofPairs ys ∧
      us.count false=vs.count false ∧ us.count true=vs.count true := by
  rw [edgeProduct_eq,edgeProduct_eq] at he
  rw [incidenceProduct_eq,incidenceProduct_eq] at hi
  have heq := EdgeCounts.eq_of_joint_products _ _ a b c ha hb hc hbias hdet
    (by simpa using helen) he hi
  rw [bitProduct_eq,bitProduct_eq] at hm
  have hne : a+b≠b+c := by intro h; apply hbias; linarith
  exact ⟨heq,two_product_counts (a+b) (b+c) (add_pos ha hb) (add_pos hb hc) hne
    _ _ _ _ (by simpa using hmlen) hm⟩

/-- Any target symmetric binary interaction and marked unary activity are
compatible with the actual three source products, including NAND and -1. -/
theorem list_target_compatible {T : Type*} [Field T]
    (xs ys : List (Bool × Bool)) (us vs : List Bool) (a b c : F)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hbias : a≠c) (hdet : a*c≠b^2)
    (helen : xs.length=ys.length) (hmlen : us.length=vs.length)
    (he : edgeProduct xs a b c=edgeProduct ys a b c)
    (hi : incidenceProduct xs (a+b) (b+c)=incidenceProduct ys (a+b) (b+c))
    (hm : bitProduct us (a+b) (b+c)=bitProduct vs (a+b) (b+c))
    (x y z h₀ h₁ : T) :
    edgeProduct xs x y z*bitProduct us h₀ h₁=
      edgeProduct ys x y z*bitProduct vs h₀ h₁ := by
  obtain ⟨heq,h₀eq,h₁eq⟩ := list_counts_of_joint_products xs ys us vs a b c ha hb hc
    hbias hdet helen hmlen he hi hm
  simp only [edgeProduct_eq,bitProduct_eq,heq,h₀eq,h₁eq]
end Separation
end PlanarHom.BiasedBinaryProductSeparation
