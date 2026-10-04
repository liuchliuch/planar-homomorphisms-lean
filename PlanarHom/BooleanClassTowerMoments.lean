import PlanarHom.BooleanTensorRingMap
import PlanarHom.BooleanTowerSpectral
import PlanarHom.BooleanGroupedMetadataMachines

/-! NEW literal grouped spectral moments in the represented radical algebra.
The same signed contraction coefficients are used for source powers and the
retained coordinate class, including loops and an empty selected edge list. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanClassTowerMoments
open BooleanFieldTower BooleanFieldTowerAlgebra BooleanFieldCollision BooleanTowerSpectral
open BooleanTensorSpectral BooleanTensorPartitionMoments Complexity Complexity.MixedCode
variable {K : Type} [Field K] [Algebra ℚ K] {b d bt ut : ℕ}

abbrev D (a w : Fin b→K) (x : K) := radicands a w x

def nodeValue (cls : Fin d→Fin b) (c a w : Fin b→K) (x : K) {m : ℕ}
    (ε : Fin m→Fin d→Bool) : Carrier (D a w x) b :=
  ofTower (D a w x) b (spectral c a w x (BooleanSpectralCounts.total cls m)
    (BooleanSpectralCounts.count cls ε))

theorem spectral_value (c a w : Fin b→K) (x : K) (n k : Fin b→ℕ) :
    ofTower (D a w x) b (spectral c a w x n k) =
      ∏g,(algebraMap K (Carrier (D a w x) b) (c g)+radical (D a w x) g)^(n g-k g)*
        (algebraMap K (Carrier (D a w x) b) (c g)-radical (D a w x) g)^(k g) := by
  change _ = ∏g,(branch (algebraMap K (Carrier (D a w x) b) (c g))
    (radical (D a w x) g) false)^(n g-k g)*
    (branch (algebraMap K (Carrier (D a w x) b) (c g)) (radical (D a w x) g) true)^(k g)
  simp only [branch_eq_linear,Bool.false_eq_true,↓reduceIte,product_eq,mul_eq,pow_eq,
    ofTower,spectral,D]

theorem eigenvalue_product_node (cls : Fin d→Fin b) (c a w : Fin b→K) (x : K)
    {m : ℕ} (ε : Fin m→Fin d→Bool) :
    (∏e,eigenvalue (fun i=>algebraMap K (Carrier (D a w x) b) (c (cls i)))
      (fun i=>radical (D a w x) (cls i)) (ε e)) = nodeValue cls c a w x ε := by
  have h:=eigenvalue_product_counts cls (fun g=>algebraMap K (Carrier (D a w x) b) (c g))
    (fun g=>radical (D a w x) g) ε
  exact h.trans (spectral_value c a w x _ _).symm

def retainedNode (cls : Fin d→Fin b) (c a w : Fin b→K) (x : K) (g0 : Fin b) {m : ℕ}
    (ε : Fin m→Fin d→Bool) : Carrier (D a w x) b :=
  ofTower (D a w x) b (mul (D a w x) b
    (power (D a w x) b (linear b g0 (c g0) 1)
      (BooleanSpectralCounts.total cls m g0-BooleanSpectralCounts.count cls ε g0))
    (power (D a w x) b (linear b g0 (c g0) (-1)) (BooleanSpectralCounts.count cls ε g0)))

theorem retained_product_node (cls : Fin d→Fin b) (c a w : Fin b→K) (x : K)
    (g0 : Fin b) {m : ℕ} (ε : Fin m→Fin d→Bool) :
    (∏e,∏i,if cls i=g0 then branch
      (algebraMap K (Carrier (D a w x) b) (c (cls i)))
      (radical (D a w x) (cls i)) (ε e i) else 1) = retainedNode cls c a w x g0 ε := by
  rw [retained_product_counts cls g0 (fun g=>algebraMap K (Carrier (D a w x) b) (c g))
    (fun g=>radical (D a w x) g) ε]
  have hp:=branch_eq_linear (D a w x) (c g0) g0 false
  have hm:=branch_eq_linear (D a w x) (c g0) g0 true
  simp only [branch,Bool.false_eq_true,↓reduceIte] at hp hm
  rw [hp,hm]
  simp only [retainedNode,ofTower,mul_eq,pow_eq]

def coefficient (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (ω : (Fin d→Bool)→K) (cls : Fin d→Fin b) (a w : Fin b→K) (x : K)
    (z : (Fin g.vertices→Fin d→Bool) × (Fin (g.markedCount selected.val)→Fin d→Bool)) :
    Carrier (D a w x) b :=
  let φ:=algebraMap K (Carrier (D a w x) b)
  rest g hg selected (fun l=>(M l).map φ) (fun l i=>φ (U l i)) (fun i=>φ (ω i))
    (fun i=>φ (a (cls i))) (fun i=>φ (w (cls i)*x)) (fun _=>φ (1/2))
    (fun i=>inverseRadical (D a w x) (cls i)) z

theorem evaluate_power (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (ω : (Fin d→Bool)→K) (cls : Fin d→Fin b) (c a w : Fin b→K) (x : K)
    (hD : ∀i:Fin b,D a w x i.val≠0) (n : ℕ) :
    algebraMap K (Carrier (D a w x) b)
      (g.evaluate hg (replace M selected
        ((tensor (fun i=>block (c (cls i)) (a (cls i)) (w (cls i)*x)))^n)) U ω) =
      ∑z : (Fin g.vertices→Fin d→Bool) × (Fin (g.markedCount selected.val)→Fin d→Bool),
        coefficient g hg selected M U ω cls a w x z * (nodeValue cls c a w x z.2)^n := by
  let φ:=algebraMap K (Carrier (D a w x) b)
  letI : CharZero K := Algebra.charZero_of_charZero ℚ K
  have hh : (1/2:K)+(1/2:K)=1 := by norm_num
  have hr (i : Fin d) : (radical (D a w x) (cls i))^2 =
      (φ (a (cls i)))^2+(φ (w (cls i)*x))^2 := by
    rw [radical_sq]
    change φ ((D a w x) (cls i).val) = _
    simp only [D,radicands,extend_val,mul_pow,φ,_root_.map_add,_root_.map_mul,_root_.map_pow]
  rw [BooleanTensorRingMap.mapped_evaluate_replace,BooleanTensorRingMap.tensor_power_map]
  have h:=BooleanTensorPartitionMoments.evaluate_power g hg selected
    (fun l=>(M l).map φ) (fun l i=>φ (U l i)) (fun i=>φ (ω i))
    (fun i=>φ (c (cls i))) (fun i=>φ (a (cls i))) (fun i=>φ (w (cls i)*x))
    (fun _=>φ (1/2)) (fun i=>inverseRadical (D a w x) (cls i))
    (fun i=>radical (D a w x) (cls i))
    (fun _=>by rw [←_root_.map_add,hh,_root_.map_one])
    (fun i=>radical_mul_inverse _ _ (hD _)) hr n
  dsimp only [φ] at h
  simpa only [eigenvalue_product_node,coefficient] using h

theorem evaluate_retained (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (ω : (Fin d→Bool)→K) (cls : Fin d→Fin b) (c a w : Fin b→K) (x : K)
    (hD : ∀i:Fin b,D a w x i.val≠0) (g0 : Fin b) :
    algebraMap K (Carrier (D a w x) b)
      (g.evaluate hg (replace M selected
        (tensor (fun i=>if cls i=g0 then block (c (cls i)) (a (cls i)) (w (cls i)*x) else 1))) U ω) =
      ∑z : (Fin g.vertices→Fin d→Bool) × (Fin (g.markedCount selected.val)→Fin d→Bool),
        coefficient g hg selected M U ω cls a w x z * retainedNode cls c a w x g0 z.2 := by
  let φ:=algebraMap K (Carrier (D a w x) b)
  letI : CharZero K := Algebra.charZero_of_charZero ℚ K
  have hh : (1/2:K)+(1/2:K)=1 := by norm_num
  have hr (i : Fin d) : (radical (D a w x) (cls i))^2 =
      (φ (a (cls i)))^2+(φ (w (cls i)*x))^2 := by
    rw [radical_sq]
    change φ ((D a w x) (cls i).val) = _
    simp only [D,radicands,extend_val,mul_pow,φ,_root_.map_add,_root_.map_mul,_root_.map_pow]
  let S:=Finset.univ.filter (fun i=>cls i=g0)
  have hs : ∀i:Fin d, i∈S ↔ cls i=g0 := by simp [S]
  simp_rw [←hs]
  rw [BooleanTensorRingMap.mapped_evaluate_replace,BooleanTensorRingMap.tensor_retained_map]
  have h:=BooleanTensorPartitionMoments.evaluate_retained g hg selected
    (fun l=>(M l).map φ) (fun l i=>φ (U l i)) (fun i=>φ (ω i))
    (fun i=>φ (c (cls i))) (fun i=>φ (a (cls i))) (fun i=>φ (w (cls i)*x))
    (fun _=>φ (1/2)) (fun i=>inverseRadical (D a w x) (cls i))
    (fun i=>radical (D a w x) (cls i)) S
    (fun _=>by rw [←_root_.map_add,hh,_root_.map_one])
    (fun i=>radical_mul_inverse _ _ (hD _)) hr
  dsimp only [φ] at h
  simpa only [hs,retained_product_node,coefficient] using h

end PlanarHom.BooleanClassTowerMoments
