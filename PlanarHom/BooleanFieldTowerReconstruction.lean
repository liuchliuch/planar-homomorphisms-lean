import PlanarHom.BooleanFieldTowerInverse
import PlanarHom.BooleanFieldTowerEvaluation

/-! Reconstruction and inversion are valid in the represented algebra even
when specialized radicals are squares or algebraically dependent. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerReconstruction
open BooleanFieldTower BooleanFieldTowerAlgebra BooleanFieldTowerInverse
open BooleanFieldTowerEvaluation
variable {K : Type} [Field K]

/-- Each signed specialization is a ring homomorphism on the represented algebra. -/
def evalHom (f : K →+* ℝ) (r : ℕ → ℝ) (D : ℕ → K) (n : ℕ)
    (hr : ∀ i<n,r i^2=f (D i)) (σ : Fin n → Bool) : Carrier D n →+* ℝ where
  toFun p := eval f r n p σ
  map_zero' := by simp only [zero_eq,eval_zero]
  map_one' := by simp only [one_eq,eval_embed,map_one]
  map_add' p q := by simp only [add_eq,eval_add]
  map_mul' p q := by simp only [mul_eq,eval_mul f r D n hr]

theorem norm_ne_zero_of_all_evaluations_ne_zero (f : K →+* ℝ) (r : ℕ → ℝ)
    (D : ℕ → K) (n : ℕ) (hr : ∀ i<n,r i^2=f (D i)) (p : Tower K n)
    (h : ∀ σ,eval f r n p σ≠0) : norm D n p≠0 := by
  intro hz
  have hn := (eval_norm_ne_zero_iff f r D n hr p).mpr h
  exact hn (hz ▸ f.map_zero)

theorem isUnit_of_all_evaluations_ne_zero (f : K →+* ℝ) (r : ℕ → ℝ)
    (D : ℕ → K) (n : ℕ) (hr : ∀ i<n,r i^2=f (D i)) (p : Tower K n)
    (h : ∀ σ,eval f r n p σ≠0) : @IsUnit (Carrier D n) inferInstance p :=
  isUnit_of_norm_ne_zero D n p (norm_ne_zero_of_all_evaluations_ne_zero f r D n hr p h)

theorem eval_inverse (f : K →+* ℝ) (r : ℕ → ℝ) (D : ℕ → K) (n : ℕ)
    (hr : ∀ i<n,r i^2=f (D i)) (p : Tower K n) (h : norm D n p≠0)
    (σ : Fin n → Bool) : eval f r n (inverse D n p) σ=(eval f r n p σ)⁻¹ := by
  have he := congrArg (fun q => eval f r n q σ) (mul_inverse D n p h)
  simp only [eval_mul f r D n hr,eval_embed,map_one] at he
  exact eq_inv_of_mul_eq_one_right he

/-- A coefficient in the squarefree monomial indexed by a Boolean mask. -/
def coefficient : (n : ℕ) → Tower K n → (Fin n → Bool) → K
  | 0,p,_ => p
  | n+1,p,σ => if σ (Fin.last n) then coefficient n p.2 (fun i=>σ i.castSucc)
      else coefficient n p.1 (fun i=>σ i.castSucc)

@[simp] theorem coefficient_zero (n : ℕ) (σ : Fin n → Bool) :
    coefficient n (zero n : Tower K n) σ=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coefficient,zero,ih]

omit [Field K] in
@[simp] theorem coefficient_empty (n : ℕ) (p : Tower K n) :
    coefficient n p (fun _=>false)=constantCoeff n p := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coefficient,constantCoeff,ih]

theorem coefficient_embed_nonconstant (n : ℕ) (c : K) (σ : Fin n → Bool)
    (h : ∃ i,σ i=true) : coefficient n (embed n c) σ=0 := by
  induction n with
  | zero => obtain ⟨i,_⟩ := h; exact Fin.elim0 i
  | succ n ih =>
    by_cases hl : σ (Fin.last n)=true
    · simp [coefficient,hl,embed]
    · have ht : ∃ i : Fin n,σ i.castSucc=true := by
        obtain ⟨i,hi⟩ := h
        revert hi
        refine Fin.lastCases ?_ (fun j hj=>?_) i
        · exact fun hi=>False.elim (hl hi)
        · exact ⟨j,hj⟩
      simpa [coefficient,hl,embed] using ih (fun i=>σ i.castSucc) ht

/-- Equality across every real sign forces the represented element to consist
of its constant coefficient, and identifies its common real value. -/
theorem reconstruction (f : K →+* ℝ) (hf : Function.Injective f) (r : ℕ → ℝ)
    (n : ℕ) (hr : ∀ i<n,r i≠0) (p : Tower K n) (a : ℝ)
    (h : ∀ σ,eval f r n p σ=a) :
    p=embed n (constantCoeff n p) ∧ f (constantCoeff n p)=a := by
  induction n with
  | zero => exact ⟨rfl,h (fun i=>Fin.elim0 i)⟩
  | succ n ih =>
    have hs (σ : Fin n→Bool) : eval f r n p.1 σ=a ∧ eval f r n p.2 σ=0 := by
      have hp:=h (Fin.snoc σ false)
      have hm:=h (Fin.snoc σ true)
      simp only [eval_snoc,Bool.false_eq_true,↓reduceIte] at hp hm
      have hd : r n*eval f r n p.2 σ=0 := by linarith
      have hz := (mul_eq_zero.mp hd).resolve_left (hr n (Nat.lt_succ_self n))
      exact ⟨by linarith,hz⟩
    have hrl : ∀ i<n,r i≠0 := fun i hi=>hr i (Nat.lt.step hi)
    have hp1 := ih hrl p.1 (fun σ=>(hs σ).1)
    have hp2 : p.2=zero n := by
      apply allSign_injective f hf r n hrl
      funext σ
      exact (hs σ).2.trans (eval_zero f r n σ).symm
    exact ⟨Prod.ext hp1.1 hp2,hp1.2⟩

theorem nonconstant_coefficients_vanish (f : K →+* ℝ) (hf : Function.Injective f)
    (r : ℕ → ℝ) (n : ℕ) (hr : ∀ i<n,r i≠0) (p : Tower K n) (a : ℝ)
    (h : ∀ σ,eval f r n p σ=a) (μ : Fin n→Bool) (hμ : ∃ i,μ i=true) :
    coefficient n p μ=0 := by
  rw [(reconstruction f hf r n hr p a h).1]
  exact coefficient_embed_nonconstant n _ μ hμ

end PlanarHom.BooleanFieldTowerReconstruction
