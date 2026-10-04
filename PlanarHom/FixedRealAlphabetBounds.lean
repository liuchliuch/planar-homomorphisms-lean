import PlanarHom.FixedRealAlphabetCode

/-! Polynomial physical-code bounds for every prefix of the cleared fixed
multiplication-matrix recurrence. Both numerator coefficients and the shared
polynomial denominator are charged, including all zero padding. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealAlphabet
open DensePolynomial Complexity
variable {n e t:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable {basis:Module.Basis (Fin e) (RationalFunction n) K} {A:Fin t→K}

structure Bounds (d:Data basis A) where
  W : ℕ
  D : ℕ
  H : ℕ
  C : ℕ
  D_pos : 0<D
  H_le_C : H≤C
  factor_le_C : (e+1)*W^n*H≤C
  denominator : BoxBound n W d.denominator ∧ CoeffBound n D H d.denominator
  initial : ∀i,BoxBound n W (d.initial i) ∧ CoeffBound n D H (d.initial i)
  transition : ∀a i j,BoxBound n W (d.transition a i j) ∧ CoeffBound n D H (d.transition a i j)

theorem exists_bounds (d:Data basis A) : Nonempty (Bounds d) := by
  let family : Option (Fin e ⊕ Fin t×Fin e×Fin e)→Code n
    | none=>d.denominator
    | some (.inl i)=>d.initial i
    | some (.inr (a,i,j))=>d.transition a i j
  obtain ⟨W,D,H,hW,hD,hH,h⟩:=fixed_family_bounds n family
  exact ⟨⟨W,D,H,H+(e+1)*W^n*H,hD,by omega,by omega,h none,
    fun i=>h (some (.inl i)),fun a i j=>h (some (.inr (a,i,j)))⟩⟩

def bounds (d:Data basis A) : Bounds d := Classical.choice (exists_bounds d)

def StateBound {d:Data basis A} (b:Bounds d) (L:ℕ) (s:FixedRealExtension.Code n e) : Prop :=
  (BoxBound n ((b.W+1)*(L+1)) s.2 ∧ CoeffBound n (b.D^(L+1)) (b.C^(L+1)) s.2) ∧
  ∀i,BoxBound n ((b.W+1)*(L+1)) (s.1 i) ∧ CoeffBound n (b.D^(L+1)) (b.C^(L+1)) (s.1 i)

theorem initial_bound (d:Data basis A) (b:Bounds d) : StateBound b 0 (initial d) := by
  have h:∀p:Code n,BoxBound n b.W p ∧ CoeffBound n b.D b.H p→
      BoxBound n ((b.W+1)*(0+1)) p ∧ CoeffBound n (b.D^(0+1)) (b.C^(0+1)) p := by
    intro p hp
    exact ⟨box_mono n (by omega) hp.1,by simpa using coeff_mono n b.D b.H_le_C hp.2⟩
  exact ⟨h _ b.denominator,fun i=>h _ (b.initial i)⟩

theorem step_bound (d:Data basis A) (b:Bounds d) (L:ℕ) (s:FixedRealExtension.Code n e)
    (hs:StateBound b L s) (a:Fin t) : StateBound b (L+1) (step d s a) := by
  have hwidth : b.W+(b.W+1)*(L+1)+1=(b.W+1)*(L+1+1) := by ring
  have hden : b.D*b.D^(L+1)=b.D^(L+1+1) := by rw [pow_succ]; exact Nat.mul_comm _ _
  have hg : b.W^n*b.H≤b.C := by
    have he : b.W^n*b.H≤(e+1)*b.W^n*b.H := by
      simpa only [one_mul,Nat.mul_assoc] using Nat.mul_le_mul_right (b.W^n*b.H) (show 1≤e+1 by omega)
    exact he.trans b.factor_le_C
  have hsum : e*(b.W^n*b.H)≤b.C := by
    have he : e*(b.W^n*b.H)≤(e+1)*b.W^n*b.H := by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (b.W^n*b.H) (show e≤e+1 by omega)
    exact he.trans b.factor_le_C
  have hm {p q:Code n} (hp:BoxBound n b.W p ∧ CoeffBound n b.D b.H p)
      (hq:BoxBound n ((b.W+1)*(L+1)) q ∧ CoeffBound n (b.D^(L+1)) (b.C^(L+1)) q) :
      BoxBound n ((b.W+1)*(L+1+1)) (mul n p q) ∧
      CoeffBound n (b.D^(L+1+1)) (b.W^n*b.H*b.C^(L+1)) (mul n p q) := by
    constructor
    · simpa only [hwidth] using box_mul n _ _ p q hp.1 hq.1
    · simpa only [hden] using coeff_mul n _ _ _ _ _ _ p q hp.1 hq.1 hp.2 hq.2
  constructor
  · have hh:=hm b.denominator hs.1
    refine ⟨hh.1,coeff_mono n _ ?_ hh.2⟩
    calc
      _ ≤ b.C*b.C^(L+1) := Nat.mul_le_mul_right _ hg
      _ = b.C^(L+1+1) := (pow_succ' _ _).symm
  · intro i
    have hh:∀j,BoxBound n ((b.W+1)*(L+1+1)) (mul n (d.transition a i j) (s.1 j)) ∧
        CoeffBound n (b.D^(L+1+1)) (b.W^n*b.H*b.C^(L+1)) (mul n (d.transition a i j) (s.1 j)) :=
      fun j=>hm (b.transition a i j) (hs.2 j)
    constructor
    · apply box_sum
      intro p hp
      obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hp
      exact (hh j).1
    · have hc:=coeff_sum n (b.D^(L+1+1)) (b.W^n*b.H*b.C^(L+1))
        (List.ofFn (fun j=>mul n (d.transition a i j) (s.1 j))) (by
          intro p hp; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hp; exact (hh j).2)
      apply coeff_mono n _ _ hc
      rw [List.length_ofFn]
      calc
        _ = (e*(b.W^n*b.H))*b.C^(L+1) := by ring
        _ ≤ b.C*b.C^(L+1) := Nat.mul_le_mul_right _ hsum
        _ = b.C^(L+1+1) := (pow_succ' _ _).symm

theorem fold_bound (d:Data basis A) (b:Bounds d) (xs:List (Fin t)) (L:ℕ)
    (s:FixedRealExtension.Code n e) (hs:StateBound b L s) :
    StateBound b (L+xs.length) (xs.foldl (step d) s) := by
  induction xs generalizing L s with
  | nil => simpa using hs
  | cons a xs ih =>
    simpa only [List.length_cons,List.foldl_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      ih (L+1) (step d s a) (step_bound d b L s hs a)

theorem word_bound (d:Data basis A) (b:Bounds d) (xs:List (Fin t)) :
    StateBound b xs.length (word d xs) := by
  simpa only [Nat.zero_add] using fold_bound d b xs 0 (initial d) (initial_bound d b)

def sizePolynomial {d:Data basis A} (b:Bounds d) : Polynomial ℕ :=
  let p:=DensePolynomial.sizePolynomial n (Polynomial.C (b.W+1)*Polynomial.X) b.C b.D
  (Polynomial.C 2*((Polynomial.C 2*p+Polynomial.C 3)*Polynomial.C e+1)+p+1).comp (Polynomial.X+1)

theorem state_size {d:Data basis A} (b:Bounds d) (L:ℕ) (s:FixedRealExtension.Code n e)
    (h:StateBound b L s) :
    ((FixedRealExtension.encoding n e).encode s).length≤(sizePolynomial b).eval L := by
  let p:=DensePolynomial.sizePolynomial n (Polynomial.C (b.W+1)*Polynomial.X) b.C b.D
  have hp {q:Code n} (hq:BoxBound n ((b.W+1)*(L+1)) q ∧ CoeffBound n (b.D^(L+1)) (b.C^(L+1)) q) :
      ((encoding n).encode q).length≤p.eval (L+1) :=
    encoded_size_bound n _ _ _ _ b.D_pos q (by simpa using hq.1) hq.2
  have hv:=CoefficientListHeights.list_encoding_length_le (encoding n) (List.ofFn s.1) (p.eval (L+1)) (by
    intro q hq; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq; exact hp (h.2 i))
  rw [List.length_ofFn] at hv
  have hd:=hp h.1
  rw [FixedRealExtension.encoding,BitEncoding.prod_length]
  change 2*((encoding n).list.encode (List.ofFn s.1)).length+((encoding n).encode s.2).length+1≤_
  simp only [sizePolynomial,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  dsimp [p] at hv hd
  omega

theorem word_size (d:Data basis A) (xs:List (Fin t)) :
    ((FixedRealExtension.encoding n e).encode (word d xs)).length≤(sizePolynomial (bounds d)).eval xs.length :=
  state_size _ _ _ (word_bound d (bounds d) xs)

end PlanarHom.FixedRealAlphabet
