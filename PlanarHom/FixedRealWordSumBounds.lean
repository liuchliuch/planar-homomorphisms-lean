import PlanarHom.FixedRealWordSums

/-! NEW polynomial bit size of exponentially many equal-length word sums.
Both clearing layers are explicit: the shared polynomial denominator, and the
single fixed positive rational coefficient denominator D^(L+1). -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealWordSums
open DensePolynomial FixedRealAlphabet Complexity
variable {n e t:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable {basis:Module.Basis (Fin e) (RationalFunction n) K} {A:Fin t→K}

 def SumBound {d:Data basis A} (b:Bounds d) (Q L:ℕ) (s:FixedRealExtension.Code n e) : Prop :=
    (BoxBound n ((b.W+1)*(L+1)) s.2 ∧ CoeffBound n (b.D^(L+1)) ((Q*b.C)^(L+1)) s.2) ∧
      ∀i,BoxBound n ((b.W+1)*(L+1)) (s.1 i) ∧ CoeffBound n (b.D^(L+1)) ((Q*b.C)^(L+1)) (s.1 i)

 theorem sumWords_bound (d:Data basis A) (b:Bounds d) (Q L:ℕ) (hQ:1≤Q)
    (words:List (List (Fin t))) (hlen:∀xs∈words,xs.length=L) (hcard:words.length≤Q^(L+1)) :
    SumBound b Q L (sumWords d L words) := by
  have hw:∀xs∈words,StateBound b L (word d xs):=by
    intro xs hx
    simpa only [hlen xs hx] using word_bound d b xs
  constructor
  · have hd:=denominatorAt_bound d b L
    refine ⟨hd.1,coeff_mono n _ ?_ hd.2⟩
    apply Nat.pow_le_pow_left
    simpa only [one_mul] using Nat.mul_le_mul_right b.C hQ
  · intro i
    constructor
    · apply box_sum
      intro p hp
      obtain ⟨xs,hxs,rfl⟩:=List.mem_map.mp hp
      exact (hw xs hxs).2 i |>.1
    · have hc:=coeff_sum n (b.D^(L+1)) (b.C^(L+1))
        (words.map (fun xs=>(word d xs).1 i)) (by
          intro p hp
          obtain ⟨xs,hxs,rfl⟩:=List.mem_map.mp hp
          exact (hw xs hxs).2 i |>.2)
      apply coeff_mono n _ _ hc
      rw [List.length_map,mul_pow]
      exact Nat.mul_le_mul_right _ hcard

 def outputPolynomial {d:Data basis A} (b:Bounds d) (Q:ℕ) : Polynomial ℕ :=
  let p:=DensePolynomial.sizePolynomial n (Polynomial.C (b.W+1)*Polynomial.X) (Q*b.C) b.D
  (Polynomial.C 2*((Polynomial.C 2*p+Polynomial.C 3)*Polynomial.C e+1)+p+1).comp (Polynomial.X+1)

 theorem sumBound_size {d:Data basis A} (b:Bounds d) (Q L:ℕ) (s:FixedRealExtension.Code n e)
    (h:SumBound b Q L s) :
    ((FixedRealExtension.encoding n e).encode s).length≤(outputPolynomial b Q).eval L := by
  let p:=DensePolynomial.sizePolynomial n (Polynomial.C (b.W+1)*Polynomial.X) (Q*b.C) b.D
  have hp {q:Code n} (hq:BoxBound n ((b.W+1)*(L+1)) q ∧ CoeffBound n (b.D^(L+1)) ((Q*b.C)^(L+1)) q) :
      ((encoding n).encode q).length≤p.eval (L+1) :=
    encoded_size_bound n _ _ _ _ b.D_pos q (by simpa using hq.1) hq.2
  have hv:=CoefficientListHeights.list_encoding_length_le (encoding n) (List.ofFn s.1) (p.eval (L+1)) (by
    intro q hq; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq; exact hp (h.2 i))
  rw [List.length_ofFn] at hv
  have hd:=hp h.1
  rw [FixedRealExtension.encoding,BitEncoding.prod_length]
  change 2*((encoding n).list.encode (List.ofFn s.1)).length+((encoding n).encode s.2).length+1≤_
  simp only [outputPolynomial,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  dsimp [p] at hv hd
  omega

 theorem sumWords_size (d:Data basis A) (Q L:ℕ) (hQ:1≤Q)
    (words:List (List (Fin t))) (hlen:∀xs∈words,xs.length=L) (hcard:words.length≤Q^(L+1)) :
    ((FixedRealExtension.encoding n e).encode (sumWords d L words)).length≤
      (outputPolynomial (bounds d) Q).eval L :=
  sumBound_size _ _ _ _ (sumWords_bound d (bounds d) Q L hQ words hlen hcard)

/-- No input-dependent coordinate, denominator or height certificate is assumed. -/
 theorem exists_sum_representation (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (A:Fin t→K) (Q:ℕ) (hQ:1≤Q) : ∃P:Polynomial ℕ,
    ∀words:List (List (Fin t)),∀L:ℕ,(∀xs∈words,xs.length=L)→words.length≤Q^(L+1)→
      ∃c:FixedRealExtension.Code n e,FixedRealExtension.Valid n c ∧
        FixedRealExtension.value basis c=(words.map (fun xs=>(xs.map A).prod)).sum ∧
          ((FixedRealExtension.encoding n e).encode c).length≤P.eval L := by
  let d:=data basis A
  refine ⟨outputPolynomial (bounds d) Q,?_⟩
  intro words L hlen hcard
  exact ⟨sumWords d L words,sumWords_valid d L words,sumWords_value d L words hlen,
    sumWords_size d Q L hQ words hlen hcard⟩

end PlanarHom.FixedRealWordSums
