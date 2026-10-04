import PlanarHom.DomainSpectralAvailability
noncomputable section
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.PrescribedDomains PlanarHom.AlgebraicProductInterpolation

-- The endpoint table permits domains 0 and 1 and rejects domain 2.
-- Domain 0 is genuinely narrower than the fixed full internal domain 1.
private def domains : Fin 3 → Set (Fin 2) :=
  fun x => if x=1 then Set.univ else {0}
private def binaryTyping : Fin 1 → Fin 3 → Fin 3 → Prop :=
  fun _ x y => x.val<2 ∧ y.val<2
private def unaryTyping : Fin 0 → Fin 3 → Prop := fun i => Fin.elim0 i

example : domains 0 ≠ domains 1 := by
  intro h
  have hm : (1 : Fin 2) ∈ domains 1 := by simp [domains]
  rw [← h] at hm
  simp [domains] at hm

private theorem pathTyping : ∀ x y, binaryTyping 0 x y →
    PathDomainTyping binaryTyping 0 1 x y := by
  intro x y h
  exact ⟨h,⟨h.1,by decide⟩,⟨by decide,by decide⟩,⟨by decide,h.2⟩⟩

-- This table fails the former full/full endpoint hypothesis.
example : ¬ (∀ x y, binaryTyping 0 x y → x=(1 : Fin 3) ∧ y=1) := by
  intro h
  have h0 := (h 0 0 (by norm_num [binaryTyping])).1
  have : (0 : ℕ)=1 := congrArg Fin.val h0
  omega

-- The general endpoints retain the narrower domain and original source oracle.
example (L : RealLanguage 2 1 0) (hunit : ∀ i, L.weights i=1)
    (hC : (L.matrices 0).PosSemidef) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction
      (L.domainProblem domains binaryTyping unaryTyping) base) :
    PromisePolyTimeTuringReduction
      (L.domainRangeTargetProblem domains binaryTyping unaryTyping 0 hC) base :=
  L.lemma33_domain_range_of_pathTyping hunit domains binaryTyping unaryTyping 0 1
    (by simp [domains]) pathTyping hC base available

example (L : RealLanguage 2 1 0) (hunit : ∀ i, L.weights i=1)
    (hC : (L.matrices 0).PosDef) (r : ℚ) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction
      (L.domainProblem domains binaryTyping unaryTyping) base) :
    PromisePolyTimeTuringReduction
      (L.domainRationalPowerTargetProblem domains binaryTyping unaryTyping 0 hC r) base :=
  L.lemma33_domain_rationalPower_of_pathTyping hunit domains binaryTyping unaryTyping 0 1
    (by simp [domains]) pathTyping hC r base available
