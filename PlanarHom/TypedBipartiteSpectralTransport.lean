import PlanarHom.TypedBipartiteSpectralAvailability

/-! Unused entries of a typed matrix are immaterial on every promised raw word.
This lets a same-X block use any mathematical completion on the other side,
without sending those entries to a typed oracle. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.TypedBipartiteSpectral
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases
variable {C R : Type} [Fintype C] [CommSemiring R]
variable {bt ut dt : ℕ}

/-- Matrix entries need agree only at the prescribed, permitted endpoints. -/
theorem evaluateRestricted_congr (M N : Fin bt → Matrix C C R)
    (U : Fin ut → C → R) (w : C → R) (D : Fin dt → Set C)
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (hMN : ∀ l x y,B l x y → ∀ i∈D x,∀ j∈D y,M l i j=N l i j)
    (g : MixedCode) (hg : g.Valid bt ut) (δ : Fin g.vertices → Fin dt)
    (ht : Typed B T g hg δ) :
    evaluateRestricted g hg M U w D δ=evaluateRestricted g hg N U w D δ := by
  unfold evaluateRestricted
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs with hs
  · congr 2
    apply congrArg List.prod
    apply List.map_congr_left
    intro e he
    have hb := hg.1 e he
    simp only [binaryValue,hb.1,hb.2.1,hb.2.2,and_self,↓reduceDIte]
    exact hMN _ _ _ (ht.1 e he) _ (hs _) _ (hs _)
  · rfl

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

/-- Equality holds for every alternate decodable word, not just canonical
encodings or a chosen domain assignment representation. -/
theorem domain_value_congr (basis : Module.Basis (Fin dimension) ℚ K)
    (M N : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop)
    (hMN : ∀ l x y,B l x y → ∀ i∈D x,∀ j∈D y,M l i j=N l i j)
    (raw : Bits) (hr : EncodedInput B T raw) :
    (domainEvaluationProblem basis M U w D B T).value raw=
      (domainEvaluationProblem basis N U w D B T).value raw := by
  obtain ⟨g,hg,δ,ht,_,hd⟩ := hr
  change evaluationValue basis M (extendedUnaries U D) w raw=
    evaluationValue basis N (extendedUnaries U D) w raw
  rw [evaluationValue_decode basis M _ w raw _ hd (withDomains_valid g hg δ),
    evaluationValue_decode basis N _ w raw _ hd (withDomains_valid g hg δ),
    evaluate_withDomains g hg M U w D δ,evaluate_withDomains g hg N U w D δ]
  exact congrArg _ (evaluateRestricted_congr M N U w D B T hMN g hg δ ht)

variable {X Y : Type}

/-- Normalize only the selected, intrinsically same-side matrix. -/
def supportedContext (M : Fin bt → Matrix (X ⊕ Y) (X ⊕ Y) K)
    (old : Fin bt) (A : Matrix X X K) : Fin bt → Matrix (X ⊕ Y) (X ⊕ Y) K :=
  fun l=>if l=old then zeroExtend A else M l

@[simp] theorem supportedContext_self (M : Fin bt → Matrix (X ⊕ Y) (X ⊕ Y) K)
    (old : Fin bt) (A : Matrix X X K) : supportedContext M old A old=zeroExtend A := by
  simp [supportedContext]

@[simp] theorem supportedContext_other (M : Fin bt → Matrix (X ⊕ Y) (X ⊕ Y) K)
    (old l : Fin bt) (A : Matrix X X K) (hl : l≠old) : supportedContext M old A l=M l := by
  simp [supportedContext,hl]

theorem supportedContext_congr (M : Fin bt → Matrix (X ⊕ Y) (X ⊕ Y) K)
    (old : Fin bt) (A : Matrix X X K)
    (hblock : ∀ i j,M old (.inl i) (.inl j)=A i j)
    (D : Fin dt → Set (X ⊕ Y)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (htype : ∀ x y,B old x y → D x⊆Set.range Sum.inl ∧ D y⊆Set.range Sum.inl) :
    ∀ l x y,B l x y → ∀ i∈D x,∀ j∈D y,
      supportedContext M old A l i j=M l i j := by
  intro l x y hl i hi j hj
  by_cases he : l=old
  · subst l
    obtain ⟨i,rfl⟩ := (htype x y hl).1 hi
    obtain ⟨j,rfl⟩ := (htype x y hl).2 hj
    simpa only [supportedContext_self,zeroExtend_inl] using (hblock i j).symm
  · rw [supportedContext_other M old l A he]

end PlanarHom.TypedBipartiteSpectral
