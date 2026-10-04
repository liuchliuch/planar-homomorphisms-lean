import PlanarHom.DomainSpectralAvailability
noncomputable section
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.PrescribedDomains PlanarHom.AlgebraicProductInterpolation

-- The actual full-color source endpoint convention supplies path closure,
-- without a universal-domain assumption on unrelated companion constraints.
example {bt dt : ℕ} (B : Fin bt → Fin dt → Fin dt → Prop) (old : Fin bt)
    (full : Fin dt) (htype : ∀ x y, B old x y → x=full ∧ y=full)
    (x y : Fin dt) (h : B old x y) : PathDomainTyping B old full x y :=
  pathDomainTyping_of_full_endpoints B old full htype x y h

-- Both source-level endpoints consume the original supplied source oracle.
example {q bt ut dt : ℕ} (L : RealLanguage q bt ut) (hunit : ∀ i, L.weights i=1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ) (htype : ∀ x y, B old x y → x=full ∧ y=full)
    (hC : (L.matrices old).PosSemidef) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainRangeTargetProblem D B T old hC) base :=
  L.lemma33_domain_range hunit D B T old full hfull htype hC base available

-- Zero and negative rational exponents need no added endpoint or pinning type.
example {q bt ut dt : ℕ} (L : RealLanguage q bt ut) (hunit : ∀ i, L.weights i=1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ) (htype : ∀ x y, B old x y → x=full ∧ y=full)
    (hC : (L.matrices old).PosDef) (r : ℚ) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainRationalPowerTargetProblem D B T old hC r) base :=
  L.lemma33_domain_rationalPower hunit D B T old full hfull htype hC r base available
