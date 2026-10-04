import PlanarHom.DomainSpectralAvailability

/-!
# Spectral interpolation for a matrix defined on the ambient color domain

A full q×q matrix is defined on every pair of colors in [q], so it can be used
between any of the already permitted vertex-domain restrictions. This fixed
language convention is stated explicitly below. It is not a reduction that
turns an arbitrarily restricted endpoint table into an unrestricted one.
Original vertex domain assignments and all companion permissions are retained;
new internal vertices use the already allowed ambient [q] domain.
-/
noncomputable section
namespace PlanarHom.PrescribedDomains
variable {bt dt : ℕ}

/-- The fixed endpoint policy of one globally defined matrix label. Every
other constraint keeps exactly its original endpoint permission table. -/
def withGlobalMatrix (B : Fin bt → Fin dt → Fin dt → Prop) (old : Fin bt) :
    Fin bt → Fin dt → Fin dt → Prop := fun l x y => if l=old then True else B l x y

@[simp] theorem withGlobalMatrix_self (B : Fin bt → Fin dt → Fin dt → Prop)
    (old : Fin bt) (x y : Fin dt) : withGlobalMatrix B old old x y := by
  simp [withGlobalMatrix]

theorem withGlobalMatrix_other (B : Fin bt → Fin dt → Fin dt → Prop)
    (old l : Fin bt) (h : l≠old) : withGlobalMatrix B old l=B l := by
  funext x y
  simp only [withGlobalMatrix,if_neg h]

/-- Path admissibility follows from the actual global-matrix policy; original
endpoints need not have the full internal domain. -/
theorem withGlobalMatrix_pathTyping (B : Fin bt → Fin dt → Fin dt → Prop)
    (old : Fin bt) (full x y : Fin dt) : PathDomainTyping (withGlobalMatrix B old) old full x y :=
  ⟨withGlobalMatrix_self _ _ _ _, withGlobalMatrix_self _ _ _ _,
    withGlobalMatrix_self _ _ _ _, withGlobalMatrix_self _ _ _ _⟩

end PlanarHom.PrescribedDomains

namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PrescribedDomains
variable {q bt ut dt : ℕ} (L : RealLanguage q bt ut)

/-- The canonical global-C prescribed-domain version of the PSD conclusion.
The source availability already has this fixed C policy; none is added by the reduction. -/
def lemma33_global_domain_range (hunit : ∀ i, L.weights i=1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ) (hC : (L.matrices old).PosSemidef)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (L.domainProblem D (withGlobalMatrix B old) T) base) :
    PromisePolyTimeTuringReduction
      (L.domainRangeTargetProblem D (withGlobalMatrix B old) T old hC) base :=
  L.lemma33_domain_range_of_pathTyping hunit D (withGlobalMatrix B old) T old full hfull
    (fun x y _ => withGlobalMatrix_pathTyping B old full x y) hC base available

/-- Every fixed rational power under the same explicit global-C policy. -/
def lemma33_global_domain_rationalPower (hunit : ∀ i, L.weights i=1)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (full : Fin dt)
    (hfull : D full=Set.univ) (hC : (L.matrices old).PosDef) (r : ℚ)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (L.domainProblem D (withGlobalMatrix B old) T) base) :
    PromisePolyTimeTuringReduction
      (L.domainRationalPowerTargetProblem D (withGlobalMatrix B old) T old hC r) base :=
  L.lemma33_domain_rationalPower_of_pathTyping hunit D (withGlobalMatrix B old) T old full hfull
    (fun x y _ => withGlobalMatrix_pathTyping B old full x y) hC r base available

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
