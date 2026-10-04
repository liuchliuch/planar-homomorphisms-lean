import PlanarHom.PrescribedDomains

/-! Fixed endpoint-domain typing and its exact preservation under occurrence replication. -/

namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode
variable {binaryTypes unaryTypes domainTypes : ℕ}

/-- The original fixed tables of permitted endpoint domains. They may distinguish
ordered endpoints and therefore include rectangular-constraint models. -/
def Typed (binaryDomains : Fin binaryTypes → Fin domainTypes → Fin domainTypes → Prop)
    (unaryDomains : Fin unaryTypes → Fin domainTypes → Prop)
    (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes) (δ : Fin g.vertices → Fin domainTypes) : Prop :=
  (∀ e (he : e ∈ g.edges), binaryDomains ⟨e.2.2, (hg.1 e he).2.2⟩
    (δ ⟨e.1, (hg.1 e he).1⟩) (δ ⟨e.2.1, (hg.1 e he).2.1⟩)) ∧
  (∀ u (hu : u ∈ g.unaries), unaryDomains ⟨u.2, (hg.2 u hu).2⟩ (δ ⟨u.1, (hg.2 u hu).1⟩))

theorem Typed.parallelLabel
    {B : Fin binaryTypes → Fin domainTypes → Fin domainTypes → Prop}
    {U : Fin unaryTypes → Fin domainTypes → Prop}
    {g : MixedCode} {hg : g.Valid binaryTypes unaryTypes} {δ : Fin g.vertices → Fin domainTypes}
    (h : Typed B U g hg δ) (selected s : ℕ) :
    Typed B U (g.parallelLabel selected s)
      (parallelLabel_valid selected s binaryTypes unaryTypes g hg) δ := by
  exact ⟨fun e he => h.1 e (repeatSelected_mem _ _ _ he), h.2⟩

theorem Typed.parallelUnaryLabel
    {B : Fin binaryTypes → Fin domainTypes → Fin domainTypes → Prop}
    {U : Fin unaryTypes → Fin domainTypes → Prop}
    {g : MixedCode} {hg : g.Valid binaryTypes unaryTypes} {δ : Fin g.vertices → Fin domainTypes}
    (h : Typed B U g hg δ) (selected s : ℕ) :
    Typed B U (g.parallelUnaryLabel selected s) (parallelUnaryLabel_valid selected s g hg) δ := by
  exact ⟨h.1, fun u hu => h.2 u (repeatSelected_mem _ _ _ hu)⟩

/-- A raw domain-aware input consists exactly of the original typed planar
instance with its reserved intrinsic domain occurrences, not arbitrary pinning. -/
def EncodedInput
    (B : Fin binaryTypes → Fin domainTypes → Fin domainTypes → Prop)
    (U : Fin unaryTypes → Fin domainTypes → Prop) (bits : Bits) : Prop :=
  ∃ (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes) (δ : Fin g.vertices → Fin domainTypes),
    Typed B U g hg δ ∧ g.underlying.PlanarValid ∧
      MixedCode.encoding.decode bits = some (withDomains (unaryTypes := unaryTypes) g δ)

/-- The intrinsic domain representation is an ordinary mixed planar input with
an explicitly stronger domain-preserving promise. -/
theorem EncodedInput.planarInput
    {B : Fin binaryTypes → Fin domainTypes → Fin domainTypes → Prop}
    {U : Fin unaryTypes → Fin domainTypes → Prop} {bits : Bits}
    (h : EncodedInput B U bits) : MixedCode.PlanarInput binaryTypes (unaryTypes + domainTypes) bits := by
  obtain ⟨g, hg, δ, _, hplanar, hdecode⟩ := h
  exact ⟨withDomains g δ, hdecode, withDomains_valid g hg δ, hplanar⟩

/-- No extra domain types arise when the original typed instance is encoded. -/
theorem encodedInput_encode_withDomains
    {B : Fin binaryTypes → Fin domainTypes → Fin domainTypes → Prop}
    {U : Fin unaryTypes → Fin domainTypes → Prop}
    {g : MixedCode} {hg : g.Valid binaryTypes unaryTypes} {δ : Fin g.vertices → Fin domainTypes}
    (htyped : Typed B U g hg δ) (hplanar : g.underlying.PlanarValid) :
    EncodedInput B U (MixedCode.encoding.encode (withDomains (unaryTypes := unaryTypes) g δ)) :=
  ⟨g, hg, δ, htyped, hplanar, MixedCode.encoding.decode_encode _⟩

end PlanarHom.PrescribedDomains
