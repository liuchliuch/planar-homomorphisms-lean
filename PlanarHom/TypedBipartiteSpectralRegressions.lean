import PlanarHom.TypedBipartiteSpectralCompletion

/-! Boundary checks for intrinsic private-X spectral queries. -/
noncomputable section
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.PrescribedDomains PlanarHom.TypedBipartiteSpectral
open PlanarHom.FiniteLanguageAliases PlanarHom.SpectralFieldPresentation

namespace PlanarHom.TypedBipartiteSpectral.Regressions

abbrev Colors := Fin 2 ⊕ Fin 3

def sides : Fin 2 → Set Colors :=
  fun d=>if d=0 then Set.range Sum.inl else Set.range Sum.inr

def permissions : Fin 2 → Fin 2 → Fin 2 → Prop :=
  fun l x y=>if l=0 then x=0 ∧ y=0 else (x=0 ∧ y=1) ∨ (x=1 ∧ y=0)

def unaryPermissions : Fin 1 → Fin 2 → Prop := fun _ _=>True

theorem privateX_ne_ambient : sides 0≠Set.univ := by
  intro h
  have hy : (Sum.inr (0:Fin 3) : Colors)∈sides 0 := by rw [h]; trivial
  simpa [sides] using hy

theorem actual_path_typing : ∀ x y,permissions 0 x y →
    PathDomainTyping permissions 0 0 x y := by
  intro x y h
  obtain ⟨rfl,rfl⟩ := (by simpa [permissions] using h : x=0 ∧ y=0)
  simp [PathDomainTyping,permissions]

theorem actual_endpoint_typing : ∀ x y,permissions 0 x y →
    sides x⊆Set.range Sum.inl ∧ sides y⊆Set.range Sum.inl := by
  intro x y h
  obtain ⟨rfl,rfl⟩ := (by simpa [permissions] using h : x=0 ∧ y=0)
  simp [sides]

/-- The target has a selected loop and a retained cross companion. Its ordinary
unary uses label zero, so the reserved X/Y labels start at one. -/
def loopWithCompanion : MixedCode :=
  ⟨2,[(0,0,2),(0,1,1)],[(1,0),(0,1),(1,2)]⟩

example : (loopWithCompanion.stretchLabelDomainsLength 2 0 1 3).vertices=4 := by decide

example : (loopWithCompanion.stretchLabelDomainsLength 2 0 1 3).edges=
    [(0,2,0),(2,3,0),(3,0,0),(0,1,1)] := by decide

example : (loopWithCompanion.stretchLabelDomainsLength 2 0 1 3).unaries=
    [(1,0),(0,1),(1,2),(2,1),(3,1)] := by decide

/-- Sample length one creates no private vertices or extra metadata. -/
example : (loopWithCompanion.stretchLabelDomainsLength 2 0 1 1).unaries=
    loopWithCompanion.unaries := by decide

example (A : Matrix (Fin 2) (Fin 2) ℚ) (E : Matrix (Fin 3) (Fin 3) ℚ) (x : Fin 2) :
    (∑ τ : Fin 2 → Colors,PathPower.weight 2 (Matrix.fromBlocks A 0 0 E) (.inl x) (.inl x) τ)=
      ∑ τ : Fin 2 → Fin 2,PathPower.weight 2 A x x τ :=
  completed_path_sum_eq_private_X A E 2 x x

/-- The supported zero-exponent identity does not become the ambient identity. -/
example : zeroExtend (Y:=Fin 3) (1 : Matrix (Fin 2) (Fin 2) ℚ)≠1 := by
  intro h
  have he := congrArg (fun A : Matrix Colors Colors ℚ=>A (.inr 0) (.inr 0)) h
  norm_num at he

/-- Unused completion entries are arbitrary; the cross companion remains the
literal original matrix, even if nonsymmetric. -/
example {K : Type} [Field K] [Algebra ℚ K]
    (M : Fin 2 → Matrix Colors Colors K) (A : Matrix (Fin 2) (Fin 2) K) :
    supportedContext M 0 A 1=M 1 := supportedContext_other M 0 1 A (by decide)

variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀] {dimension : ℕ}

/-- A typed language with |X|=2 and |Y|=3 receives an actual raw oracle reduction
at rational exponent zero, with ordinary unary offset one. -/
def zeroPowerReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin 2 → Matrix Colors Colors K₀) (U : Fin 1 → Colors → K₀)
    (A : Matrix (Fin 2) (Fin 2) K₀) (hblock : ∀ i j,M 0 (.inl i) (.inl j)=A i j)
    (hpd : (realMatrix A).PosDef) :=
  typedRationalPowerAppendReduction b₀ M U sides permissions unaryPermissions 0 0
    (by simp [sides]) actual_path_typing actual_endpoint_typing A hblock hpd 0

/-- Negative exponents use the same genuine compiler and unchanged source
basis; no inverse entry or oracle is added to the source alphabet. -/
def inverseReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin 2 → Matrix Colors Colors K₀) (U : Fin 1 → Colors → K₀)
    (A : Matrix (Fin 2) (Fin 2) K₀) (hblock : ∀ i j,M 0 (.inl i) (.inl j)=A i j)
    (hpd : (realMatrix A).PosDef) :=
  typedRationalPowerAppendReduction b₀ M U sides permissions unaryPermissions 0 0
    (by simp [sides]) actual_path_typing actual_endpoint_typing A hblock hpd (-1)

/-- The literal CFC matrix at rational exponent zero is the X identity. -/
example (A : Matrix (Fin 2) (Fin 2) K₀) (hpd : (realMatrix A).PosDef) (i j : Fin 2) :
    ((N A (fun x=>x^((0:ℚ):ℝ))) i j:ℝ)=(1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  change cfc (fun x : ℝ=>x^((0:ℚ):ℝ)) (realMatrix A) i j=_
  simpa only [Rat.cast_zero,Real.rpow_zero] using
    congrArg (fun P : Matrix (Fin 2) (Fin 2) ℝ=>P i j) (cfc_const_one ℝ (realMatrix A) hpd.1)

/-- Machine output is certified on every decodable word of the actual ordinary
parameter/graph codec, including noncanonical representations. -/
example (raw : Bits) (length : ℕ) (g : MixedCode)
    (hd : (BitEncoding.unaryNat.prod encoding).decode raw=some (length,g)) :
    Turing.TM2OutputsInTime (stretchLabelDomainsLengthRawComputer 2 0 1).tm
      (raw.map (stretchLabelDomainsLengthRawComputer 2 0 1).inputAlphabet.symm)
      (some ((encoding.encode (g.stretchLabelDomainsLength 2 0 1 length)).map
        (stretchLabelDomainsLengthRawComputer 2 0 1).outputAlphabet.symm))
      ((stretchLabelDomainsLengthRawComputer 2 0 1).time.eval raw.length) :=
  stretchLabelDomainsLength_raw_outputs 2 0 1 raw length g hd

end PlanarHom.TypedBipartiteSpectral.Regressions
