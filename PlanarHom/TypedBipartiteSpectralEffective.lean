import PlanarHom.TypedBipartiteSpectralFiniteBlocks
import PlanarHom.TypedBipartiteSpectralUniform
import PlanarHom.RestrictedFixedSpectralTransfer

/-! Effective source3.10 spectral closure in a genuine typed mixed context.
All zero bounds and product identities concern the X block alone. Unused
ambient sampling entries duplicate real X entries, so no new product relation
is introduced. The typed oracle only queries X×X selected paths. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.TypedBipartiteSpectral
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases
open EffectiveProductTransfer SpectralFieldPresentation ExponentProductTables
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {q y bt ut dt dimension : ℕ}

/-- Effective fixed-target spectral transfer, with an actual uniform selected
path simulator and the original companion language/source presentation. -/
def effectiveAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin (q+y)) (Fin (q+y)) K)
    (U : Fin ut → Fin (q+y) → K)
    (D : Fin dt → Set (Fin (q+y))) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hX : D privateX=Set.range (leftEmbedding (q:=q) (y:=y)))
    (hpath : ∀ x y,B old x y → PathDomainTyping B old privateX x y)
    (htype : ∀ x z,B old x z → D x⊆Set.range (leftEmbedding (q:=q) (y:=y)) ∧
      D z⊆Set.range (leftEmbedding (q:=q) (y:=y)))
    (A N : Matrix (Fin q) (Fin q) K) (hA : M old=zeroExtendFin A)
    (x₀ : Fin q) (hpd : (realMatrix A).PosDef) (hNs : ∀ i j,N i j=N j i)
    (n₀ : ℕ) (hn₀ : 1≤n₀)
    (hp : ∀ n,n₀≤n → ∀ i j,0<matrixPowerRealFamily A n i j)
    (hi : ProductIdentities (matrixPowerRealFamily A) (fun i j=>(N i j:ℝ))) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M (zeroExtendFin N)) U (fun _=>1)
        D (appendOne B (B old)) T)
      (domainEvaluationProblem basis M U (fun _=>1) D B T) := by
  let ρ := retractLeft (y:=y) x₀
  let F := fun n=>repeatEntries ρ (A^n)
  let N' := repeatEntries ρ N
  let HT := EncodedGraph (appendOne B (B old)) T
  have hv : ∀ g,HT g → g.Valid (bt+1) (ut+dt) := fun _ h=>(h.planarValid _ T).1
  have hsup : ∀ c,c∉D privateX → ∀ d,M old c d=0 := by
    rw [hX,hA]
    exact zeroExtendFin_support A
  have hpow : ∀ n,1≤n → ∀ x y,B old x y → ∀ i∈D x,∀ j∈D y,F n i j=(M old^n) i j := by
    intro n hn x z hb i hi j hj
    obtain ⟨i,rfl⟩ := (htype x z hb).1 hi
    obtain ⟨j,rfl⟩ := (htype x z hb).2 hj
    rw [hA]
    exact repeatEntries_power_on_X A x₀ n (by omega) i j
  let simulation := supportedUniformReduction basis M U D B T old privateX hsup hpath F hpow
  let c := spectralCandidateCount q (Nat.card (spectrum ℝ (realMatrix A)))
  have hfp : FP BitEncoding.unaryNat ((numberFieldEncoding basis).vector ((q+y)*(q+y)))
      (fun n=>binaryAlphabet (F n)) := by
    have h := (SpectralPowerEvaluationMachines.fp_matrixPowers basis A hpd.1).comp
      (fp_repeatEntries basis ρ)
    exact h.congr (fun n=>(binaryAlphabet_repeatEntries ρ (A^n)).symm)
  have hnz : ∀ n,n₀≤n → ∀ i j,F n i j≠0 := by
    intro n hn i j hz
    have hpos := hp n hn (ρ i) (ρ j)
    rw [← matrixPowerFamily_coe A hpd.1] at hpos
    change (A^n) (ρ i) (ρ j)=0 at hz
    rw [hz] at hpos
    exact lt_irrefl 0 hpos
  have hs : ∀ m,∃ j<c.eval m,CompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet N') m := by
    intro m
    obtain ⟨j,hj,hc⟩ := spectral_samples A N hpd n₀ hNs hi m
    refine ⟨j,hj,?_⟩
    rw [binaryAlphabet_repeatEntries,binaryAlphabet_repeatEntries]
    exact compatibleAt_comp _ _ _ m hc
  let r := RestrictedFixedSpectralTransfer.reduction basis M (extendedUnaries U D) (fun _=>1)
    F N' HT hv (fun g hg s=>hg.parallelLabel _ T bt s) n₀ hn₀ c hfp hnz hs
    (domainEvaluationProblem basis M U (fun _=>1) D B T) simulation
  apply r.transport
    (domainEvaluationProblem basis (appendOne M (zeroExtendFin N)) U (fun _=>1)
      D (appendOne B (B old)) T)
    (domainEvaluationProblem basis M U (fun _=>1) D B T)
    (fun raw h=>(encodedInput_iff_graph _ T raw).mp h) (fun _ h=>h) ?_ (fun _ _=>rfl)
  intro raw hr
  apply domain_value_congr basis _ _ U (fun _=>1) D (appendOne B (B old)) T ?_ raw hr
  intro l
  refine Fin.addCases (fun l=>?_) (fun l=>?_) l
  · intro x z hb i hi j hj
    simp only [appendOne_old]
  · intro x z hb i hi j hj
    have he : Fin.natAdd bt l=Fin.last bt := by
      have : l=(0:Fin 1) := Subsingleton.elim _ _
      subst l
      exact Fin.ext (Nat.add_zero bt)
    simp only [he,appendOne_aux] at hb ⊢
    obtain ⟨i,rfl⟩ := (htype x z hb).1 hi
    obtain ⟨j,rfl⟩ := (htype x z hb).2 hj
    simp [N',repeatEntries,ρ]

end PlanarHom.TypedBipartiteSpectral
