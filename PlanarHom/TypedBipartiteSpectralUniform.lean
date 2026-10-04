import PlanarHom.TypedBipartiteSpectralTransport
import PlanarHom.TypedBipartiteSpectralUniformCompiler

/-! Actual uniform private-side power queries. Their target family may choose
any unused entries, provided its permitted endpoint values are the X powers. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteSpectral
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K] [DecidableEq K]
variable {dimension q bt ut dt : ℕ}

theorem encodedGraph_evaluate_congr
    (M N : Fin bt → Matrix C C K) (U : Fin ut → C → K) (w : C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop)
    (hMN : ∀ l x y,B l x y → ∀ i∈D x,∀ j∈D y,M l i j=N l i j)
    (g : MixedCode) (hg : EncodedGraph B T g) :
    g.evaluate (hg.planarValid B T).1 M (extendedUnaries U D) w=
      g.evaluate (hg.planarValid B T).1 N (extendedUnaries U D) w := by
  obtain ⟨original,ho,δ,ht,hp,hd⟩ := hg
  rw [encoding.decode_encode] at hd
  have he : g=withDomains (unaryTypes:=ut) original δ := Option.some.inj hd
  subst g
  rw [evaluate_withDomains original ho M U w D δ,evaluate_withDomains original ho N U w D δ]
  exact evaluateRestricted_congr M N U w D B T hMN original ho δ ht

/-- The target parameter n is physically present in the existing unary codec.
All submitted graphs keep every companion and receive private-X metadata. -/
def supportedUniformReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hsupport : ∀ c,c∉D privateX → ∀ d,M old c d=0)
    (hpath : ∀ x y,B old x y → PathDomainTyping B old privateX x y)
    (F : ℕ → Matrix (Fin q) (Fin q) K)
    (hF : ∀ n,1≤n → ∀ x y,B old x y → ∀ i∈D x,∀ j∈D y,F n i j=(M old^n) i j) :
    PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.sourceProblem basis M (extendedUnaries U D) (fun _=>1)
        F (EncodedGraph (appendOne B (B old)) T))
      (domainEvaluationProblem basis M U (fun _=>1) D B T) := by
  let HT := EncodedGraph (appendOne B (B old)) T
  let HS := EncodedGraph B T
  let transform := fun n (g : MixedCode)=>g.stretchLabelDomainsLength bt old.val (ut+privateX.val) n
  have validT : ∀ g,HT g → g.Valid (bt+1) (ut+dt) := fun _ h=>(h.planarValid _ T).1
  have validS : ∀ g,HS g → g.Valid bt (ut+dt) := fun _ h=>(h.planarValid _ T).1
  have hq : ∀ g,HT g → ∀ n,1≤n → HS (transform n g) :=
    fun g hg n _=>hg.stretchAppendedAuxiliary old privateX hpath (n-1)
  have he : ∀ g (hg : HT g) n (hn : 1≤n),
      (transform n g).evaluate (validS _ (hq g hg n hn)) M (extendedUnaries U D) (fun _=>1)=
        g.evaluate (validT g hg) (appendOne M (F n)) (extendedUnaries U D) (fun _=>1) := by
    intro g hg n hn
    have hs : ∀ c d,M old c d≠0 → extendedUnaries U D (Fin.natAdd ut privateX) c=1 := by
      intro c d hc
      have hx : c∈D privateX := by
        by_contra h
        exact hc (hsupport c h d)
      simp [extendedUnaries,indicator,hx]
    have hf := g.evaluate_stretchLabel_withFreshDomains_of_support (validT g hg)
      bt (n-1) old (g.appended_companion_bound (validT g hg))
      (Fin.natAdd ut privateX) M (extendedUnaries U D) (fun _=>1) hs
    have hp := g.evaluate_stretchLabelLength_appendOne (validT g hg) old n hn M (extendedUnaries U D)
    apply (hf.trans hp).trans
    apply encodedGraph_evaluate_congr _ _ U (fun _=>1) D (appendOne B (B old)) T ?_ g hg
    intro l
    refine Fin.addCases (fun l=>?_) (fun l=>?_) l
    · intro x y hl i hi j hj
      simp only [appendOne_old]
    · intro x y hl i hi j hj
      have he : Fin.natAdd bt l=Fin.last bt := by
        have : l=(0:Fin 1) := Subsingleton.elim _ _
        subst l
        exact Fin.ext (Nat.add_zero bt)
      simp only [he,appendOne_aux] at hl ⊢
      exact (hF n hn x y hl i hi j hj).symm
  let r := familyReductionOn basis M (extendedUnaries U D) F HT HS validT validS
    transform (fp_stretchLabelDomainsLength bt old.val (ut+privateX.val)) hq he
  exact r.transport _ _ (fun _ h=>h)
    (fun raw h=>(encodedInput_iff_graph B T raw).mpr h) (fun _ _=>rfl) (fun _ _=>rfl)

end PlanarHom.TypedBipartiteSpectral
