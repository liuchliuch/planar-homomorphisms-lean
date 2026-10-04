import PlanarHom.FixedExtensionSolutionCorrectness

/-! Prescribed fixed-extension output for exact variable-order systems. Raw
lexical input normalization is genuine, and the answer relation accepts every
valid representative of the exact solution. -/
noncomputable section
namespace PlanarHom.FixedRealExtension
open DensePolynomial Complexity RepresentedBit
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

def systemNormalizer (n e:ℕ) : BitEncoding.Normalizer (systemEncoding n e) :=
  BitEncoding.prodNormalizer (BitEncoding.listNormalizer (BitEncoding.listNormalizer (normalizer n e)))
    (BitEncoding.listNormalizer (normalizer n e))

def SolutionCode (basis:Module.Basis (Fin e) (RationalFunction n) K) (p:System n e) (xs:List (Code n e)) : Prop :=
  xs.length=p.1.length ∧ (∀x∈xs,Valid n x) ∧
    (systemMatrix basis p).mulVec (fun i=>value basis (xs[i.val]?.getD (zeroCode n e)))=systemVector basis p

theorem solve_solutionCode (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (T:MultiplicationTable n e) (hT:T.Realizes basis) (p:System n e)
    (hv:SystemValid n e p) (hn:(systemMatrix basis p).det≠0) :
    SolutionCode basis p (solve T p) := by
  refine ⟨solve_length T p,?_,solve_correct basis T hT p hv hn⟩
  intro x hx
  obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hx
  have hik:i<p.1.length:=by simpa only [solve_length] using hi
  have hh:=solve_output_valid basis T hT p hv hn ⟨i,hik⟩
  simpa only [List.getElem?_eq_getElem hi,Option.getD_some,he] using hh

def linearSystemProblem (basis:Module.Basis (Fin e) (RationalFunction n) K) : Problem :=
  typedProblem (systemEncoding n e) (encoding n e).list
    (fun p=>SystemValid n e p ∧ (systemMatrix basis p).det≠0) (SolutionCode basis)

theorem linearSystem_inFP (basis:Module.Basis (Fin e) (RationalFunction n) K) :
    (linearSystemProblem basis).InFP :=
  typedProblem_inFP (systemEncoding n e) (encoding n e).list (systemNormalizer n e) _ _
    (solve (multiplicationTable basis)) (fp_solve _) (fun p hp=>
      solve_solutionCode basis (multiplicationTable basis) (multiplicationTable_realizes basis) p hp.1 hp.2)

theorem solve_nil (T:MultiplicationTable n e) (b:List (Code n e)) : solve T ([],b)=[] := rfl

end PlanarHom.FixedRealExtension
