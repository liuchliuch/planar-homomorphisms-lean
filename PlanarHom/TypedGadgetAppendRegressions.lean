import PlanarHom.TypedGadgetAppendTransport
import PlanarHom.TypedGadgetAppendMachines
import PlanarHom.TypedGadgetAppendRestrictedSemantics

/-! Boundary regressions: no private indicators on old identity templates;
source fields and arbitrary successfully decoded input words stay unchanged. -/
noncomputable section
namespace PlanarHom.TypedGadgetAppend.Regressions
open Complexity Complexity.MixedCode PrescribedDomains FixedGadgetNetwork EdgeSubstitution

example (l : Fin 3) : (identityTemplate l).privateCount=0 := rfl
example (l : Fin 3) : (identityTemplate l).unaries=[] := rfl

/-- An isolated host vertex stays present, with its own original domain. -/
example : substitute [] (⟨1,[],[(0,2)]⟩ : MixedCode)=⟨1,[],[(0,2)]⟩ := rfl

/-- An empty host does not receive fabricated vertices or domain occurrences. -/
example (ts : List Template) : substitute ts (⟨0,[],[]⟩ : MixedCode)=⟨0,[],[]⟩ := rfl

/-- Every decodable representation is accepted by the same actual query TM2. -/
noncomputable def rawQuery (ts : List Template) (raw : Bits) (g : MixedCode)
    (hd : MixedCode.encoding.decode raw=some g) :
    Turing.TM2OutputsInTime (queryRawComputer ts).tm
      (raw.map (queryRawComputer ts).inputAlphabet.symm)
      (some ((MixedCode.encoding.encode (substitute ts g)).map
        (queryRawComputer ts).outputAlphabet.symm))
      ((queryRawComputer ts).time.eval raw.length) := query_raw_outputs ts raw g hd

/-- The raw scalar signature of an edge-free two-terminal gadget is one,
even at disallowed domain pairs: APPEND-on-domains must allow completion. -/
def emptyBinary : Template := ⟨2,0,[],[]⟩

example {C : Type} [Fintype C] (M : Fin 0 → Matrix C C ℚ)
    (U : Fin 2 → C → ℚ) (i j : C) : templateInteraction emptyBinary M U i j=1 := by
  simp [templateInteraction,templateSignature,factor,emptyBinary,Template.code]

end PlanarHom.TypedGadgetAppend.Regressions
