import PlanarHom.PrescribedDomainStretch
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.PrescribedDomains

-- A selected loop remains an ordinary loop at length one. No fresh metadata is emitted.
example : (MixedCode.mk 1 [(0,0,1)] [(0,0),(0,1)]).stretchLabelDomainsLength 1 0 2 1 =
    MixedCode.mk 1 [(0,0,0)] [(0,0),(0,1)] := by decide

-- A loop at length three uses distinct private vertices and exactly one fresh
-- intrinsic full-domain occurrence at each, after the original metadata prefix.
example : (MixedCode.mk 1 [(0,0,1)] [(0,0),(0,1)]).stretchLabelDomainsLength 1 0 2 3 =
    MixedCode.mk 3 [(0,1,0),(1,2,0),(2,0,0)] [(0,0),(0,1),(1,2),(2,2)] := by decide

-- Repeated selected occurrences retain multiplicity and do not share private
-- vertices. A companion loop and repeated original unary records remain intact.
example : (MixedCode.mk 1 [(0,0,1),(0,0,0),(0,0,1)] [(0,0),(0,0),(0,1)]).stretchLabelDomainsLength 1 0 2 2 =
    MixedCode.mk 3 [(0,1,0),(1,0,0),(0,2,0),(2,0,0),(0,0,0)]
      [(0,0),(0,0),(0,1),(1,2),(2,2)] := by decide

-- A source table can reject an unrelated third domain: path closure is explicit,
-- without imposing universal closure on all entries of an arbitrary table.
example (x y : Fin 3) (h : x=0 ∧ y=0) :
    PathDomainTyping (fun (_ : Fin 1) a b => a.val<2 ∧ b.val<2)
      0 1 x y := by
  rcases h with ⟨rfl,rfl⟩
  norm_num [PathDomainTyping]
