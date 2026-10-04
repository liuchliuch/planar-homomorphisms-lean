import PlanarHom.TypedGadgetAppendReduction
import PlanarHom.ColoredEdgeGadgetJointReduction
import PlanarHom.PrescribedDomainAliasReductions

/-! Generic retained-context APPEND for an actual typed planar edge gadget.
Every original binary matrix, unary function, endpoint policy, and prescribed
vertex domain remains in the source language. New signatures are available
jointly with all original labels through literal one-edge identity templates. -/
noncomputable section
open Classical
namespace PlanarHom.TypedGadgetAppend
open Complexity Complexity.MixedCode PrescribedDomains FixedGadgetNetwork EdgeSubstitution
open FiniteLanguageAliases
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension bt ut dt a : ℕ}

/-- Indexed finite-family version, retaining the original finite label type. -/
def indexedFamilyReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (ts : Fin a → Template) (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (BT : Fin a → Fin dt → Fin dt → Prop)
    (fallback : Fin dt) (ht : ∀l,(ts l).code.Valid bt (ut+dt))
    (hb : ∀l,(ts l).boundary=2)
    (hp : ∀l,TwoTerminal.PlanarEdgeGadget ((ts l).edgeGadget (hb l) (ht l)))
    (hfamily : ∀l x y,BT l x y → ∃tag,TemplateTyping (ut:=ut) B (ts l) tag ∧ tag 0=x ∧ tag 1=y) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun l=>templateInteraction (ts l) M (extendedUnaries U D))
        U (fun _=>1) D BT T)
      (domainEvaluationProblem basis M U (fun _=>1) D B T) := by
  let xs := List.ofFn ts
  let cast : Fin a ≃ Fin xs.length := (finCongr (by simp [xs])).symm
  let BX := BT ∘ cast.symm
  have hget (l : Fin xs.length) : xs.get l=ts (cast.symm l) := by
    simp only [xs,List.get_eq_getElem,List.getElem_ofFn]
    congr 1
  have hx : ∀t∈xs,t.code.Valid bt (ut+dt) := by
    intro t hm
    obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hm
    exact ht l
  have hxb : ∀t∈xs,t.boundary=2 := by
    intro t hm
    obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hm
    exact hb l
  have hxp : ∀t (h:t∈xs),TwoTerminal.PlanarEdgeGadget (t.edgeGadget (hxb t h) (hx t h)) := by
    intro t hm
    obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hm
    exact hp l
  have hxf : FamilyTyping (ut:=ut) xs B BX := by
    intro l x y h
    rw [hget]
    exact hfamily (cast.symm l) x y h
  have hv : interactions xs M (extendedUnaries U D) ∘ cast =
      fun l=>templateInteraction (ts l) M (extendedUnaries U D) := by
    funext l i j
    change templateInteraction (xs.get (cast l)) M (extendedUnaries U D) i j=_
    rw [hget,Equiv.symm_apply_apply]
  have r := domainBinaryRelabelReduction basis cast
    (interactions xs M (extendedUnaries U D)) U (fun _=>1) D BT BX T (by
      intro l x y h
      simpa only [BX,Function.comp_apply,Equiv.symm_apply_apply] using h)
  rw [hv] at r
  exact r.trans (familyReduction basis xs M U D B T BX fallback hx hxb hxp hxf)

/-- The old occurrence is literally one original labelled edge, with zero
private vertices and no added unary/domain occurrence. -/
def identityTemplate (l : Fin bt) : Template :=
  ofColoredTwoTerminal singleFinEdge (fun _=>l)

theorem identityTemplate_typed (B : Fin bt → Fin dt → Fin dt → Prop)
    (l : Fin bt) (x y : Fin dt) (h : B l x y) :
    ∃tag,TemplateTyping (ut:=ut) B (identityTemplate l) tag ∧ tag 0=x ∧ tag 1=y := by
  let tag : ℕ → Fin dt := fun v=>if v=0 then x else y
  refine ⟨tag,⟨ofColoredTwoTerminal_valid _ _,rfl,?_⟩,by simp [tag],by simp [tag]⟩
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  simpa only [identityTemplate,ofColoredTwoTerminal,ofColoredFinGraph,twoTerminalFinGraph,
    singleFinEdge,MultiGraph.reindex,Equiv.refl_symm,Equiv.refl_apply,tag] using h

@[simp] theorem identityTemplate_signature (l : Fin bt) (M : Fin bt → Matrix C C K)
    (U : Fin ut → C → K) : templateInteraction (identityTemplate l) M U=M l := by
  rw [identityTemplate,templateInteraction_colored,singleFinEdge_signature]

/-- The desired APPEND contract, using the original exact typed source oracle.
The appended endpoint policy can be XX, YY, or any fixed ordered policy for
which the supplied template is actually typed. -/
def appendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (D : Fin dt → Set C) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (A : Fin dt → Fin dt → Prop)
    (fallback : Fin dt) (t : Template) (ht : t.code.Valid bt (ut+dt)) (hb : t.boundary=2)
    (hp : TwoTerminal.PlanarEdgeGadget (t.edgeGadget hb ht))
    (hnew : ∀x y,A x y → ∃tag,TemplateTyping (ut:=ut) B t tag ∧ tag 0=x ∧ tag 1=y) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M (templateInteraction t M (extendedUnaries U D)))
        U (fun _=>1) D (appendOne B A) T)
      (domainEvaluationProblem basis M U (fun _=>1) D B T) := by
  let ts : Fin (bt+1) → Template := appendOne identityTemplate t
  have hvalid : ∀l,(ts l).code.Valid bt (ut+dt) := by
    intro l
    refine Fin.addCases (fun l=>?_) (fun l=>?_) l
    · simpa only [ts,appendOne,Fin.addCases_left] using
        (ofColoredTwoTerminal_valid (ut:=ut+dt) singleFinEdge (fun _=>l))
    · simpa only [ts,appendOne,Fin.addCases_right] using ht
  have hboundary : ∀l,(ts l).boundary=2 := by
    intro l
    refine Fin.addCases (fun l=>?_) (fun l=>?_) l
    · simp only [ts,appendOne,Fin.addCases_left,identityTemplate,ofColoredTwoTerminal_boundary]
    · simpa only [ts,appendOne,Fin.addCases_right] using hb
  have hplanar : ∀l,TwoTerminal.PlanarEdgeGadget ((ts l).edgeGadget (hboundary l) (hvalid l)) := by
    have transfer (s z : Template) (hs : s.code.Valid bt (ut+dt)) (hz : z.code.Valid bt (ut+dt))
        (bs : s.boundary=2) (bz : z.boundary=2) (he : s=z)
        (h : TwoTerminal.PlanarEdgeGadget (z.edgeGadget bz hz)) :
        TwoTerminal.PlanarEdgeGadget (s.edgeGadget bs hs) := by
      subst z
      exact h
    intro l
    refine Fin.addCases (fun l=>?_) (fun l=>?_) l
    · exact transfer _ _ _ (ofColoredTwoTerminal_valid singleFinEdge (fun _=>l)) _ rfl
        (by simp only [ts,appendOne,Fin.addCases_left,identityTemplate])
        (ofColoredTwoTerminal_planar singleFinEdge (fun _=>l) singleFinEdge_planar)
    · exact transfer _ _ _ ht _ hb (by simp only [ts,appendOne,Fin.addCases_right]) hp
  have hfamily : ∀l x y,appendOne B A l x y →
      ∃tag,TemplateTyping (ut:=ut) B (ts l) tag ∧ tag 0=x ∧ tag 1=y := by
    intro l
    refine Fin.addCases (fun l x y h=>?_) (fun l x y h=>?_) l
    · simp only [appendOne,Fin.addCases_left] at h
      simpa only [ts,appendOne,Fin.addCases_left] using (identityTemplate_typed (ut:=ut) B l x y h)
    · simp only [appendOne,Fin.addCases_right] at h
      simpa only [ts,appendOne,Fin.addCases_right] using hnew x y h
  have he : (fun l=>templateInteraction (ts l) M (extendedUnaries U D))=
      appendOne M (templateInteraction t M (extendedUnaries U D)) := by
    funext l
    refine Fin.addCases (fun l=>?_) (fun l=>?_) l
    · simpa only [ts,appendOne,Fin.addCases_left] using
        (identityTemplate_signature l M (extendedUnaries U D))
    · simp only [ts,appendOne,Fin.addCases_right]
  have r := indexedFamilyReduction basis ts M U D B T (appendOne B A) fallback
    hvalid hboundary hplanar hfamily
  rw [he] at r
  exact r

end PlanarHom.TypedGadgetAppend
