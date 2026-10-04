import PlanarHom.TypedGadgetAppendTyping
import PlanarHom.TypedGadgetAppendColoredTemplates

/-! Actual edge-coloured gadgets satisfy the generic typed APPEND contract
whenever every source edge obeys its ordered endpoint table. -/
noncomputable section
open Classical
namespace PlanarHom.TypedGadgetAppend
open FixedGadgetNetwork
variable {p e bt ut dt : ℕ}

/-- Total bookkeeping tags, with the two actual terminals followed by exactly
the private tags. The value outside the allocated range is irrelevant. -/
def coloredNaturalTag (x y : Fin dt) (privateTag : Fin p → Fin dt) : ℕ → Fin dt :=
  fun v => if v=0 then x else if v=1 then y else
    if h : v-2<p then privateTag ⟨v-2,h⟩ else x

@[simp] theorem coloredNaturalTag_zero (x y : Fin dt) (privateTag : Fin p → Fin dt) :
    coloredNaturalTag x y privateTag 0=x := by simp [coloredNaturalTag]

@[simp] theorem coloredNaturalTag_one (x y : Fin dt) (privateTag : Fin p → Fin dt) :
    coloredNaturalTag x y privateTag 1=y := by simp [coloredNaturalTag]

@[simp] theorem coloredNaturalTag_private (x y : Fin dt) (privateTag : Fin p → Fin dt)
    (j : Fin p) : coloredNaturalTag x y privateTag (2+j.val)=privateTag j := by
  have h1 : 2+j.val≠1 := by omega
  simp [coloredNaturalTag,h1,j.isLt]

theorem coloredNaturalTag_private_nat (x y : Fin dt) (privateTag : Fin p → Fin dt)
    (j : ℕ) (hj : j<p) :
    coloredNaturalTag x y privateTag (2+j)=privateTag ⟨j,hj⟩ :=
  coloredNaturalTag_private x y privateTag ⟨j,hj⟩

/-- Reindexing the source vertices preserves every endpoint and private tag. -/
theorem coloredNaturalTag_serialized (x y : Fin dt) (privateTag : Fin p → Fin dt)
    (v : Bool ⊕ Fin p) :
    coloredNaturalTag x y privateTag
      (finSumFinEquiv ((Equiv.sumCongr finTwoEquiv.symm (Equiv.refl _)) v)).val =
      TwoTerminal.extend x y privateTag v := by
  rcases v with (v|v)
  · cases v
    · exact coloredNaturalTag_zero x y privateTag
    · exact coloredNaturalTag_one x y privateTag
  · exact coloredNaturalTag_private x y privateTag v

/-- The literal private-unary list is the exact range-indexed intrinsic tail
required by `TemplateTyping`. -/
theorem ofTypedColoredTwoTerminal_domains (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (privateTag : Fin p → Fin dt) (ut : ℕ) (x y : Fin dt) :
    (ofTypedColoredTwoTerminal G label privateTag ut).unaries =
      (List.range p).map (fun j => (2+j,ut+(coloredNaturalTag x y privateTag (2+j)).val)) := by
  apply List.ext_getElem
  · simp [ofTypedColoredTwoTerminal_unaries]
  · intro i hi hj
    have hi' : i<p := by simpa using hj
    simp only [ofTypedColoredTwoTerminal_unaries,List.getElem_ofFn,
      List.getElem_map,List.getElem_range]
    rw [coloredNaturalTag_private_nat x y privateTag i hi']

/-- General source typing: arbitrary source labels and ordered endpoint
relations, including same-side edges and ordinary companion labels. -/
theorem ofTypedColoredTwoTerminal_typing
    (B : Fin bt → Fin dt → Fin dt → Prop)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e → Fin bt)
    (privateTag : Fin p → Fin dt) (ut : ℕ) (x y : Fin dt)
    (hedges : ∀ i, B (label i)
      (TwoTerminal.extend x y privateTag (G.src i))
      (TwoTerminal.extend x y privateTag (G.dst i))) :
    TemplateTyping (ut:=ut) B (ofTypedColoredTwoTerminal G label privateTag ut)
      (coloredNaturalTag x y privateTag) := by
  refine ⟨ofTypedColoredTwoTerminal_valid G label privateTag ut,
    ofTypedColoredTwoTerminal_domains G label privateTag ut x y,?_⟩
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  change B (label i)
    (coloredNaturalTag x y privateTag (finSumFinEquiv ((twoTerminalFinGraph G).src i)).val)
    (coloredNaturalTag x y privateTag (finSumFinEquiv ((twoTerminalFinGraph G).dst i)).val)
  rw [show (twoTerminalFinGraph G).src i =
    (Equiv.sumCongr finTwoEquiv.symm (Equiv.refl _)) (G.src i) from rfl,
    show (twoTerminalFinGraph G).dst i =
    (Equiv.sumCongr finTwoEquiv.symm (Equiv.refl _)) (G.dst i) from rfl,
    coloredNaturalTag_serialized,coloredNaturalTag_serialized]
  exact hedges i

/-- The existential endpoint contract consumed by the generic APPEND family
compiler, for any target endpoint relation `A`. -/
theorem ofTypedColoredTwoTerminal_typing_exists
    (B : Fin bt → Fin dt → Fin dt → Prop) (A : Fin dt → Fin dt → Prop)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e → Fin bt)
    (privateTag : Fin p → Fin dt) (ut : ℕ)
    (hedges : ∀ x y, A x y → ∀ i, B (label i)
      (TwoTerminal.extend x y privateTag (G.src i))
      (TwoTerminal.extend x y privateTag (G.dst i))) :
    ∀ x y, A x y → ∃ tag,
      TemplateTyping (ut:=ut) B (ofTypedColoredTwoTerminal G label privateTag ut) tag ∧
        tag 0=x ∧ tag 1=y := by
  intro x y hxy
  exact ⟨coloredNaturalTag x y privateTag,
    ofTypedColoredTwoTerminal_typing B G label privateTag ut x y (hedges x y hxy),
    coloredNaturalTag_zero x y privateTag,coloredNaturalTag_one x y privateTag⟩

end PlanarHom.TypedGadgetAppend
