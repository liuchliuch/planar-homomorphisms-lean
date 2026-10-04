import PlanarHom.ConcreteRoutingCanvas
import PlanarHom.FiniteBlockAllocation

/-! Exact finite equivalence between numeric materialized variables and the
Boolean-variable vertices of the drawn macro-grid. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree ParsimoniousBlockTemplate

def CellShape.outputCount (s : CellShape) : ℕ := s.portCount-s.kind.template.inputs

theorem CellShape.inputs_le_ports (s : CellShape) : s.kind.template.inputs≤s.portCount := by cases s <;> decide

theorem CellShape.outputs_add_auxiliaries (s : CellShape) :
    s.outputCount+s.auxiliaryCount=s.kind.template.fresh := by
  cases s <;> decide

theorem CellShape.inputs_add_outputs (s : CellShape) :
    s.kind.template.inputs+s.outputCount=s.portCount := Nat.add_sub_of_le s.inputs_le_ports

def Cell.freshPort (c : Cell) (j : Fin c.shape.outputCount) : Fin c.shape.portCount :=
  ⟨c.shape.kind.template.inputs+j.val,by have h := c.shape.inputs_add_outputs; omega⟩

theorem Cell.freshPort_reference (c : Cell) (j : Fin c.shape.outputCount) :
    (c.portData (c.freshPort j)).1=c.base+j.val := by
  rw [←c.port_reference (c.freshPort j)]
  simp [Template.translate,CellShape.portVertex,Cell.freshPort,Cell.instruction]

theorem Cell.output_mem (c : Cell) (x : ℕ) (hx : x∈c.outputRefs) :
    ∃ j : Fin c.shape.outputCount,x=c.base+j.val := by
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> simp_all [Cell.outputRefs,CellShape.outputCount,CellShape.portCount,CellShape.kind,
    Kind.template,equality,crossover,fanout,termination,Fin.exists_fin_succ,or_comm]

def initialBoundary (f : NumericFormula) (i : Fin f.1) : Boundary f :=
  ⟨(0,i.val),Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩

theorem registry_initial_input (f : NumericFormula) (i : Fin f.1) :
    (i.val,0,i.val)∈canvasRegistry f := by
  apply registry_initial
  have h := boundaryEntries_get 0 0 (List.range f.1) i.val (by simpa using i.isLt)
  simpa [getRef] using h

theorem boundary_registry_exists (f : NumericFormula) (hf : NumericValid f) (b : Boundary f) :
    ∃ p∈canvasRegistry f,p.2=b.val := by
  rcases Finset.mem_union.mp b.property with hb | hb
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hb
    exact ⟨(i.val,0,i.val),registry_initial_input f i,hi⟩
  · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hi
    exact ⟨(canvasCell f i).portData k,canvasRegistry_port f hf _ (List.get_mem _ _) k,hk⟩

def boundaryName (f : NumericFormula) (hf : NumericValid f) (b : Boundary f) : ℕ :=
  (Classical.choose (boundary_registry_exists f hf b)).1

theorem boundaryName_of_entry (f : NumericFormula) (hf : NumericValid f) (b : Boundary f)
    (p : PortData) (hp : p∈canvasRegistry f) (hpos : p.2=b.val) : boundaryName f hf b=p.1 := by
  have he := Classical.choose_spec (boundary_registry_exists f hf b)
  have h := List.inj_on_of_nodup_map (canvasRegistry_positions_nodup f) he.1 hp (he.2.trans hpos.symm)
  exact congrArg Prod.fst h

theorem boundaryName_injective (f : NumericFormula) (hf : NumericValid f) : Function.Injective (boundaryName f hf) := by
  intro b d h
  have hb := Classical.choose_spec (boundary_registry_exists f hf b)
  have hd := Classical.choose_spec (boundary_registry_exists f hf d)
  have he := List.inj_on_of_nodup_map (canvasRegistry_refs_nodup f hf) hb.1 hd.1 h
  apply Subtype.ext
  exact hb.2.symm.trans ((congrArg Prod.snd he).trans hd.2)

@[simp] theorem boundaryName_initial (f : NumericFormula) (hf : NumericValid f) (i : Fin f.1) :
    boundaryName f hf (initialBoundary f i)=i.val :=
  boundaryName_of_entry f hf _ (i.val,0,i.val) (registry_initial_input f i) rfl

@[simp] theorem boundaryName_port (f : NumericFormula) (hf : NumericValid f) (i : CanvasIndex f)
    (k : PatchPort f i) : boundaryName f hf (boundaryPort f i k)=((canvasCell f i).portData k).1 :=
  boundaryName_of_entry f hf _ _ (canvasRegistry_port f hf _ (List.get_mem _ _) k) rfl

theorem boundaryName_source (f : NumericFormula) (hf : NumericValid f) (b : Boundary f) :
    boundaryName f hf b∈List.range f.1 ∨ boundaryName f hf b∈(canvas f).flatMap Cell.outputRefs := by
  have hp := (Classical.choose_spec (boundary_registry_exists f hf b)).1
  have h := registry_ref_source (formulaStages f.1 f.2) 0 f.1 (List.range f.1)
    (Classical.choose (boundary_registry_exists f hf b)) hp
  simpa only [stagesCells_formulaStages] using h

abbrev Allocated (f : NumericFormula) := Fin f.1 ⊕ (i : CanvasIndex f) × Fin (canvasCell f i).fresh
abbrev BooleanGrid (f : NumericFormula) := Boundary f ⊕ (i : CanvasIndex f) × Fin (canvasCell f i).shape.auxiliaryCount

def allocatedBool (f : NumericFormula) : Allocated f → BooleanGrid f
  | .inl i => .inl (initialBoundary f i)
  | .inr p =>
    if h : p.2.val<(canvasCell f p.1).shape.outputCount then
      .inl (boundaryPort f p.1 ((canvasCell f p.1).freshPort ⟨p.2.val,h⟩))
    else .inr ⟨p.1,⟨p.2.val-(canvasCell f p.1).shape.outputCount,by
      have hh := (canvasCell f p.1).shape.outputs_add_auxiliaries
      have hp := p.2.isLt
      change p.2.val<(canvasCell f p.1).shape.kind.template.fresh at hp
      omega⟩⟩

def booleanName (f : NumericFormula) (hf : NumericValid f) : BooleanGrid f → ℕ
  | .inl b => boundaryName f hf b
  | .inr p => (canvasCell f p.1).base+(canvasCell f p.1).shape.outputCount+p.2.val

@[simp] theorem canvasAllocation_old (f : NumericFormula) (hf : NumericValid f) (i : Fin f.1) :
    (canvasAllocation f hf (.inl i)).val=i.val := rfl
@[simp] theorem canvasAllocation_new (f : NumericFormula) (hf : NumericValid f)
    (i : CanvasIndex f) (j : Fin (canvasCell f i).fresh) :
    (canvasAllocation f hf (.inr ⟨i,j⟩)).val=(canvasCell f i).base+j.val := rfl

/-- Every placed Boolean vertex retains exactly its original numeric name. -/
theorem allocatedBool_name (f : NumericFormula) (hf : NumericValid f) (a : Allocated f) :
    booleanName f hf (allocatedBool f a)=(canvasAllocation f hf a).val := by
  cases a with
  | inl i =>
    change boundaryName f hf (initialBoundary f i)=(canvasAllocation f hf (.inl i)).val
    rw [boundaryName_initial,canvasAllocation_old]
  | inr p =>
    rcases p with ⟨i,j⟩
    by_cases hj : j.val<(canvasCell f i).shape.outputCount
    · simp only [allocatedBool,dif_pos hj,booleanName,boundaryName_port,Cell.freshPort_reference,
        canvasAllocation_new]
    · simp only [allocatedBool,dif_neg hj,booleanName,canvasAllocation_new]
      omega

theorem allocatedBool_injective (f : NumericFormula) (hf : NumericValid f) : Function.Injective (allocatedBool f) := by
  intro a b h
  apply (canvasAllocation f hf).injective
  apply Fin.ext
  simpa only [allocatedBool_name] using congrArg (booleanName f hf) h

theorem allocatedBool_surjective (f : NumericFormula) (hf : NumericValid f) : Function.Surjective (allocatedBool f) := by
  intro b
  cases b with
  | inl b =>
    rcases boundaryName_source f hf b with hb | hb
    · let i : Fin f.1 := ⟨boundaryName f hf b,List.mem_range.mp hb⟩
      refine ⟨.inl i,?_⟩
      apply congrArg Sum.inl
      apply boundaryName_injective f hf
      exact boundaryName_initial f hf i
    · obtain ⟨c,hc,hx⟩ := List.mem_flatMap.mp hb
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hc
      subst c
      obtain ⟨j,hj⟩ := (canvasCell f i).output_mem _ hx
      let j' : Fin (canvasCell f i).fresh := ⟨j.val,by
        have h := (canvasCell f i).shape.outputs_add_auxiliaries
        change j.val<(canvasCell f i).shape.kind.template.fresh
        omega⟩
      refine ⟨.inr ⟨i,j'⟩,?_⟩
      have hh : j'.val<(canvasCell f i).shape.outputCount := j.isLt
      simp only [allocatedBool,dif_pos hh]
      apply congrArg Sum.inl
      apply boundaryName_injective f hf
      rw [boundaryName_port,Cell.freshPort_reference]
      exact hj.symm
  | inr b =>
    rcases b with ⟨i,j⟩
    let j' : Fin (canvasCell f i).fresh := ⟨(canvasCell f i).shape.outputCount+j.val,by
      have h := (canvasCell f i).shape.outputs_add_auxiliaries
      change (canvasCell f i).shape.outputCount+j.val<(canvasCell f i).shape.kind.template.fresh
      omega⟩
    refine ⟨.inr ⟨i,j'⟩,?_⟩
    have hh : ¬j'.val<(canvasCell f i).shape.outputCount := by dsimp [j']; omega
    simp only [allocatedBool,dif_neg hh]
    congr 2
    apply Fin.ext
    simp [j']

def variableEquiv (f : NumericFormula) (hf : NumericValid f) :
    Fin (PositiveRoutingCompiler.compile f).1 ≃ BooleanGrid f :=
  (canvasAllocation f hf).symm.trans
    (Equiv.ofBijective (allocatedBool f) ⟨allocatedBool_injective f hf,allocatedBool_surjective f hf⟩)

/-- The inverse coordinate map is exactly the original materialized index. -/
theorem variableEquiv_name (f : NumericFormula) (hf : NumericValid f) (i : Fin (PositiveRoutingCompiler.compile f).1) :
    booleanName f hf (variableEquiv f hf i)=i.val := by
  change booleanName f hf (allocatedBool f ((canvasAllocation f hf).symm i))=i.val
  rw [allocatedBool_name,Equiv.apply_symm_apply]

theorem booleanName_injective (f : NumericFormula) (hf : NumericValid f) : Function.Injective (booleanName f hf) := by
  intro a b h
  obtain ⟨i,rfl⟩ := (variableEquiv f hf).surjective a
  obtain ⟨j,rfl⟩ := (variableEquiv f hf).surjective b
  rw [variableEquiv_name,variableEquiv_name] at h
  exact congrArg (variableEquiv f hf) (Fin.ext h)

end PlanarHom.PositiveBlockProgram
