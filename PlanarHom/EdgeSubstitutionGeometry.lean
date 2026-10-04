import PlanarHom.EdgeSubstitutionAllocation
import PlanarHom.EdgeGadgetTemplateGeometry
import PlanarHom.PlanarHeterogeneousGadgetInsertion

/-! Ordinary planarity of the literal numeric edge-substitution compiler. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.EdgeSubstitution
open Complexity FixedGadgetNetwork

 def selected (ts : List Template) (g : MixedCode) (i : Fin g.edges.length) : Template :=
   gateTemplate ts (gate (g.edges.get i))

 theorem selected_mem (ts : List Template) {ut : ℕ} (g : MixedCode)
     (hg : g.Valid ts.length ut) (i : Fin g.edges.length) : selected ts g i ∈ ts :=
   gateTemplate_mem (hg.1 _ (List.get_mem _ i)).2.2

 def occurrenceOffset (ts : List Template) (g : MixedCode) (i : Fin g.edges.length) : ℕ :=
   g.vertices + ∑ j : Fin i.val, (selected ts g (Fin.castLE i.isLt.le j)).privateCount

 def occurrenceBlock (ts : List Template) (g : MixedCode) (i : Fin g.edges.length) :
     List (ℕ × ℕ × ℕ) :=
   (selected ts g i).edges.map
     (remapEdge (selected ts g i) (occurrenceOffset ts g i) (gate (g.edges.get i)).2)

 theorem substitute_vertices (ts : List Template) (g : MixedCode) :
     (substitute ts g).vertices = g.vertices + ∑ i : Fin g.edges.length, (selected ts g i).privateCount := by
   rw [substitute,compile_vertices]
   simp only [network,List.map_map]
   congr 1
   simpa [selected] using sum_take_map g.edges
     (fun e => (gateTemplate ts (gate e)).privateCount) g.edges.length le_rfl

 theorem substitute_edges (ts : List Template) (g : MixedCode) :
     (substitute ts g).edges = (List.ofFn (occurrenceBlock ts g)).flatten := by
   rw [substitute,compile_edges]
   simp only [network,List.nil_append,edgeBlocks,List.length_map]
   congr 2
   funext i
   have hoff : gateOffset ts g.vertices (g.edges.map gate) i.val = occurrenceOffset ts g i := by
     simp only [gateOffset,occurrenceOffset,← List.map_take,List.map_map,Function.comp_def]
     rw [sum_take_map g.edges (fun e => (gateTemplate ts (gate e)).privateCount) i.val i.isLt.le]
     rfl
   simp only [List.get_eq_getElem,List.getElem_map,Fin.coe_cast,hoff,occurrenceBlock,selected]

 def substitutionVertices (ts : List Template) (g : MixedCode) :
     (Fin g.vertices ⊕ (Σ i : Fin g.edges.length, Fin (selected ts g i).privateCount)) ≃
       Fin (substitute ts g).vertices :=
   ((Equiv.sumCongr (Equiv.refl _) finSigmaFinEquiv).trans finSumFinEquiv).trans
     (finCongr (substitute_vertices ts g).symm)

 @[simp] theorem substitutionVertices_old (ts : List Template) (g : MixedCode) (v : Fin g.vertices) :
     (substitutionVertices ts g (.inl v)).val = v.val := by
   simp [substitutionVertices]

 @[simp] theorem substitutionVertices_private (ts : List Template) (g : MixedCode)
     (i : Fin g.edges.length) (v : Fin (selected ts g i).privateCount) :
     (substitutionVertices ts g (.inr ⟨i,v⟩)).val = occurrenceOffset ts g i + v.val := by
   simp [substitutionVertices,occurrenceOffset,Nat.add_assoc]

 def substitutionEdges (ts : List Template) (g : MixedCode) :
     (Σ i : Fin g.edges.length, Fin (selected ts g i).edges.length) ≃
       Fin (substitute ts g).edges.length :=
   ((Equiv.sigmaCongrRight (fun i : Fin g.edges.length => finCongr (by simp [occurrenceBlock] :
       (selected ts g i).edges.length = (occurrenceBlock ts g i).length))).trans
     (ofFnBlockEquiv (occurrenceBlock ts g))).trans
       (finCongr (congrArg List.length (substitute_edges ts g)).symm)

 theorem get_substitutionEdges (ts : List Template) (g : MixedCode)
     (p : Σ i : Fin g.edges.length, Fin (selected ts g i).edges.length) :
     (substitute ts g).edges.get (substitutionEdges ts g p) =
       remapEdge (selected ts g p.1) (occurrenceOffset ts g p.1)
         (gate (g.edges.get p.1)).2 ((selected ts g p.1).edges.get p.2) := by
   simp only [substitutionEdges,Equiv.trans_apply]
   generalize he : (Equiv.sigmaCongrRight (fun i : Fin g.edges.length =>
     finCongr (by simp [occurrenceBlock] : (selected ts g i).edges.length =
       (occurrenceBlock ts g i).length))) p = q
   have h := get_ofFnBlockEquiv (occurrenceBlock ts g) q
   have hg := substitute_edges ts g
   have hh : (substitute ts g).edges.get
       ((finCongr (congrArg List.length hg).symm) (ofFnBlockEquiv (occurrenceBlock ts g) q)) =
         (List.ofFn (occurrenceBlock ts g)).flatten.get (ofFnBlockEquiv (occurrenceBlock ts g) q) := by
     exact get_finCongr hg _
   rw [hh,h]
   subst q
   simp [Equiv.sigmaCongrRight,occurrenceBlock]

 theorem remapVertex_terminal (t : Template) (hb : t.boundary=2)
     (n s d : ℕ) (v : Bool ⊕ Fin t.privateCount) :
     remapVertex t n [s,d] ((t.terminalVertices hb) v).val =
       Sum.elim (fun b => if b then d else s) (fun w => n+w.val) v := by
   rcases v with b|w
   · cases b <;> simp [Template.terminalVertices,remapVertex,hb,finTwoEquiv]
   · simp [Template.terminalVertices,remapVertex,hb,finTwoEquiv]

 theorem substitutionVertices_attach (ts : List Template) {bt ut : ℕ}
     (ht : ∀ t ∈ ts, t.code.Valid bt ut) (hb : ∀ t ∈ ts, t.boundary=2)
     (g : MixedCode) (hg : g.Valid ts.length ut) (i : Fin g.edges.length)
     (v : Fin ((selected ts g i).boundary+(selected ts g i).privateCount)) :
     (substitutionVertices ts g ((g.toMultiGraph hg).insertFamilyVertex i
       (((selected ts g i).terminalVertices (hb _ (selected_mem ts g hg i))).symm v))).val =
       remapVertex (selected ts g i) (occurrenceOffset ts g i) (gate (g.edges.get i)).2 v.val := by
   obtain ⟨w,rfl⟩ := ((selected ts g i).terminalVertices (hb _ (selected_mem ts g hg i))).surjective v
   rw [Equiv.symm_apply_apply]
   change _ = remapVertex (selected ts g i) (occurrenceOffset ts g i)
     [(g.edges.get i).1,(g.edges.get i).2.1] _
   rw [remapVertex_terminal]
   rcases w with b|w
   · cases b <;> simp [MultiGraph.insertFamilyVertex,MixedCode.toMultiGraph]
   · simp [MultiGraph.insertFamilyVertex]

 def selectedGadget (ts : List Template) {bt ut : ℕ}
     (ht : ∀ t ∈ ts, t.code.Valid bt ut) (hb : ∀ t ∈ ts, t.boundary=2)
     (g : MixedCode) (hg : g.Valid ts.length ut) (i : Fin g.edges.length) :
     TwoTerminal (Fin (selected ts g i).privateCount) (Fin (selected ts g i).edges.length) :=
   (selected ts g i).edgeGadget (hb _ (selected_mem ts g hg i)) (ht _ (selected_mem ts g hg i))

 def substitutionIncidence (ts : List Template) {bt ut : ℕ}
     (ht : ∀ t ∈ ts, t.code.Valid bt ut) (hb : ∀ t ∈ ts, t.boundary=2)
     (g : MixedCode) (hg : g.Valid ts.length ut) :
     MultiGraph.IncidenceEquiv
       ((g.toMultiGraph hg).insertFamily (selectedGadget ts ht hb g hg))
       ((substitute ts g).toMultiGraph (substitute_valid ts ht hb g hg)) where
   vertex := substitutionVertices ts g
   edge := substitutionEdges ts g
   src_eq p := by
     apply Fin.ext
     change ((substitute ts g).edges.get (substitutionEdges ts g p)).1 = _
     rw [get_substitutionEdges]
     exact (substitutionVertices_attach ts ht hb g hg p.1
       (((selected ts g p.1).code.toMultiGraph (ht _ (selected_mem ts g hg p.1))).src p.2)).symm
   dst_eq p := by
     apply Fin.ext
     change ((substitute ts g).edges.get (substitutionEdges ts g p)).2.1 = _
     rw [get_substitutionEdges]
     exact (substitutionVertices_attach ts ht hb g hg p.1
       (((selected ts g p.1).code.toMultiGraph (ht _ (selected_mem ts g hg p.1))).dst p.2)).symm

 theorem substitute_planarValid (ts : List Template) {bt ut : ℕ}
     (ht : ∀ t ∈ ts, t.code.Valid bt ut) (hb : ∀ t ∈ ts, t.boundary=2)
     (hp : ∀ t (h : t ∈ ts), TwoTerminal.PlanarEdgeGadget (t.edgeGadget (hb t h) (ht t h)))
     (g : MixedCode) (hg : g.PlanarValid ts.length ut) :
     (substitute ts g).PlanarValid bt ut := by
   apply (MixedCode.planarValid_iff _ (substitute_valid ts ht hb g hg.1)).mpr
   apply (substitutionIncidence ts ht hb g hg.1).planar_iff.mp
   exact ((MixedCode.planarValid_iff g hg.1).mp hg).insertFamily _
     (fun i => hp _ (selected_mem ts g hg.1 i))

end PlanarHom.EdgeSubstitution
