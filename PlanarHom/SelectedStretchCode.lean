import PlanarHom.GraphStretchCode
import PlanarHom.MixedPlanarCode
import Mathlib.Data.List.Enum

/-! Selected binary occurrences are replaced by positive-length paths. Fresh
vertices are private to selected occurrences. All companion occurrences and
all original unary occurrences are retained. The parameter `n` means `n+1`
segments and `n` fresh vertices per selected occurrence. -/

namespace PlanarHom.Complexity.MixedCode

def selectedEdges (g : MixedCode) (selected : ℕ) : List (ℕ × (ℕ × ℕ)) :=
  g.edges.filter (fun e => decide (e.2.2=selected))

def companionEdges (g : MixedCode) (selected : ℕ) : List (ℕ × (ℕ × ℕ)) :=
  g.edges.filter (fun e => decide (e.2.2≠selected))

def selectedGraph (g : MixedCode) (selected : ℕ) : GraphCode :=
  ⟨g.vertices,(g.selectedEdges selected).map (fun e => (e.1,e.2.1))⟩

@[simp] theorem selectedGraph_vertices (g : MixedCode) (selected : ℕ) :
    (g.selectedGraph selected).vertices=g.vertices := rfl

@[simp] theorem selectedGraph_edges_length (g : MixedCode) (selected : ℕ) :
    (g.selectedGraph selected).edges.length=(g.selectedEdges selected).length := by
  simp [selectedGraph]

theorem selectedGraph_valid {a u : ℕ} (g : MixedCode) (hg : g.Valid a u) (selected : ℕ) :
    (g.selectedGraph selected).Valid := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  have hv := hg.1 f (List.mem_filter.mp hf).1
  exact ⟨hv.1,hv.2.1⟩

/-- The source and target labels are separate: selected auxiliary occurrences
become paths using the already available matrix label `replacement`. -/
def stretchLabel (g : MixedCode) (selected replacement n : ℕ) : MixedCode :=
  ⟨((g.selectedGraph selected).stretch n).vertices,
    ((g.selectedGraph selected).stretch n).edges.map (fun e => (e.1,e.2,replacement)) ++
      g.companionEdges selected,
    g.unaries⟩

@[simp] theorem stretchLabel_vertices (g : MixedCode) (selected replacement n : ℕ) :
    (g.stretchLabel selected replacement n).vertices=
      g.vertices+(g.selectedEdges selected).length*n := by
  simp [stretchLabel]

@[simp] theorem stretchLabel_unaries (g : MixedCode) (selected replacement n : ℕ) :
    (g.stretchLabel selected replacement n).unaries=g.unaries := rfl

@[simp] theorem stretchLabel_edges_length (g : MixedCode) (selected replacement n : ℕ) :
    (g.stretchLabel selected replacement n).edges.length=
      (g.selectedEdges selected).length*(n+1)+(g.companionEdges selected).length := by
  simp [stretchLabel]

theorem selected_companion_lengths (g : MixedCode) (selected : ℕ) :
    (g.selectedEdges selected).length+(g.companionEdges selected).length=g.edges.length := by
  have h := (List.filter_append_perm (fun e : ℕ × (ℕ × ℕ) => decide (e.2.2=selected)) g.edges).length_eq
  simpa [selectedEdges, companionEdges] using h

/-- Exact size increase: `n` vertices and `n` net edges per selected occurrence. -/
theorem stretchLabel_edges_length_add (g : MixedCode) (selected replacement n : ℕ) :
    (g.stretchLabel selected replacement n).edges.length=
      g.edges.length+(g.selectedEdges selected).length*n := by
  rw [stretchLabel_edges_length]
  have h := g.selected_companion_lengths selected
  nlinarith

theorem stretchLabel_valid {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (selected replacement n : ℕ) (hr : replacement<b)
    (hkeep : ∀ e∈g.edges,e.2.2≠selected→e.2.2<b) :
    (g.stretchLabel selected replacement n).Valid b u := by
  have hv := (g.selectedGraph selected).stretch_valid (g.selectedGraph_valid hg selected) n
  have hV : g.vertices≤(g.stretchLabel selected replacement n).vertices := by
    simp only [stretchLabel_vertices]; omega
  constructor
  · intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      exact ⟨(hv f hf).1,(hv f hf).2,hr⟩
    · have he' := List.mem_filter.mp he
      have h := hg.1 e he'.1
      exact ⟨h.1.trans_le hV,h.2.1.trans_le hV,hkeep e he'.1 (by simpa using he'.2)⟩
  · intro e he
    exact ⟨(hg.2 e he).1.trans_le hV,(hg.2 e he).2⟩

/-- Arithmetic presentation of a path segment, used by the actual compiler.
All natural inputs are allowed; validity is established separately. -/
def pathSegment (vertices replacement n : ℕ) (e : (ℕ × (ℕ × ℕ)) × ℕ)
    (k : ℕ) : ℕ × (ℕ × ℕ) :=
  (if k=0 then e.1.1 else vertices+e.2*n+(k-1),
    if k=n then e.1.2.1 else vertices+e.2*n+k,
    replacement)

def pathList (vertices replacement n : ℕ) (e : (ℕ × (ℕ × ℕ)) × ℕ) :
    List (ℕ × (ℕ × ℕ)) :=
  (List.range (n+1)).map (pathSegment vertices replacement n e)

theorem pathList_eq_ofFn (vertices replacement n : ℕ) (e : (ℕ × (ℕ × ℕ)) × ℕ) :
    pathList vertices replacement n e =
      List.ofFn (fun k : Fin (n+1) => pathSegment vertices replacement n e k.val) := by
  apply List.ext_getElem
  · simp [pathList]
  · intro i hi hj
    simp only [pathList, List.getElem_map, List.getElem_range, List.getElem_ofFn]

theorem zipIdx_eq_ofFn {α : Type} (xs : List α) :
    xs.zipIdx = List.ofFn (fun i : Fin xs.length => (xs.get i,i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Equality of the incidence-indexed definition with its arithmetic list
implementation. This is the bridge used by the ordinary polynomial machine. -/
theorem stretchLabel_edges_eq_flatMap (g : MixedCode) (selected replacement n : ℕ) :
    (g.stretchLabel selected replacement n).edges =
      (g.selectedEdges selected).zipIdx.flatMap (pathList g.vertices replacement n) ++
        g.companionEdges selected := by
  change _ ++ g.companionEdges selected = _ ++ g.companionEdges selected
  apply congrArg (fun es => es ++ g.companionEdges selected)
  change (List.ofFn (fun q => (g.selectedGraph selected).stretchEndpoints n
    (finProdFinEquiv.symm q))).map (fun e => (e.1,e.2,replacement)) = _
  rw [List.map_ofFn, List.ofFn_mul, zipIdx_eq_ofFn]
  simp only [List.flatMap, List.map_ofFn, Function.comp_apply]
  congr 1
  simp only [selectedGraph, List.length_map]
  congr 1
  funext i
  simp only [Function.comp_apply, pathList_eq_ofFn]
  congr 1
  funext j
  have hdiv : (j.val+i.val*(n+1))/(n+1)=i.val := by
    rw [Nat.add_mul_div_right _ _ (Nat.succ_pos n), Nat.div_eq_of_lt j.isLt]
    omega
  simp [GraphCode.stretchEndpoints, GraphCode.stretchInternal, pathSegment,
    finProdFinEquiv, Fin.divNat, Fin.modNat, Nat.mul_comm, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc, Nat.mod_eq_of_lt j.isLt,
    hdiv]

end PlanarHom.Complexity.MixedCode
