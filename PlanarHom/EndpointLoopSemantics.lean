import PlanarHom.EndpointLoopMachines

/-! Exact endpoint-loop signatures, with every original background and unary
unchanged. Marked loops receive both decorations at the same color. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.EndpointLoopMachines
open Complexity Complexity.MixedCode FiniteLanguageAliases FiniteLabelLookupMachines
variable {C R : Type} [Fintype C] [CommSemiring R]

def decorated (A : Matrix C C R) (k : ℕ) : Matrix C C R :=
  fun i j=>(A i i)^k*A i j*(A j j)^k

def loopScalar (n : ℕ) (A : Matrix C C R) (σ : Fin n→C) (r : ℕ) : R :=
  if h:r<n then A (σ ⟨r,h⟩) (σ ⟨r,h⟩) else 0

theorem loopVertices_product (selected k : ℕ) (g : MixedCode) (f : ℕ→R) :
    ((loopVertices selected k g).map f).prod=
      (g.edges.map (fun e=>if e.2.2=selected then f e.1^k*f e.2.1^k else 1)).prod := by
  unfold loopVertices GraphDegreeMachines.endpoints
  induction g.edges with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_flatten,List.prod_flatten,List.map_map] at ih
    by_cases he:e.2.2=selected <;>
      simp [he,List.flatMap_cons,List.map_replicate,List.prod_replicate,ih,mul_assoc]

theorem sourceLabels {b : ℕ} (M : Fin b→Matrix C C R) (old : Fin b) :
    M ∘ dropAux old=appendOne M (M old) := by
  funext l
  refine Fin.lastCases ?_ (fun i=>?_) l
  · simp [dropAux,appendOne_aux]
  · simp only [Function.comp_apply,dropAux,Fin.lastCases_castSucc,id_eq]
    change M i=appendOne M (M old) (Fin.castAdd 1 i)
    rw [appendOne_old]

theorem edge_value_decorated {b n : ℕ} (M : Fin b→Matrix C C R) (old : Fin b) (k : ℕ)
    (σ : Fin n→C) (e : ℕ×ℕ×ℕ) (hv : e.1<n ∧ e.2.1<n ∧ e.2.2<b+1) :
    binaryValue n (b+1) (appendOne M (M old)) σ e *
      (if e.2.2=b then loopScalar n (M old) σ e.1^k*loopScalar n (M old) σ e.2.1^k else 1) =
    binaryValue n (b+1) (appendOne M (decorated (M old) k)) σ e := by
  rw [binaryValue,dif_pos hv,binaryValue,dif_pos hv]
  by_cases he:e.2.2=b
  · have hl : (⟨e.2.2,hv.2.2⟩ : Fin (b+1))=Fin.last b := Fin.ext he
    simp only [if_pos he,hl,appendOne_aux,loopScalar,dif_pos hv.1,dif_pos hv.2.1,decorated]
    ring
  · have hlt : e.2.2<b := by omega
    have hl : (⟨e.2.2,hv.2.2⟩ : Fin (b+1))=Fin.castAdd 1 ⟨e.2.2,hlt⟩ := rfl
    simp only [if_neg he,hl,appendOne_old,mul_one]

theorem evaluate_transform {b u : ℕ} (old : Fin b) (k : ℕ) (g : MixedCode)
    (hg : g.Valid (b+1) u) (M : Fin b→Matrix C C R) (U : Fin u→C→R) (w : C→R)
    (hout : (transform old k g).Valid b u) :
    (transform old k g).evaluate hout M U w=
      g.evaluate hg (appendOne M (decorated (M old) k)) U w := by
  unfold evaluate
  apply Finset.sum_congr rfl
  intro σ _
  change Fin g.vertices→C at σ
  change (∏v : Fin g.vertices,w (σ v))*
      ((((g.relabelBinary (finTable (dropAux old))).edges ++
        (loopVertices b k g).map (fun r=>(r,r,old.val))).map
          (binaryValue g.vertices b M σ)).prod)*
      (g.unaries.map (unaryValue g.vertices u U σ)).prod = _
  rw [List.map_append,List.prod_append,List.map_map]
  have hbase : (((g.relabelBinary (finTable (dropAux old))).edges).map
      (binaryValue g.vertices b M σ))=
      g.edges.map (binaryValue g.vertices (b+1) (appendOne M (M old)) σ) := by
    change (g.edges.map (fun e=>(e.1,e.2.1,lookup (finTable (dropAux old)) e.2.2))).map _=_
    rw [List.map_map]
    apply List.map_congr_left
    intro e he
    have hv := hg.1 e he
    have hl := lookup_finTable (dropAux old) ⟨e.2.2,hv.2.2⟩
    have ht : e.1<g.vertices ∧ e.2.1<g.vertices ∧ lookup (finTable (dropAux old)) e.2.2<b :=
      ⟨hv.1,hv.2.1,lookup_finTable_lt _ _ hv.2.2⟩
    simp only [Function.comp_apply]
    rw [binaryValue,dif_pos ht,binaryValue,dif_pos hv]
    have hf : (⟨lookup (finTable (dropAux old)) e.2.2,ht.2.2⟩ : Fin b)=dropAux old ⟨e.2.2,hv.2.2⟩ := Fin.ext hl
    change M (⟨lookup (finTable (dropAux old)) e.2.2,ht.2.2⟩ : Fin b)
      (σ ⟨e.1,hv.1⟩) (σ ⟨e.2.1,hv.2.1⟩)=_
    rw [hf]
    have hh := congrFun (congrFun (congrFun (sourceLabels M old) ⟨e.2.2,hv.2.2⟩)
      (σ ⟨e.1,hv.1⟩)) (σ ⟨e.2.1,hv.2.1⟩)
    exact hh
  have hloop : ((loopVertices b k g).map (binaryValue g.vertices b M σ ∘ fun r=>(r,r,old.val)))=
      (loopVertices b k g).map (loopScalar g.vertices (M old) σ) := by
    apply List.map_congr_left
    intro r hr
    have hv := loopVertices_lt g hg b k r hr
    simp [Function.comp_def,binaryValue,loopScalar,hv,old.isLt]
  rw [hbase,hloop,loopVertices_product]
  have hp : (g.edges.map (binaryValue g.vertices (b+1) (appendOne M (M old)) σ)).prod *
      (g.edges.map (fun e=>if e.2.2=b then
        loopScalar g.vertices (M old) σ e.1^k*loopScalar g.vertices (M old) σ e.2.1^k else 1)).prod=
      (g.edges.map (binaryValue g.vertices (b+1) (appendOne M (decorated (M old) k)) σ)).prod := by
    rw [←List.prod_map_mul]
    apply congrArg List.prod
    apply List.map_congr_left
    intro e he
    exact edge_value_decorated M old k σ e (hg.1 e he)
  rw [hp]

end PlanarHom.EndpointLoopMachines
