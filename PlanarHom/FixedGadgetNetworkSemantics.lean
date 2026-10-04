import PlanarHom.EdgeSubstitutionCode

/-! NEW reconstruction: attachment is exactly a finite-assignment Fubini sum.
All old factors and every occurrence in each template are retained literally. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedGadgetNetwork
open Complexity
variable {C R : Type} [Fintype C] [CommSemiring R] {bt ut n p : ℕ}

def restrictColor {m n : ℕ} (h : m≤n) (σ : Fin n→C) : Fin m→C :=
  fun v=>σ (Fin.castLE h v)

@[simp] theorem restrictColor_merge {m n p : ℕ} (h : m≤n)
    (σ : Fin n→C) (η : Fin p→C) :
    restrictColor (h.trans (Nat.le_add_right n p)) (mergeColor σ η)=restrictColor h σ := by
  funext v
  exact mergeColor_left σ η (Fin.castLE h v)

@[simp] theorem restrictColor_refl (σ : Fin n→C) : restrictColor le_rfl σ=σ := rfl

theorem sum_mergeColor (f : (Fin (n+p)→C)→R) :
    ∑ σ,f σ = ∑ τ : Fin n→C,∑ η : Fin p→C,f (mergeColor τ η) := by
  let e : ((Fin n→C) × (Fin p→C)) ≃ (Fin (n+p)→C) :=
    (Equiv.sumArrowEquivProdArrow (Fin n) (Fin p) C).symm.trans
      (finSumFinEquiv.arrowCongr (Equiv.refl C))
  rw [←e.sum_comp f,Fintype.sum_prod_type]
  rfl

def portsColor (t : Template) (ports : List ℕ) (hp : ports.length=t.boundary)
    (hr : ∀v∈ports,v<n) (σ : Fin n→C) : Fin t.boundary→C :=
  fun v=>σ ⟨ports.getD v.val 0,hr _ (by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem (by omega))⟩

theorem remap_color (t : Template) (ports : List ℕ) (hp : ports.length=t.boundary)
    (hr : ∀v∈ports,v<n) (σ : Fin n→C) (η : Fin t.privateCount→C)
    (v : Fin (t.boundary+t.privateCount)) :
    mergeColor σ η ⟨remapVertex t n ports v.val,remapVertex_lt t n ports hp hr _ v.isLt⟩ =
      mergeColor (portsColor t ports hp hr σ) η v := by
  induction v using Fin.addCases with
  | left v =>
    have h : (Fin.castAdd t.privateCount v).val<t.boundary := v.isLt
    simp only [remapVertex,h,↓reduceIte,mergeColor_left]
    exact mergeColor_left σ η ⟨ports.getD v.val 0,hr _ (by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem (by omega))⟩
  | right v =>
    have h : remapVertex t n ports (Fin.natAdd t.boundary v).val=n+v.val := by
      simp [remapVertex,Fin.natAdd]
    simp only [h,mergeColor_right]
    exact mergeColor_right σ η v

theorem binaryValue_old (M : Fin bt→Matrix C C R) (σ : Fin n→C) (η : Fin p→C)
    (e : ℕ × ℕ × ℕ) (hv : e.1<n ∧ e.2.1<n ∧ e.2.2<bt) :
    MixedCode.binaryValue (n+p) bt M (mergeColor σ η) e =
      MixedCode.binaryValue n bt M σ e := by
  have hv' : e.1<n+p ∧ e.2.1<n+p ∧ e.2.2<bt := by omega
  simp only [MixedCode.binaryValue,dif_pos hv,dif_pos hv']
  exact congrArg₂ (M ⟨e.2.2,hv.2.2⟩) (mergeColor_left σ η ⟨e.1,hv.1⟩)
    (mergeColor_left σ η ⟨e.2.1,hv.2.1⟩)

theorem unaryValue_old (U : Fin ut→C→R) (σ : Fin n→C) (η : Fin p→C)
    (u : ℕ × ℕ) (hv : u.1<n ∧ u.2<ut) :
    MixedCode.unaryValue (n+p) ut U (mergeColor σ η) u =
      MixedCode.unaryValue n ut U σ u := by
  have hv' : u.1<n+p ∧ u.2<ut := by omega
  simp only [MixedCode.unaryValue,dif_pos hv,dif_pos hv']
  exact congrArg (U ⟨u.2,hv.2⟩) (mergeColor_left σ η ⟨u.1,hv.1⟩)

theorem factor_attachTemplate (t : Template) (g : MixedCode) (ports : List ℕ)
    (ht : t.code.Valid bt ut) (hg : g.Valid bt ut)
    (hp : ports.length=t.boundary) (hr : ∀v∈ports,v<g.vertices)
    (M : Fin bt→Matrix C C R) (U : Fin ut→C→R)
    (σ : Fin g.vertices→C) (η : Fin t.privateCount→C) :
    factor (attachTemplate t g ports) M U (mergeColor σ η) =
      factor g M U σ * factor t.code M U (mergeColor (portsColor t ports hp hr σ) η) := by
  have heold : g.edges.map (MixedCode.binaryValue (g.vertices+t.privateCount) bt M (mergeColor σ η))=
      g.edges.map (MixedCode.binaryValue g.vertices bt M σ) :=
    List.map_congr_left (fun e he=>binaryValue_old M σ η e (hg.1 e he))
  have huold : g.unaries.map (MixedCode.unaryValue (g.vertices+t.privateCount) ut U (mergeColor σ η))=
      g.unaries.map (MixedCode.unaryValue g.vertices ut U σ) :=
    List.map_congr_left (fun u hu=>unaryValue_old U σ η u (hg.2 u hu))
  have henew : t.edges.map (fun e=>MixedCode.binaryValue (g.vertices+t.privateCount) bt M
      (mergeColor σ η) (remapEdge t g.vertices ports e))=
      t.edges.map (MixedCode.binaryValue t.code.vertices bt M
        (mergeColor (portsColor t ports hp hr σ) η)) := by
    apply List.map_congr_left
    intro e he
    have hv := ht.1 e he
    have h1 := remapVertex_lt t g.vertices ports hp hr e.1 hv.1
    have h2 := remapVertex_lt t g.vertices ports hp hr e.2.1 hv.2.1
    simp only [remapEdge,MixedCode.binaryValue,h1,h2,hv.1,hv.2.1,hv.2.2,and_self,↓reduceDIte]
    exact congrArg₂ (M ⟨e.2.2,hv.2.2⟩)
      (remap_color t ports hp hr σ η ⟨e.1,hv.1⟩)
      (remap_color t ports hp hr σ η ⟨e.2.1,hv.2.1⟩)
  have hunew : t.unaries.map (fun u=>MixedCode.unaryValue (g.vertices+t.privateCount) ut U
      (mergeColor σ η) (remapUnary t g.vertices ports u))=
      t.unaries.map (MixedCode.unaryValue t.code.vertices ut U
        (mergeColor (portsColor t ports hp hr σ) η)) := by
    apply List.map_congr_left
    intro u hu
    have hv := ht.2 u hu
    have h1 := remapVertex_lt t g.vertices ports hp hr u.1 hv.1
    simp only [remapUnary,MixedCode.unaryValue,h1,hv.1,hv.2,and_self,↓reduceDIte]
    exact congrArg (U ⟨u.2,hv.2⟩) (remap_color t ports hp hr σ η ⟨u.1,hv.1⟩)
  simp only [factor,attachTemplate,List.map_append,List.prod_append,List.map_map,
    Function.comp_def,heold,huold,henew,hunew,Template.code]
  ring

/-- One finite gate signature, interpreted on its fixed shared vertices.
The default branch is irrelevant for valid networks but makes this total. -/
def gateFactor (ts : List Template) (M : Fin bt→Matrix C C R) (U : Fin ut→C→R)
    (shared : ℕ) (σ : Fin shared→C) (a : Gate) : R :=
  if h : a.Valid ts shared then
    templateSignature (gateTemplate ts a) M U
      (portsColor (gateTemplate ts a) a.2 h.2.1 h.2.2 σ)
  else 1

/-- Exact semantics for a whole attachment fold. Shared vertices need not fill
all of the current graph, and private assignments are summed, never chosen. -/
theorem sum_factor_compile (ts : List Template)
    (ht : ∀t∈ts,t.code.Valid bt ut) (M : Fin bt→Matrix C C R) (U : Fin ut→C→R)
    (shared : ℕ) (g : MixedCode) (as : List Gate) (hg : g.Valid bt ut)
    (hs : shared≤g.vertices) (ha : ∀a∈as,a.Valid ts shared) :
    (∑ σ : Fin (compile ts ⟨g,as⟩).vertices→C,factor (compile ts ⟨g,as⟩) M U σ) =
      ∑ σ : Fin g.vertices→C,factor g M U σ *
        (as.map (gateFactor ts M U shared (restrictColor hs σ))).prod := by
  induction as generalizing g with
  | nil => simp [compile]
  | cons a as ih =>
    have hva := ha a (by simp)
    have hta := ht _ (gateTemplate_mem hva.1)
    have hra : ∀v∈a.2,v<g.vertices := fun v hv=>(hva.2.2 v hv).trans_le hs
    have hga : (compileStep ts g a).Valid bt ut :=
      attachTemplate_valid _ _ _ hta hg hva.2.1 hra
    have hsa : shared≤(compileStep ts g a).vertices := hs.trans (Nat.le_add_right _ _)
    change (∑ σ : Fin (compile ts ⟨compileStep ts g a,as⟩).vertices→C,
      factor (compile ts ⟨compileStep ts g a,as⟩) M U σ)=_
    rw [ih (compileStep ts g a) hga hsa (fun b hb=>ha b (by simp [hb]))]
    change (∑ σ : Fin (g.vertices+(gateTemplate ts a).privateCount)→C,
      factor (attachTemplate (gateTemplate ts a) g a.2) M U σ *
        (as.map (gateFactor ts M U shared (restrictColor hsa σ))).prod)=_
    rw [sum_mergeColor]
    apply Finset.sum_congr rfl
    intro σ _
    have hpcol : portsColor (gateTemplate ts a) a.2 hva.2.1 hra σ =
        portsColor (gateTemplate ts a) a.2 hva.2.1 hva.2.2 (restrictColor hs σ) := rfl
    have hrestrict (η : Fin (gateTemplate ts a).privateCount→C) :
        restrictColor hsa (mergeColor σ η)=restrictColor hs σ := restrictColor_merge hs σ η
    simp only [factor_attachTemplate _ _ _ hta hg hva.2.1 hra,hrestrict,
      List.map_cons,List.prod_cons,gateFactor,dif_pos hva]
    rw [hpcol]
    simp only [templateSignature]
    rw [←Finset.sum_mul,←Finset.mul_sum]
    ring

end PlanarHom.FixedGadgetNetwork
