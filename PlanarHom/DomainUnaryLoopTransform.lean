import PlanarHom.DomainUnaryLoopPermutation
import PlanarHom.PrescribedDomainQueryPromises

/-! Literal preservation of reserved domain metadata while an appended unary
occurrence becomes a loop. The old vertex-domain function is unchanged. -/
noncomputable section
open Classical
namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode FiniteLanguageAliases FiniteLabelLookupMachines

def domainUnaryLoopTransform (u d selected : ℕ) (g : MixedCode) : MixedCode :=
  realizeUnaryLoops (u+d) selected (g.relabelUnary (finTable (auxUnaryLast u d)))

private theorem selected_old_unaries (u d selected : ℕ) (xs : List (ℕ×ℕ))
    (hx : ∀e∈xs,e.2<u+1) :
    List.map (fun e : ℕ×ℕ=>(e.1,e.1,selected))
      (List.filter (fun e : ℕ×ℕ=>decide (e.2=u+d))
        (xs.map (fun e=>(e.1,lookup (finTable (auxUnaryLast u d)) e.2)))) =
      (xs.filter (fun e=>decide (e.2=u))).map (fun e=>(e.1,e.1,selected)) := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    have ht : ∀a∈xs,a.2<u+1 := fun a ha=>hx a (by simp [ha])
    have he := hx e (by simp)
    by_cases h : e.2=u
    · simp [h,ih ht]
    · have hl : e.2<u := by omega
      have hn : e.2≠u+d := by omega
      simp [lookup_auxUnaryLast_old (d:=d) hl,h,hn,ih ht]

private theorem retained_old_unaries (u d : ℕ) (xs : List (ℕ×ℕ))
    (hx : ∀e∈xs,e.2<u+1) :
    List.filter (fun e : ℕ×ℕ=>decide (e.2≠u+d))
      (xs.map (fun e=>(e.1,lookup (finTable (auxUnaryLast u d)) e.2))) =
      xs.filter (fun e=>decide (e.2≠u)) := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    have ht : ∀a∈xs,a.2<u+1 := fun a ha=>hx a (by simp [ha])
    have he := hx e (by simp)
    have ih2 := ih ht
    simp only [ne_eq,decide_not] at ih2
    by_cases h : e.2=u
    · simp [h,ih2]
    · have hl : e.2<u := by omega
      have hn : e.2≠u+d := by omega
      simp [lookup_auxUnaryLast_old (d:=d) hl,h,hn,ih2]

private theorem domainOccurrences_relabel {d : ℕ} (u : ℕ) (g : MixedCode) (δ : Fin g.vertices→Fin d) :
    ((domainOccurrences (unaryTypes:=u+1) g δ).map
      (fun e=>(e.1,lookup (finTable (auxUnaryLast u d)) e.2))) =
      domainOccurrences (unaryTypes:=u) g δ := by
  simp only [domainOccurrences,List.map_ofFn]
  congr 1
  funext v
  simp only [Function.comp_apply,lookup_auxUnaryLast_domain]

private theorem domainOccurrences_ne {d : ℕ} (u : ℕ) (g : MixedCode) (δ : Fin g.vertices→Fin d)
    (e : ℕ×ℕ) (he : e∈domainOccurrences (unaryTypes:=u) g δ) : e.2≠u+d := by
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp he
  have h := (δ v).isLt
  change u+(δ v).val≠u+d
  omega

theorem domainUnaryLoopTransform_withDomains {b u d : ℕ} (g : MixedCode) (hg : g.Valid b (u+1))
    (δ : Fin g.vertices→Fin d) (selected : ℕ) :
    domainUnaryLoopTransform u d selected (withDomains (unaryTypes:=u+1) g δ) =
      withDomains (unaryTypes:=u) (realizeUnaryLoops u selected g) δ := by
  have hsel := selected_old_unaries u d selected g.unaries (fun e he=>(hg.2 e he).2)
  have hret := retained_old_unaries u d g.unaries (fun e he=>(hg.2 e he).2)
  have heq : (domainOccurrences (unaryTypes:=u) g δ).filter (fun e=>decide (e.2=u+d))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp [domainOccurrences_ne u g δ e he]
  have hne : (domainOccurrences (unaryTypes:=u) g δ).filter (fun e=>decide (e.2≠u+d))=
      domainOccurrences (unaryTypes:=u) g δ := by
    apply List.filter_eq_self.mpr
    intro e he
    simp [domainOccurrences_ne u g δ e he]
  simp only [domainUnaryLoopTransform,withDomains,relabelUnary,realizeUnaryLoops,List.map_append,
    domainOccurrences_relabel,List.filter_append,List.map_append,hsel,hret,heq,hne,List.map_nil,List.append_nil]
  rfl

theorem fp_domainUnaryLoopTransform (u d selected : ℕ) :
    FP encoding encoding (domainUnaryLoopTransform u d selected) :=
  (fp_relabelUnary (finTable (auxUnaryLast u d))).comp (fp_realizeUnaryLoops (u+d) selected)

theorem Typed.realizeUnaryLoops {b u d : ℕ}
    {B : Fin b→Fin d→Fin d→Prop} {T : Fin u→Fin d→Prop} {TV : Fin d→Prop}
    {g : MixedCode} {hg : g.Valid b (u+1)} {δ : Fin g.vertices→Fin d}
    (ht : Typed B (appendOne T TV) g hg δ) (selected : Fin b)
    (hloop : ∀x,TV x→B selected x x) :
    Typed B T (realizeUnaryLoops u selected.val g) (realizeUnaryLoops_valid selected g hg) δ := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he|he
    · exact ht.1 e he
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
      have hh := hg.2 v (List.mem_filter.mp hv).1
      have hl : v.2=u := of_decide_eq_true (List.mem_filter.mp hv).2
      have hu := ht.2 v (List.mem_filter.mp hv).1
      have hei : (⟨v.2,hh.2⟩ : Fin (u+1))=Fin.last u := Fin.ext hl
      rw [hei,appendOne_aux] at hu
      exact hloop _ hu
  · intro e he
    have hh := hg.2 e (List.mem_filter.mp he).1
    have hl : e.2≠u := of_decide_eq_true (List.mem_filter.mp he).2
    have hlt : e.2<u := by omega
    have hu := ht.2 e (List.mem_filter.mp he).1
    change appendOne T TV (Fin.castAdd 1 ⟨e.2,hlt⟩) _ at hu
    rw [appendOne_old] at hu
    exact hu

theorem EncodedGraph.domainUnaryLoopTransform {b u d : ℕ}
    {B : Fin b→Fin d→Fin d→Prop} {T : Fin u→Fin d→Prop} {TV : Fin d→Prop}
    {g : MixedCode} (h : EncodedGraph B (appendOne T TV) g) (selected : Fin b)
    (hloop : ∀x,TV x→B selected x x) :
    EncodedGraph B T (domainUnaryLoopTransform u d selected.val g) := by
  obtain ⟨original,hg,δ,ht,hp,hd⟩ := h
  rw [MixedCode.encoding.decode_encode] at hd
  have he : g=withDomains (unaryTypes:=u+1) original δ := Option.some.inj hd
  subst g
  unfold EncodedGraph
  rw [domainUnaryLoopTransform_withDomains original hg]
  exact encodedInput_encode_withDomains (ht.realizeUnaryLoops selected hloop)
    (realizeUnaryLoops_planar selected original ⟨hg,hp⟩).2

end PlanarHom.PrescribedDomains
