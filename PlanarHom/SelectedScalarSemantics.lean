import PlanarHom.MarkedOccurrenceCount
import PlanarHom.MixedProductSemantics
import PlanarHom.PrescribedDomainAliases

/-! Scaling one selected constraint counts its actual edge occurrences,
including loops and repetitions, while preserving every other contribution. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.SelectedScalarSemantics
open Complexity Complexity.MixedCode FiniteLanguageAliases
variable {C R : Type} [Fintype C] [CommSemiring R] {b u : ℕ}

def scaled (M : Fin b→Matrix C C R) (selected : Fin b) (c : R) : Fin b→Matrix C C R :=
  fun l=>if l=selected then c • M l else M l

theorem selected_product (g : MixedCode) (hg : g.Valid b u)
    (M : Fin b→Matrix C C R) (selected : Fin b) (c : R) (σ : Fin g.vertices→C) :
    selectedBinaryProduct g selected.val (scaled M selected c) σ=
      c^(g.markedCount selected.val)*selectedBinaryProduct g selected.val M σ := by
  unfold selectedBinaryProduct
  have he : ((g.edges.filter (fun e=>e.2.2=selected.val)).map
      (binaryValue g.vertices b (scaled M selected c) σ))=
      (g.edges.filter (fun e=>e.2.2=selected.val)).map (fun e=>c*binaryValue g.vertices b M σ e) := by
    apply List.map_congr_left
    intro e he
    have hv:=hg.1 e (List.mem_filter.mp he).1
    have hl : (⟨e.2.2,hv.2.2⟩ : Fin b)=selected := Fin.ext (by simpa using (List.mem_filter.mp he).2)
    simp [binaryValue,hv,scaled,hl,Matrix.smul_apply,smul_eq_mul]
  rw [he,List.prod_map_mul]
  simp [markedCount]

theorem evaluate_scaled (g : MixedCode) (hg : g.Valid b u)
    (M : Fin b→Matrix C C R) (U : Fin u→C→R) (w : C→R) (selected : Fin b) (c : R) :
    g.evaluate hg (scaled M selected c) U w=c^(g.markedCount selected.val)*g.evaluate hg M U w := by
  rw [evaluate_eq_binary_product_sum g hg selected.val,evaluate_eq_binary_product_sum g hg selected.val,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [selected_product g hg]
  have hrest := binaryRemainder_congr g selected.val M (scaled M selected c) U w
    (by intro l hl; simp [scaled,show l≠selected from fun he=>hl (congrArg Fin.val he)]) σ
  rw [hrest]
  ring

theorem scaled_append (M : Fin b→Matrix C C R) (A : Matrix C C R) (c : R) :
    scaled (appendOne M A) (Fin.last b) c=appendOne M (c • A) := by
  funext l
  refine Fin.lastCases ?_ (fun i=>?_) l
  · simp [scaled,appendOne_aux]
  · simp only [scaled,Fin.castSucc_ne_last,↓reduceIte]
    change appendOne M A (Fin.castAdd 1 i)=appendOne M (c • A) (Fin.castAdd 1 i)
    simp [appendOne_old]

theorem evaluate_append_smul (g : MixedCode) (hg : g.Valid (b+1) u)
    (M : Fin b→Matrix C C R) (A : Matrix C C R) (U : Fin u→C→R) (w : C→R) (c : R) :
    g.evaluate hg (appendOne M (c • A)) U w=c^(g.markedCount b)*g.evaluate hg (appendOne M A) U w := by
  rw [←scaled_append]
  exact evaluate_scaled g hg _ U w (Fin.last b) c

end PlanarHom.SelectedScalarSemantics
