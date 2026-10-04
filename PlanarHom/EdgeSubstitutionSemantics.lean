import PlanarHom.FixedGadgetNetworkSemantics

/-! NEW reconstruction of genuine literal edge substitution semantics.
This is the full partition sum, with all retained unary occurrences and isolates. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.EdgeSubstitution
open Complexity FixedGadgetNetwork
variable {C R : Type} [Fintype C] [CommSemiring R] {bt ut : ℕ}

theorem gateFactor_gate (ts : List Template) (hb : ∀t∈ts,t.boundary=2)
    (M : Fin bt→Matrix C C R) (U : Fin ut→C→R)
    (n : ℕ) (σ : Fin n→C) (e : ℕ × ℕ × ℕ)
    (he : e.1<n ∧ e.2.1<n ∧ e.2.2<ts.length) :
    gateFactor ts M U n σ (gate e)=MixedCode.binaryValue n ts.length (interactions ts M U) σ e := by
  have hgate : (gate e).Valid ts n := by
    refine ⟨he.2.2,?_,?_⟩
    · simpa [gate] using (hb _ (gateTemplate_mem (a:=gate e) he.2.2)).symm
    · intro v hv
      simp only [gate,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl
      · exact he.1
      · exact he.2.1
  have hget : gateTemplate ts (gate e)=ts.get ⟨e.2.2,he.2.2⟩ :=
    List.getD_eq_getElem ts emptyTemplate he.2.2
  have htwo : (gateTemplate ts (gate e)).boundary=2 := hb _ (gateTemplate_mem hgate.1)
  simp only [gateFactor,dif_pos hgate,MixedCode.binaryValue,dif_pos he,interactions,templateInteraction]
  rw [←hget]
  apply congrArg (templateSignature (gateTemplate ts (gate e)) M U)
  funext v
  unfold portsColor
  by_cases hv : v.val=0
  · simp [gate,hv]
  · have hv1 : v.val=1 := by have := v.isLt; omega
    simp [gate,hv,hv1]

theorem evaluate_substitute (ts : List Template)
    (ht : ∀t∈ts,t.code.Valid bt ut) (hb : ∀t∈ts,t.boundary=2)
    (g : MixedCode) (hg : g.Valid ts.length ut)
    (M : Fin bt→Matrix C C R) (U : Fin ut→C→R) :
    (substitute ts g).evaluate (substitute_valid ts ht hb g hg) M U (fun _=>1) =
      g.evaluate hg (interactions ts M U) U (fun _=>1) := by
  have hn := network_valid ts ht hb g hg
  have h := sum_factor_compile ts ht M U g.vertices (network g).base (network g).gates
    hn.1 le_rfl hn.2.2
  simp only [MixedCode.evaluate,Finset.prod_const_one,one_mul]
  change (∑ σ,factor (substitute ts g) M U σ)=_
  rw [show substitute ts g=compile ts (network g) from rfl,h]
  apply Finset.sum_congr rfl
  intro σ _
  have he : g.edges.map (fun e=>gateFactor ts M U g.vertices σ (gate e))=
      g.edges.map (MixedCode.binaryValue g.vertices ts.length (interactions ts M U) σ) :=
    List.map_congr_left (fun e he=>gateFactor_gate ts hb M U _ σ e (hg.1 e he))
  simp only [network,restrictColor_refl,factor,List.map_nil,List.prod_nil,one_mul,
    List.map_map,Function.comp_def] at *
  rw [he]
  exact mul_comm _ _

end PlanarHom.EdgeSubstitution
