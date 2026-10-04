import PlanarHom.RadialPottsAssembly
import PlanarHom.OccurrencePfaffianPairings

/-! NEW reconstruction: exact long-edge incidence degrees of the materialized
radial assembly. Port pairing is a proved two-element fiber, not a quotient
with an assumed cardinality or an abstract degree promise. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile
variable {E : Type} {k : ℕ}

noncomputable def longDartEquiv (rotation : Equiv.Perm (Medial.Dart E)) (k : ℕ) :
    ((E × Long k) × Bool) ≃ ((E × White k) ⊕ ((Medial.Dart E × Fin k) × Bool)) :=
  (Equiv.prodAssoc E (Long k) Bool).trans
    ((Equiv.prodCongr (Equiv.refl E) (longEndpointEquiv k)).trans
      ((Equiv.prodSumDistrib E (White k) (Port k)).trans
        (Equiv.sumCongr (Equiv.refl _) (portFiberEquiv rotation))))

def collapseLongDart : ((E × White k) ⊕ ((Medial.Dart E × Fin k) × Bool)) → Vertex E k
  | .inl w => .inl w
  | .inr p => .inr p.1

theorem longDart_vertex (rotation : Equiv.Perm (Medial.Dart E))
    (d : (E × Long k) × Bool) :
    (longGraph rotation k).dartVertex d=collapseLongDart (longDartEquiv rotation k d) := by
  rcases d with ⟨⟨e,f⟩,b⟩
  cases b
  · rfl
  · cases h : longRight f <;>
      simp [longDartEquiv,longGraph,MultiGraph.dartVertex,collapseLongDart,embed,
        longEndpointEquiv,longEndpoint,h,portFiberEquiv]

variable [Fintype E]

/-- White vertices have one long incidence; each paired port has two, also
when the two ports belong to the same original edge occurrence. -/
theorem long_degree (rotation : Equiv.Perm (Medial.Dart E)) (v : Vertex E k) :
    (longGraph rotation k).selectedDegree Finset.univ v=
      match v with | .inl _ => 1 | .inr _ => 2 := by
  rw [selectedDegree_eq_dartCount,Fintype.card_subtype,Finset.card_filter]
  simp only [Finset.mem_univ,true_and]
  rw [Fintype.sum_equiv (longDartEquiv rotation k)
    (fun d => if (longGraph rotation k).dartVertex d=v then 1 else 0)
    (fun d => if collapseLongDart d=v then 1 else 0) (by intro d; dsimp only; rw [longDart_vertex])]
  rw [Fintype.sum_sum_type]
  cases v with
  | inl w => simp [collapseLongDart]
  | inr w =>
    simp only [collapseLongDart,Sum.inl_ne_inr,ite_false,Finset.sum_const_zero,zero_add,Sum.inr.injEq]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [Finset.sum_add_distrib]
    simp

def longEdgeMap (p : E × Long k) : E × RadialPottsTile.Edge k := (p.1,.inl p.2)

def longEdges (E : Type) [Fintype E] (k : ℕ) : Finset (E × RadialPottsTile.Edge k) :=
  @Finset.image (E × Long k) (E × RadialPottsTile.Edge k) (Classical.decEq _) longEdgeMap Finset.univ

theorem longEdgeMap_injective : Function.Injective (@longEdgeMap E k) := by
  intro a b h
  exact Prod.ext (congrArg (fun p : E × RadialPottsTile.Edge k => p.1) h)
    (Sum.inl.inj (congrArg (fun p : E × RadialPottsTile.Edge k => p.2) h))

theorem selectedDegree_longEdges (rotation : Equiv.Perm (Medial.Dart E)) (v : Vertex E k) :
    (graph rotation k).selectedDegree (longEdges E k) v=
      match v with | .inl _ => 1 | .inr _ => 2 := by
  simpa only [longEdges] using (selectedDegree_image (longGraph rotation k) (graph rotation k) longEdgeMap
    (by intro e v; rfl) Finset.univ longEdgeMap_injective.injOn v).trans (long_degree rotation v)

@[simp] theorem longEdges_card : (longEdges E k).card=2*k*(k+1)*Fintype.card E := by
  letI : DecidableEq (E × RadialPottsTile.Edge k) := Classical.decEq _
  rw [longEdges,Finset.card_image_of_injective _ longEdgeMap_injective,Finset.card_univ,card_long]
end PlanarHom.RadialPotts.Assembly
