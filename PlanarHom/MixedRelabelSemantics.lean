import PlanarHom.MixedRelabelMachines

/-! Exact semantic and ordinary-planarity preservation for fixed label aliases. -/
namespace PlanarHom.FiniteLabelLookupMachines

private theorem lookup_unique (table : List (ℕ × ℕ)) (n y : ℕ) (hm : (n,y)∈table)
    (hu : ∀p∈table,p.1=n→p.2=y) : lookup table n=y:=by
  induction table with
  | nil=>simp at hm
  | cons p table ih=>
    by_cases hp:n=p.1
    · simpa [lookup,hp] using hu p (by simp) hp.symm
    · rw [lookup,if_neg hp]
      have ht:(n,y)∈table:=by
        rcases List.mem_cons.mp hm with he | h
        · have hh:=congrArg Prod.fst he; exact False.elim (hp hh)
        · exact h
      exact ih ht (fun q hq=>hu q (List.mem_cons_of_mem _ hq))

/-- A complete fixed finite relabeling table, including any reserved domain labels. -/
def finTable {a b : ℕ} (ρ : Fin a→Fin b) : List (ℕ × ℕ):=
  List.ofFn (fun i : Fin a=>(i.val,(ρ i).val))

theorem lookup_finTable {a b : ℕ} (ρ : Fin a→Fin b) (i : Fin a) :
    lookup (finTable ρ) i.val=(ρ i).val:=by
  apply lookup_unique
  · exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · intro p hp he
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hp
    have hij:j=i:=Fin.ext he
    subst j
    rfl

theorem lookup_finTable_lt {a b : ℕ} (ρ : Fin a→Fin b) (i : ℕ) (hi : i<a) :
    lookup (finTable ρ) i<b:=by
  rw [lookup_finTable ρ ⟨i,hi⟩]
  exact (ρ ⟨i,hi⟩).isLt

end PlanarHom.FiniteLabelLookupMachines

namespace PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLabelLookupMachines
open scoped BigOperators

/-- Relabeling changes no occurrence endpoints and preserves ordinary planarity. -/
theorem relabelBinary_planar (table : List (ℕ × ℕ)) {g : MixedCode} {a b u : ℕ}
    (hg : g.PlanarValid a u) (hlabels : ∀i,i<a→lookup table i<b) :
    (g.relabelBinary table).PlanarValid b u:=
  ⟨relabelBinary_valid table hg.1 hlabels,by simpa only [relabelBinary_underlying] using hg.2⟩

theorem relabelUnary_planar (table : List (ℕ × ℕ)) {g : MixedCode} {b a u : ℕ}
    (hg : g.PlanarValid b a) (hlabels : ∀i,i<a→lookup table i<u) :
    (g.relabelUnary table).PlanarValid b u:=
  ⟨relabelUnary_valid table hg.1 hlabels,by simpa only [relabelUnary_underlying] using hg.2⟩

noncomputable section
variable {C R : Type} [Fintype C] [CommSemiring R]

theorem evaluate_relabelBinary {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (ρ : Fin a→Fin b) (M : Fin b→Matrix C C R) (U : Fin u→C→R) (w : C→R) :
    (g.relabelBinary (finTable ρ)).evaluate (relabelBinary_valid _ hg (lookup_finTable_lt ρ)) M U w=
      g.evaluate hg (M ∘ ρ) U w:=by
  unfold evaluate relabelBinary
  apply Finset.sum_congr rfl
  intro σ _
  have hprod : ((g.edges.map (fun e=>(e.1,e.2.1,lookup (finTable ρ) e.2.2))).map
      (binaryValue g.vertices b M σ)).prod=
      (g.edges.map (binaryValue g.vertices a (M ∘ ρ) σ)).prod:=by
    rw [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro e he
    have hv:=hg.1 e he
    have hl : lookup (finTable ρ) e.2.2=(ρ ⟨e.2.2,hv.2.2⟩).val:=lookup_finTable ρ ⟨e.2.2,hv.2.2⟩
    have ht : e.1<g.vertices ∧ e.2.1<g.vertices ∧ lookup (finTable ρ) e.2.2<b:=
      ⟨hv.1,hv.2.1,lookup_finTable_lt ρ _ hv.2.2⟩
    change binaryValue g.vertices b M σ (e.1,e.2.1,lookup (finTable ρ) e.2.2)=
      binaryValue g.vertices a (M ∘ ρ) σ e
    rw [binaryValue,dif_pos ht,binaryValue,dif_pos hv]
    simp only [hl,Function.comp_apply]
  rw [hprod]

theorem evaluate_relabelUnary {b a u : ℕ} (g : MixedCode) (hg : g.Valid b a)
    (ρ : Fin a→Fin u) (M : Fin b→Matrix C C R) (U : Fin u→C→R) (w : C→R) :
    (g.relabelUnary (finTable ρ)).evaluate (relabelUnary_valid _ hg (lookup_finTable_lt ρ)) M U w=
      g.evaluate hg M (U ∘ ρ) w:=by
  unfold evaluate relabelUnary
  apply Finset.sum_congr rfl
  intro σ _
  have hprod : ((g.unaries.map (fun e=>(e.1,lookup (finTable ρ) e.2))).map
      (unaryValue g.vertices u U σ)).prod=
      (g.unaries.map (unaryValue g.vertices a (U ∘ ρ) σ)).prod:=by
    rw [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro e he
    have hv:=hg.2 e he
    have hl : lookup (finTable ρ) e.2=(ρ ⟨e.2,hv.2⟩).val:=lookup_finTable ρ ⟨e.2,hv.2⟩
    have ht : e.1<g.vertices ∧ lookup (finTable ρ) e.2<u:=⟨hv.1,lookup_finTable_lt ρ _ hv.2⟩
    change unaryValue g.vertices u U σ (e.1,lookup (finTable ρ) e.2)=
      unaryValue g.vertices a (U ∘ ρ) σ e
    rw [unaryValue,dif_pos ht,unaryValue,dif_pos hv]
    simp only [hl,Function.comp_apply]
  rw [hprod]

end
end PlanarHom.Complexity.MixedCode
