import PlanarHom.ProductRepresentativeMachines

/-! The actual computed representative table supplies distinct nonzero nodes
and exact target representatives for the interpolation correctness theorem. -/
namespace PlanarHom.ExponentProductTables
open PlanarHom.Complexity
open scoped BigOperators

/-- Vector casting retains precisely the original weak exponent-list table. -/
theorem vectors_lists (t m : ℕ) : (vectors t m).map List.ofFn=ExponentVectors.weak t m:=by
  apply BitEncoding.nat.list.list.injective
  have h:=vectors_encoding t m
  simpa only [BitEncoding.list,BitEncoding.vector,List.length_map,List.map_map,Function.comp_def] using h

private theorem value_ofFn {K : Type} [Field K] {t : ℕ} (A : Fin t→K) (r : Fin t→ℕ) :
    ExponentProductSemantics.value A (List.ofFn r)=∏i,A i^(r i):=by
  apply Finset.prod_congr rfl
  intro i _
  rw [List.getD_eq_getElem (List.ofFn r) 0 (by simp [i.isLt]),List.getElem_ofFn]

variable {K : Type} [Field K] [DecidableEq K] {t : ℕ}

omit [DecidableEq K] in
theorem products_list_form (A B : Fin t→K) (m : ℕ) :
    products A B m=(ExponentVectors.weak t m).map
      (fun xs=>(ExponentProductSemantics.value A xs,ExponentProductSemantics.value B xs)):=by
  rw [←vectors_lists t m,List.map_map]
  simp only [products,Function.comp_def,value_ofFn]

omit [DecidableEq K] in
theorem targets_consistent (A B : Fin t→K) (h : ProductCompatibility.Compatible A B)
    (m : ℕ) (p q : K × K) (hp : p∈products A B m) (hq : q∈products A B m)
    (hz : p.1≠0) (he : p.1=q.1) : p.2=q.2:=by
  rw [products_list_form] at hp hq
  obtain ⟨xs,hxs,rfl⟩:=List.mem_map.mp hp
  obtain ⟨ys,hys,rfl⟩:=List.mem_map.mp hq
  exact ExponentProductSemantics.target_eq_of_weak_collision A B h xs ys hxs hys hz he

def sourceNode (A B : Fin t→K) (m : ℕ) (i : Fin (representatives A B m).length) : K:=
  ((representatives A B m).get i).1

def targetNode (A B : Fin t→K) (m : ℕ) (i : Fin (representatives A B m).length) : K:=
  ((representatives A B m).get i).2

theorem sourceNode_nonzero (A B : Fin t→K) (m : ℕ) (i : Fin (representatives A B m).length) :
    sourceNode A B m i≠0:=representatives_nonzero A B m _ (List.get_mem _ i)

theorem sourceNode_injective (A B : Fin t→K) (m : ℕ) : Function.Injective (sourceNode A B m):=by
  intro i j hij
  have hpair:=List.pairwise_iff_get.mp (representatives_pairwise A B m)
  by_contra hne
  have hneval : i.val≠j.val:=fun h=>hne (Fin.ext h)
  rcases lt_or_gt_of_ne hneval with hlt | hgt
  · exact hpair i j hlt hij
  · exact hpair j i hgt hij.symm

/-- Every nonzero source exponent product finds an actual retained table row,
with the matching target product forced by the source collision hypothesis. -/
theorem exists_node_for_weak (A B : Fin t→K) (h : ProductCompatibility.Compatible A B)
    {m : ℕ} (xs : List ℕ) (hxs : xs∈ExponentVectors.weak t m)
    (hz : ExponentProductSemantics.value A xs≠0) :
    ∃i : Fin (representatives A B m).length,
      sourceNode A B m i=ExponentProductSemantics.value A xs ∧
      targetNode A B m i=ExponentProductSemantics.value B xs:=by
  let p:K × K:=(ExponentProductSemantics.value A xs,ExponentProductSemantics.value B xs)
  have hp:p∈products A B m:=by rw [products_list_form]; exact List.mem_map.mpr ⟨xs,hxs,rfl⟩
  obtain ⟨q,hq,he⟩:=representatives_coverage A B m p hp hz
  have ht:p.2=q.2:=targets_consistent A B h m p q hp ((representatives_sublist A B m).subset hq) hz he
  obtain ⟨i,hi⟩:=List.get_of_mem hq
  refine ⟨i,?_,?_⟩
  · change ((representatives A B m).get i).1=ExponentProductSemantics.value A xs
    rw [hi]
    exact he.symm
  · change ((representatives A B m).get i).2=ExponentProductSemantics.value B xs
    rw [hi]
    exact ht.symm

end PlanarHom.ExponentProductTables
