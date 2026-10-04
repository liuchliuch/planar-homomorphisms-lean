import PlanarHom.PlanarityDepthFirstSearchWordBounds

/-! NEW reconstruction. One explicit polynomial in actual ordinary graph-code
bits bounds the entire materialized DFS state at every executed iteration. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity Polynomial

noncomputable def clockPolynomial : Polynomial ℕ := (X+1)*(C 2*X+C 3)
noncomputable def listPolynomial (count item : Polynomial ℕ) : Polynomial ℕ := C 3*(C 2*count*item+count)+1
noncomputable def pathPolynomial : Polynomial ℕ := listPolynomial X X
noncomputable def taskPolynomial : Polynomial ℕ := C 4*X+pathPolynomial+C 5
noncomputable def discoveryPolynomial : Polynomial ℕ := C 4*X+pathPolynomial+C 2
noncomputable def workCountPolynomial : Polynomial ℕ := X+clockPolynomial*(C 2*X+1)
noncomputable def statePolynomial : Polynomial ℕ :=
  C 2*listPolynomial workCountPolynomial taskPolynomial + C 2*pathPolynomial +
  C 2*listPolynomial X discoveryPolynomial + listPolynomial clockPolynomial X + C 3

 theorem fuel_le_clock (g : MixedCode) : fuel g ≤ clockPolynomial.eval (inputLength g) := by
  have hn:=vertices_le_input g
  have hm:=edges_le_input g
  simp only [fuel,clockPolynomial,eval_add,eval_mul,eval_C,eval_X,eval_one]
  exact Nat.mul_le_mul (by omega) (by omega)

 theorem list_encoding_polynomial {A : Type} (e : BitEncoding A) (xs : List A)
    (a b : Polynomial ℕ) (N : ℕ) (hn : xs.length≤a.eval N)
    (hb : ∀x∈xs,(e.encode x).length≤b.eval N) :
    (e.list.encode xs).length≤(listPolynomial a b).eval N := by
  simpa only [listPolynomial,eval_add,eval_mul,eval_C,eval_one] using
    PfaffianList.list_encoding_bound e xs _ _ hn hb

 theorem goodPath_word (g : MixedCode) {path : List ℕ} (h : GoodPath g path) :
    (BitEncoding.nat.list.encode path).length≤pathPolynomial.eval (inputLength g) := by
  exact list_encoding_polynomial BitEncoding.nat path X X (inputLength g)
    (by simpa only [eval_X] using (goodPath_length g h).trans (vertices_le_input g))
    (fun v hv=>by simpa only [eval_X] using small_of_le_vertices g (h.2 v hv).le)

 theorem task_word (g : MixedCode) (t : Task) (hs : SmallNat g t.vertex ∧ SmallNat g t.edge)
    (hp : GoodPath g t.path) : (taskCode.encode t).length≤taskPolynomial.eval (inputLength g) := by
  have hh:=goodPath_word g hp
  rcases hs with ⟨hv,he⟩
  unfold SmallNat at hv he
  simp only [taskCode,taskPartsCode,BitEncoding.retract,taskParts,BitEncoding.prod_length,
    BitEncoding.bool,List.length_singleton,taskPolynomial,eval_add,eval_mul,eval_C,eval_X]
  omega

 theorem discovery_word (g : MixedCode) (r : Discovery)
    (hs : SmallNat g r.vertex ∧ SmallNat g r.treeEdge) (hp : GoodPath g r.ancestors) :
    (discoveryCode.encode r).length≤discoveryPolynomial.eval (inputLength g) := by
  have hh:=goodPath_word g hp
  rcases hs with ⟨hv,he⟩
  unfold SmallNat at hv he
  simp only [discoveryCode,discoveryPartsCode,BitEncoding.retract,discoveryParts,BitEncoding.prod_length,
    discoveryPolynomial,eval_add,eval_mul,eval_C,eval_X]
  omega

 theorem iterate_state_word (g : MixedCode) (t : ℕ) (ht : t≤fuel g) :
    (stateCode.encode ((step g)^[t] (initial g))).length≤statePolynomial.eval (inputLength g) := by
  let N:=inputLength g
  let s:=(step g)^[t] (initial g)
  have hstack:=stackInvariant_iterate g t
  have hsource:=sourceInvariant_iterate g t
  have hsmall:=smallFields_iterate g t
  have htq : t≤clockPolynomial.eval N := ht.trans (fuel_le_clock g)
  have hn : g.vertices≤N := vertices_le_input g
  have hm : g.edges.length≤N := edges_le_input g
  have hworklen : s.work.length≤workCountPolynomial.eval N := by
    have hh:=iterate_work_length g t
    apply hh.trans
    simp only [workCountPolynomial,eval_add,eval_mul,eval_C,eval_X,eval_one]
    exact Nat.add_le_add hn (Nat.mul_le_mul htq (by omega))
  have hw := list_encoding_polynomial taskCode s.work workCountPolynomial taskPolynomial N hworklen
    (fun task htask=>task_word g task (hsmall.work task htask) (hsource.work_path task htask))
  have hactive : GoodPath g s.active :=
    ⟨hstack.active_nodup,fun v hv=>hstack.goodSeen.2 v (hstack.active_seen v hv)⟩
  have ha:=goodPath_word g hactive
  have hd := list_encoding_polynomial discoveryCode s.discovered X discoveryPolynomial N
    (by simpa only [eval_X] using (goodSeen_length g s hstack.goodSeen).trans hn)
    (fun r hr=>discovery_word g r (hsmall.discovered r hr) (hsource.record_path r hr))
  have hf := list_encoding_polynomial BitEncoding.nat s.finished clockPolynomial X N
    ((iterate_finished_length g t).trans htq) (fun x hx=>by simpa only [eval_X] using hsmall.finished x hx)
  change (stateCode.encode s).length≤statePolynomial.eval N
  simp only [stateCode,statePartsCode,BitEncoding.retract,stateParts,BitEncoding.prod_length,
    statePolynomial,eval_add,eval_mul,eval_C]
  change (BitEncoding.nat.list.encode s.active).length≤pathPolynomial.eval N at ha
  omega

end PlanarHom.PlanarityDepthFirstSearch
