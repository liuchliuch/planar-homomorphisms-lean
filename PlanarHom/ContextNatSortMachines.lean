import PlanarHom.ContextNatSortCorrectness

/-! NEW reconstruction. Context-dependent natural-label sorting is an actual
encoded polynomial-time program. The insertion fold preserves literal payload
by permutation, so its complete live state has a proved linear code bound. -/
namespace PlanarHom.ContextNatSortMachines
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives ListFlattenMachines Polynomial
variable {C : Type}

 def stateStep (cmp : C→ℕ→ℕ→Bool) (s : C×List ℕ) (x : ℕ) : C×List ℕ :=
   (s.1,insert cmp s.1 x s.2)

 theorem fold_stateStep (cmp : C→ℕ→ℕ→Bool) (c : C) (acc xs : List ℕ) :
    xs.foldl (stateStep cmp) (c,acc)=(c,xs.foldl (fun acc x=>insert cmp c x acc) acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons,stateStep] using ih (insert cmp c x acc)

 theorem payload_perm {A : Type} (ea : BitEncoding A) {xs ys : List A} (h : xs.Perm ys) :
    payloadSize ea xs=payloadSize ea ys := by
  simp only [payloadSize_eq]
  rw [(h.map (fun a=>(ea.encode a).length)).sum_eq,h.length_eq]

 theorem prefix_size_bound (ec : BitEncoding C) (cmp : C→ℕ→ℕ→Bool)
    (s : C×List ℕ) (xs : List ℕ) (i : ℕ) :
    ((ec.prod BitEncoding.nat.list).encode ((xs.take i).foldl (stateStep cmp) s)).length ≤
      (Polynomial.C 10*X+Polynomial.C 2).eval (((ec.prod BitEncoding.nat.list).prod BitEncoding.nat.list).encode (s,xs)).length := by
  rcases s with ⟨c,acc⟩
  let N:=(((ec.prod BitEncoding.nat.list).prod BitEncoding.nat.list).encode ((c,acc),xs)).length
  have hN : N=2*(2*(ec.encode c).length+(BitEncoding.nat.list.encode acc).length+1)+
      (BitEncoding.nat.list.encode xs).length+1 := by simp [N,BitEncoding.prod_length]
  have hacc:=payloadSize_le_word BitEncoding.nat acc
  have hxs:=payloadSize_le_word BitEncoding.nat xs
  have htake:=ListFilterMachines.payloadSize_take_le BitEncoding.nat xs i
  have hp:=payload_perm BitEncoding.nat (fold_perm cmp c (xs.take i) acc)
  have hrev : payloadSize BitEncoding.nat (xs.take i).reverse=payloadSize BitEncoding.nat (xs.take i) :=
    payload_perm _ (List.reverse_perm _)
  rw [payloadSize_append,hrev] at hp
  have hw:=word_length_le_payload BitEncoding.nat ((xs.take i).foldl (fun acc x=>insert cmp c x acc) acc)
  rw [hp] at hw
  rw [fold_stateStep,BitEncoding.prod_length]
  simp only [eval_add,eval_mul,eval_C,eval_X]
  change 2*(ec.encode c).length+_+1 ≤ 10*N+2
  omega

 theorem fp_stateStep (ec : BitEncoding C) (cmp : C→ℕ→ℕ→Bool)
    (hcmp : FP (ec.prod (BitEncoding.nat.prod BitEncoding.nat)) BitEncoding.bool
      (fun p=>cmp p.1 p.2.1 p.2.2)) :
    FP ((ec.prod BitEncoding.nat.list).prod BitEncoding.nat) (ec.prod BitEncoding.nat.list)
      (fun p=>stateStep cmp p.1 p.2) := by
  let ectx:=ec.prod BitEncoding.nat
  let ei:=(ec.prod BitEncoding.nat.list).prod BitEncoding.nat
  have hc₀:=fp_fst ectx BitEncoding.nat
  have hy:=fp_snd ectx BitEncoding.nat
  have hc:=hc₀.comp (fp_fst ec BitEncoding.nat)
  have hx:=hc₀.comp (fp_snd ec BitEncoding.nat)
  have hp:=(hc.pair (hx.pair hy)).comp hcmp
  have hn:=hp.comp (fp_bool_unary BitEncoding.bool Bool.not)
  have hs:=fp_fst (ec.prod BitEncoding.nat.list) BitEncoding.nat
  have hitem:=fp_snd (ec.prod BitEncoding.nat.list) BitEncoding.nat
  have hcontext:=hs.comp (fp_fst ec BitEncoding.nat.list)
  have hlist:=hs.comp (fp_snd ec BitEncoding.nat.list)
  have hinput:=(hcontext.pair hitem).pair hlist
  have hl:=hinput.comp (ListContextFilterMachines.fp_filterWithContext ectx BitEncoding.nat _ hn)
  have hr:=hinput.comp (ListContextFilterMachines.fp_filterWithContext ectx BitEncoding.nat _ hp)
  have hcons:=(hitem.pair hr).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  have hnew:=(hl.pair hcons).comp (ListMutationMachines.fp_append BitEncoding.nat)
  exact hcontext.pair hnew

 theorem fp_sort (ec : BitEncoding C) (cmp : C→ℕ→ℕ→Bool)
    (hcmp : FP (ec.prod (BitEncoding.nat.prod BitEncoding.nat)) BitEncoding.bool
      (fun p=>cmp p.1 p.2.1 p.2.2)) :
    FP (ec.prod BitEncoding.nat.list) BitEncoding.nat.list (fun p=>sort cmp p.1 p.2) := by
  have hfold:=ListFoldMachines.fp_foldl BitEncoding.nat (ec.prod BitEncoding.nat.list)
    (stateStep cmp) (fp_stateStep ec cmp hcmp) (Polynomial.C 10*X+Polynomial.C 2)
    (fun s xs i hi=>prefix_size_bound ec cmp s xs i)
  have hc:=fp_fst ec BitEncoding.nat.list
  have hx:=fp_snd ec BitEncoding.nat.list
  have hinit:=(hc.pair (fp_const (ec.prod BitEncoding.nat.list) BitEncoding.nat.list [])).pair hx
  exact ((hinit.comp hfold).comp (fp_snd ec BitEncoding.nat.list)).congr
    (fun p=>by simp only [Function.comp_apply,fold_stateStep,sort])

/-- The output is exactly the requested mergeSort under the actual comparator,
not merely some permutation. Comparator semantics are proved separately; all
costs here come from the supplied concrete FP comparator and list machines. -/
 theorem fp_mergeSort (ec : BitEncoding C) (cmp : C→ℕ→ℕ→Bool)
    (hcmp : FP (ec.prod (BitEncoding.nat.prod BitEncoding.nat)) BitEncoding.bool
      (fun p=>cmp p.1 p.2.1 p.2.2))
    (ht : ∀c a b,(cmp c a b || cmp c b a)=true)
    (htrans : ∀c a b d,cmp c a b=true→cmp c b d=true→cmp c a d=true)
    (hanti : ∀c a b,cmp c a b=true→cmp c b a=true→a=b) :
    FP (ec.prod BitEncoding.nat.list) BitEncoding.nat.list (fun p=>p.2.mergeSort (cmp p.1)) :=
  (fp_sort ec cmp hcmp).congr (fun p=>sort_eq_mergeSort cmp p.1 (ht p.1) (htrans p.1) (hanti p.1) p.2)

end PlanarHom.ContextNatSortMachines
