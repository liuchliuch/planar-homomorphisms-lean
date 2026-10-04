import PlanarHom.BooleanQuadraticLookup

/-! NEW finite support restriction and exact stored pivot coefficient identity. -/
namespace PlanarHom.BooleanQuadratic
open scoped BigOperators

 theorem fin_beq_val {n:ℕ} (i j:Fin n) : (i.val==j.val)=decide (i=j) := by
  apply Bool.eq_iff_iff.mpr
  simp [Fin.ext_iff]

 theorem form_congr_on {V : Type*} (s : Finset V) (c : F₂) (l : V→F₂) (a : V→V→F₂)
    (x y : V→F₂) (h : ∀i∈s,x i=y i) : form s c l a x=form s c l a y := by
  unfold form
  congr 1
  · congr 1
    exact Finset.sum_congr rfl (fun i hi=>by rw [h i hi])
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [h i hi,h j hj]

 theorem affine_congr_on {V : Type*} (s : Finset V) (c : F₂) (l : V→F₂)
    (x y : V→F₂) (h : ∀i∈s,x i=y i) : affine s c l x=affine s c l y := by
  unfold affine
  congr 1
  exact Finset.sum_congr rfl (fun i hi=>by rw [h i hi])

 theorem form_mask {V : Type*} (s : Finset V) (p : V→Prop) [DecidablePred p]
    (c : F₂) (l : V→F₂) (a : V→V→F₂) (x : V→F₂) :
    form s c (fun i=>if p i then l i else 0)
      (fun i j=>if p i ∧ p j then a i j else 0) x = form (s.filter p) c l a x := by
  unfold form
  congr 1
  · congr 1
    simp [Finset.sum_filter,ite_mul]
  · simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp:p i
    · simp [hp,ite_mul]
    · simp [hp]

 theorem erase_pair_eq_filter {V : Type*} [DecidableEq V] (s : Finset V) (i j : V) :
    (s.erase i).erase j=s.filter (fun k=>k≠i ∧ k≠j) := by
  ext k
  simp [and_left_comm,and_assoc,and_comm]

 theorem phase_pivot {n : ℕ} (q : Data) (hn : dimension q=n) (i j : Fin n) (x : Fin n→F₂) :
    phase n (pivot q i.val j.val) x =
      form ((Finset.univ.erase i).erase j)
        (bit q.1+bit (linear q i.val)*bit (linear q j.val))
        (fun k=>bit (rawLinear q k.val)+bit (linear q i.val)*bit (cross q j.val k.val)+
          bit (linear q j.val)*bit (cross q i.val k.val))
        (fun k l=>bit (entry q k.val l.val)+bit (cross q i.val k.val)*bit (cross q j.val l.val)) x := by
  have hlin : (fun k:Fin n=>bit (rawLinear (pivot q i.val j.val) k.val)) =
      (fun k=>if k≠i ∧ k≠j then bit (rawLinear q k.val)+
        bit (linear q i.val)*bit (cross q j.val k.val)+
        bit (linear q j.val)*bit (cross q i.val k.val) else 0) := by
    funext k
    by_cases hi:k=i <;> by_cases hj:k=j <;>
      simp [rawLinear_pivot,hn,k.isLt,keep,hi,hj,fin_beq_val,bit_xor,bit_and,add_assoc]
  have hmat : (fun k l:Fin n=>bit (entry (pivot q i.val j.val) k.val l.val)) =
      (fun k l=>if (k≠i ∧ k≠j) ∧ (l≠i ∧ l≠j) then
        bit (entry q k.val l.val)+bit (cross q i.val k.val)*bit (cross q j.val l.val) else 0) := by
    funext k l
    by_cases hki:k=i <;> by_cases hkj:k=j <;> by_cases hli:l=i <;> by_cases hlj:l=j <;>
      simp [entry_pivot,hn,k.isLt,l.isLt,keep,hki,hkj,hli,hlj,fin_beq_val]
  unfold phase
  rw [hlin,hmat,form_mask,←erase_pair_eq_filter]
  simp [pivot,bit_xor,bit_and]

 theorem phase_remove {n : ℕ} (q : Data) (hn : dimension q=n) (i : Fin n) (x : Fin n→F₂) :
    phase n (remove q i.val) x = form (Finset.univ.erase i) (bit q.1)
      (fun k=>bit (rawLinear q k.val)) (fun k l=>bit (entry q k.val l.val)) x := by
  have hlin : (fun k:Fin n=>bit (rawLinear (remove q i.val) k.val)) =
      (fun k=>if k≠i then bit (rawLinear q k.val) else 0) := by
    funext k
    by_cases hi:k=i <;> simp [rawLinear_remove,hn,k.isLt,fin_beq_val,hi]
  have hmat : (fun k l:Fin n=>bit (entry (remove q i.val) k.val l.val)) =
      (fun k l=>if k≠i ∧ l≠i then bit (entry q k.val l.val) else 0) := by
    funext k l
    by_cases hk:k=i <;> by_cases hl:l=i <;>
      simp [entry_remove,hn,k.isLt,l.isLt,fin_beq_val,hk,hl]
  unfold phase
  rw [hlin,hmat,form_mask]
  have hf : Finset.univ.filter (fun k:Fin n=>k≠i)=Finset.univ.erase i := by
    ext k; simp
  rw [hf]
  rfl

 def extendPair {V : Type*} [DecidableEq V] (i j : V)
    (z : {k:V // k≠i ∧ k≠j}→F₂) (k : V) : F₂ :=
  if h:k≠i ∧ k≠j then z ⟨k,h⟩ else 0

 theorem extendPair_restrict {V : Type*} [DecidableEq V] (s : Finset V) (i j : V)
    (x : V→F₂) (k : V) (hk:k∈(s.erase i).erase j) :
    extendPair i j (fun k=>x k.val) k=x k := by
  have h:k≠i ∧ k≠j := by simpa only [Finset.mem_erase,and_assoc] using
    (show k≠i ∧ k≠j from ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1,(Finset.mem_erase.mp hk).1⟩)
  simp [extendPair,h]

 def extendSingle {V : Type*} [DecidableEq V] (i : V)
    (z : {k:V // k≠i}→F₂) (k : V) : F₂ := if h:k≠i then z ⟨k,h⟩ else 0

 theorem extendSingle_restrict {V : Type*} [DecidableEq V] (s : Finset V) (i : V)
    (x : V→F₂) (k : V) (hk:k∈s.erase i) :
    extendSingle i (fun k=>x k.val) k=x k := by
  simp [extendSingle,(Finset.mem_erase.mp hk).1]

end PlanarHom.BooleanQuadratic
