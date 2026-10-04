import PlanarHom.ListPredicateMachines
import PlanarHom.ListFilterMachines

/-! # Actual stable deduplication under a polynomial-time equivalence test -/
namespace PlanarHom.ListDedupMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines ListFlattenMachines

variable {α : Type}

def Rel (test : α×α→Bool) (a b : α) : Prop := test (a,b)=true

def step (test : α×α→Bool) (acc : List α) (a : α) : List α :=
  if acc.any (fun b => test (a,b)) then acc else acc++[a]

def dedup (test : α×α→Bool) (xs : List α) : List α := xs.foldl (step test) []

theorem acc_sublist_step (test : α×α→Bool) (acc : List α) (a : α) :
    acc.Sublist (step test acc a) := by
  unfold step
  split
  · exact List.Sublist.refl _
  · exact List.sublist_append_left _ _

theorem step_sublist (test : α×α→Bool) (acc : List α) (a : α) :
    (step test acc a).Sublist (acc++[a]) := by
  unfold step
  split
  · exact List.sublist_append_left _ _
  · exact List.Sublist.refl _

/-- Stable order and exact identity of retained values, for any Boolean test. -/
theorem fold_sublist (test : α×α→Bool) (acc xs : List α) :
    (xs.foldl (step test) acc).Sublist (acc++xs) := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    have h := (ih (step test acc a)).trans ((step_sublist test acc a).append_right xs)
    simpa [List.append_assoc] using h

theorem dedup_sublist (test : α×α→Bool) (xs : List α) : (dedup test xs).Sublist xs := by
  simpa [dedup] using fold_sublist test [] xs

/-- Every stored representative survives all subsequent iterations. -/
theorem acc_sublist_fold (test : α×α→Bool) (acc xs : List α) :
    acc.Sublist (xs.foldl (step test) acc) := by
  induction xs generalizing acc with
  | nil => exact List.Sublist.refl _
  | cons a xs ih => exact (acc_sublist_step test acc a).trans (ih (step test acc a))

theorem step_coverage (test : α×α→Bool) (hrefl : Reflexive (Rel test)) (acc : List α) (a : α) :
    ∀ x∈acc++[a], ∃y∈step test acc a, Rel test x y := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact ⟨x,(acc_sublist_step test acc a).subset hx,hrefl x⟩
  · have hx' := List.mem_singleton.mp hx
    subst x
    by_cases h : acc.any (fun b => test (a,b))=true
    · obtain ⟨y,hy,hr⟩ := List.any_eq_true.mp h
      exact ⟨y,(acc_sublist_step test acc a).subset hy,hr⟩
    · exact ⟨a,by simp [step,h],hrefl a⟩

theorem fold_coverage (test : α×α→Bool) (heq : Equivalence (Rel test)) (acc xs : List α) :
    ∀x∈acc++xs,∃y∈xs.foldl (step test) acc,Rel test x y := by
  induction xs generalizing acc with
  | nil => intro x hx; exact ⟨x,by simpa using hx,heq.refl x⟩
  | cons a xs ih =>
    intro x hx
    have hx' : x∈(acc++[a])++xs := by simpa [List.append_assoc] using hx
    rcases List.mem_append.mp hx' with hleft|hright
    · obtain ⟨y,hy,hxy⟩ := step_coverage test heq.refl acc a x hleft
      obtain ⟨z,hz,hyz⟩ := ih (step test acc a) y (List.mem_append_left _ hy)
      exact ⟨z,hz,heq.trans hxy hyz⟩
    · exact ih (step test acc a) x (List.mem_append_right _ hright)

theorem dedup_coverage (test : α×α→Bool) (heq : Equivalence (Rel test)) (xs : List α) :
    ∀x∈xs,∃y∈dedup test xs,Rel test x y := by
  simpa [dedup] using fold_coverage test heq [] xs

theorem step_pairwise (test : α×α→Bool) (hsymm : Symmetric (Rel test))
    (acc : List α) (a : α) (hacc : acc.Pairwise (fun x y => ¬Rel test x y)) :
    (step test acc a).Pairwise (fun x y => ¬Rel test x y) := by
  by_cases h : acc.any (fun b => test (a,b))=true
  · simpa [step,h] using hacc
  · simp only [step,h]
    apply List.pairwise_append.mpr
    refine ⟨hacc,by simp,?_⟩
    intro x hx y hy hr
    have hy' := List.mem_singleton.mp hy
    subst y
    exact h (List.any_eq_true.mpr ⟨x,hx,hsymm hr⟩)

theorem fold_pairwise (test : α×α→Bool) (hsymm : Symmetric (Rel test))
    (acc xs : List α) (hacc : acc.Pairwise (fun x y => ¬Rel test x y)) :
    (xs.foldl (step test) acc).Pairwise (fun x y => ¬Rel test x y) := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons a xs ih => exact ih (step test acc a) (step_pairwise test hsymm acc a hacc)

theorem dedup_pairwise (test : α×α→Bool) (heq : Equivalence (Rel test)) (xs : List α) :
    (dedup test xs).Pairwise (fun x y => ¬Rel test x y) :=
  fold_pairwise test (fun _ _ h => heq.symm h) [] xs (by simp)

theorem payloadSize_sublist (e : BitEncoding α) {xs ys : List α} (h : xs.Sublist ys) :
    payloadSize e xs≤payloadSize e ys := by
  have hn := h.length_le
  have hs := (h.map (fun a => (e.encode a).length)).sum_le_sum (fun _ _ => Nat.zero_le _)
  rw [payloadSize_eq,payloadSize_eq]
  omega

/-- The accumulator contains only retained original input words, so every
prefix has linear canonical bit size. -/
theorem prefix_size_bound (e : BitEncoding α) (test : α×α→Bool) (acc xs : List α) (i : ℕ) :
    (e.list.encode ((xs.take i).foldl (step test) acc)).length≤
      (Polynomial.C 3*Polynomial.X+1).eval ((e.list.prod e.list).encode (acc,xs)).length := by
  have hsub := fold_sublist test acc (xs.take i)
  have hp := payloadSize_sublist e hsub
  rw [payloadSize_append] at hp
  have ht := ListFilterMachines.payloadSize_take_le e xs i
  have ha := payloadSize_le_word e acc
  have hx := payloadSize_le_word e xs
  have hsize : payloadSize e ((xs.take i).foldl (step test) acc)≤
      ((e.list.prod e.list).encode (acc,xs)).length := by
    rw [BitEncoding.prod_length]
    dsimp only
    omega
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one] using
    (word_length_le_payload e _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hsize) 1)

theorem fp_step (e : BitEncoding α) (test : α×α→Bool) (htest : FP (e.prod e) BitEncoding.bool test) :
    FP (e.list.prod e) e.list (fun p => step test p.1 p.2) := by
  have hz := fp_fst e.list e
  have ha := fp_snd e.list e
  have hmem := (ha.pair hz).comp (ListPredicateMachines.fp_member e test htest)
  have hpred : FP (e.list.prod e) BitEncoding.bool
      (fun p => decide (p.1.any (fun b => test (p.2,b))=true)) := hmem.congr (fun p => by simp only [Function.comp_apply,Bool.decide_coe])
  have hsingle := (ha.pair (fp_const (e.list.prod e) e.list [])).comp (ListMutationMachines.fp_cons e)
  have hadd := (hz.pair hsingle).comp (ListMutationMachines.fp_append e)
  exact hpred.ite hz hadd

/-- Generic polynomial-time stable dedup, with no equivalence hypothesis needed
for the machine. Logical equivalence is used only by its semantic invariants. -/
theorem fp_dedup (e : BitEncoding α) (test : α×α→Bool) (htest : FP (e.prod e) BitEncoding.bool test) :
    FP e.list e.list (dedup test) := by
  have hf := ListFoldMachines.fp_foldl e e.list (step test) (fp_step e test htest)
    (Polynomial.C 3*Polynomial.X+1) (fun acc xs i _ => prefix_size_bound e test acc xs i)
  exact ((fp_const e.list e.list []).pair (fp_id e.list)).comp hf

/-- In particular the earliest representative of each class is kept, not merely
an arbitrary equal replacement. This assertion needs no equivalence assumption. -/
theorem first_representative_mem (test : α×α→Bool) (before : List α) (a : α) (after : List α)
    (hfirst : ∀b∈before,¬Rel test a b) : a∈dedup test (before++a::after) := by
  have hn : ¬(dedup test before).any (fun b => test (a,b))=true := by
    intro h
    obtain ⟨b,hb,hr⟩ := List.any_eq_true.mp h
    exact hfirst b ((dedup_sublist test before).subset hb) hr
  have hstep : step test (dedup test before) a=dedup test before++[a] := by simp [step,hn]
  have ha : a∈step test (dedup test before) a := by rw [hstep]; simp
  have hretain := (acc_sublist_fold test (step test (dedup test before) a) after).subset ha
  simpa only [dedup,List.foldl_append,List.foldl_cons] using hretain

/-- A ready-to-use first-coordinate key comparison; retained second coordinates
are the original data, rather than values recomputed through any map. -/
def dedupByFirst {K T : Type} (test : K×K→Bool) : List (K×T)→List (K×T) :=
  dedup (fun p => test (p.1.1,p.2.1))

theorem fp_dedupByFirst {K T : Type} (ek : BitEncoding K) (et : BitEncoding T)
    (test : K×K→Bool) (htest : FP (ek.prod ek) BitEncoding.bool test) :
    FP (ek.prod et).list (ek.prod et).list (dedupByFirst (T:=T) test) := by
  have hl := (fp_fst (ek.prod et) (ek.prod et)).comp (fp_fst ek et)
  have hr := (fp_snd (ek.prod et) (ek.prod et)).comp (fp_fst ek et)
  exact fp_dedup (ek.prod et) (fun p => test (p.1.1,p.2.1)) ((hl.pair hr).comp htest)

theorem dedupByFirst_sublist {K T : Type} (test : K×K→Bool) (xs : List (K×T)) :
    (dedupByFirst test xs).Sublist xs := dedup_sublist _ _

theorem firstRelation_equivalence {K T : Type} (test : K×K→Bool) (heq : Equivalence (Rel test)) :
    Equivalence (Rel (fun p : (K×T)×(K×T) => test (p.1.1,p.2.1))) :=
  ⟨fun p => heq.refl p.1,fun h => heq.symm h,fun h₁ h₂ => heq.trans h₁ h₂⟩

theorem dedupByFirst_coverage {K T : Type} (test : K×K→Bool) (heq : Equivalence (Rel test)) (xs : List (K×T)) :
    ∀x∈xs,∃y∈dedupByFirst test xs,Rel test x.1 y.1 :=
  dedup_coverage _ (firstRelation_equivalence test heq) xs

theorem dedupByFirst_pairwise {K T : Type} (test : K×K→Bool) (heq : Equivalence (Rel test)) (xs : List (K×T)) :
    (dedupByFirst test xs).Pairwise (fun x y => ¬Rel test x.1 y.1) :=
  dedup_pairwise _ (firstRelation_equivalence test heq) xs

end PlanarHom.ListDedupMachines
