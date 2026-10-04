import PlanarHom.PlanarityLRBranchPaths

/-! NEW literal occurrence-dart code for deterministic LR rotations. Loops
retain two distinct darts; parallel occurrences retain separate indices. -/
namespace PlanarHom.PlanarityRotationCode
open Complexity PlanarityLRRawConstraints PlanarityLRDirect

abbrev Dart := ℕ × Bool

def reverse (a : Dart) : Dart := (a.1,!a.2)

def host (g : MixedCode) (a : Dart) : ℕ := if a.2 then (edge g a.1).1 else (edge g a.1).2.1

def outward (g : MixedCode) (e : ℕ) : Dart := (e,decide ((edge g e).1 = source g e))

def allDarts (g : MixedCode) : List Dart :=
  (List.range g.edges.length).map (fun e => (e,true)) ++
    (List.range g.edges.length).map (fun e => (e,false))

def incidentRow (g : MixedCode) (v : ℕ) : List Dart := (allDarts g).filter (fun a => decide (host g a = v))

@[simp] theorem reverse_reverse (a : Dart) : reverse (reverse a) = a := by cases a; simp [reverse]
@[simp] theorem reverse_index (a : Dart) : (reverse a).1 = a.1 := rfl
@[simp] theorem outward_index (g : MixedCode) (e : ℕ) : (outward g e).1 = e := rfl

theorem reverse_ne (a : Dart) : reverse a ≠ a := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [reverse]

theorem source_target_endpoints (g : MixedCode) (e : ℕ) :
    (source g e,target g e) = ((edge g e).1,(edge g e).2.1) ∨
      (source g e,target g e) = ((edge g e).2.1,(edge g e).1) := by
  unfold source target lower upper
  split_ifs <;> simp

theorem outward_endpoints (g : MixedCode) (e : ℕ) :
    host g (outward g e) = source g e ∧ host g (reverse (outward g e)) = target g e := by
  rcases source_target_endpoints g e with h | h
  · have hs := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    simp only [Prod.fst,Prod.snd] at hs ht
    simp [host,outward,reverse,hs,ht]
  · have hs := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    simp only [Prod.fst,Prod.snd] at hs ht
    by_cases hends : (edge g e).1 = (edge g e).2.1
    · simp [host,outward,reverse,hs,ht,hends]
    · simp [host,outward,reverse,hs,ht,hends]

@[simp] theorem host_outward (g : MixedCode) (e : ℕ) : host g (outward g e) = source g e :=
  (outward_endpoints g e).1

@[simp] theorem host_reverse_outward (g : MixedCode) (e : ℕ) : host g (reverse (outward g e)) = target g e :=
  (outward_endpoints g e).2

theorem outward_injective (g : MixedCode) : Function.Injective (outward g) := by
  intro e f h
  exact congrArg Prod.fst h

@[simp] theorem mem_allDarts (g : MixedCode) (a : Dart) : a ∈ allDarts g ↔ a.1 < g.edges.length := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [allDarts]

theorem allDarts_nodup (g : MixedCode) : (allDarts g).Nodup := by
  have hi₁ : Function.Injective (fun e : ℕ => (e,true)) := fun a b h => congrArg Prod.fst h
  have hi₂ : Function.Injective (fun e : ℕ => (e,false)) := fun a b h => congrArg Prod.fst h
  apply List.nodup_append.mpr
  refine ⟨List.nodup_range.map hi₁,List.nodup_range.map hi₂,?_⟩
  simp [List.disjoint_left]

@[simp] theorem allDarts_length (g : MixedCode) : (allDarts g).length = 2*g.edges.length := by
  simp [allDarts,two_mul]

@[simp] theorem mem_incidentRow (g : MixedCode) (v : ℕ) (a : Dart) :
    a ∈ incidentRow g v ↔ a.1 < g.edges.length ∧ host g a = v := by
  simp [incidentRow]

theorem incidentRow_nodup (g : MixedCode) (v : ℕ) : (incidentRow g v).Nodup :=
  (allDarts_nodup g).filter _

theorem host_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) {a : Dart}
    (ha : a.1 < g.edges.length) : host g a < g.vertices := by
  have hv := edge_valid g hg ha
  unfold host
  split_ifs
  · exact hv.1
  · exact hv.2

/-- Each occurrence has exactly its two opposing darts, even when it is a loop. -/
theorem dart_outward_cases (g : MixedCode) (a : Dart) :
    a = outward g a.1 ∨ a = reverse (outward g a.1) := by
  rcases a with ⟨e,b⟩
  unfold outward reverse
  cases b <;> by_cases h : (edge g e).1 = source g e <;> simp [h]

end PlanarHom.PlanarityRotationCode
