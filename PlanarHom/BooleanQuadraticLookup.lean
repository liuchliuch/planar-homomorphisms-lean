import PlanarHom.BooleanQuadraticProgram
import PlanarHom.BooleanQuadraticCharacters

/-! NEW exact coefficient formulas for the literal dense list updates. -/
namespace PlanarHom.BooleanQuadratic
open scoped BigOperators

def rawLinear (q : Data) (i : ℕ) : Bool := q.2.1[i]?.getD false

theorem rawLinear_pivot (q : Data) (i j k : ℕ) :
    rawLinear (pivot q i j) k = if k<dimension q then
      keep i j k && xor (rawLinear q k)
        (xor (linear q i && cross q j k) (linear q j && cross q i k)) else false := by
  by_cases hk:k<dimension q
  · simp [rawLinear,pivot,List.getElem?_map,List.getElem?_range,hk]
  · simp [rawLinear,pivot,List.getElem?_map,List.getElem?_range,hk]

theorem entry_pivot (q : Data) (i j k l : ℕ) :
    entry (pivot q i j) k l = if k<dimension q ∧ l<dimension q then
      keep i j k && keep i j l &&
        xor (entry q k l) (cross q i k && cross q j l) else false := by
  by_cases hk:k<dimension q <;> by_cases hl:l<dimension q <;>
    simp [entry,pivot,List.getElem?_map,List.getElem?_range,hk,hl]

theorem rawLinear_remove (q : Data) (i k : ℕ) :
    rawLinear (remove q i) k = if k<dimension q then !(k==i) && rawLinear q k else false := by
  by_cases hk:k<dimension q <;>
    simp [rawLinear,remove,List.getElem?_map,List.getElem?_range,hk]

theorem entry_remove (q : Data) (i k l : ℕ) :
    entry (remove q i) k l = if k<dimension q ∧ l<dimension q then
      !(k==i || l==i) && entry q k l else false := by
  by_cases hk:k<dimension q <;> by_cases hl:l<dimension q <;>
    simp [entry,remove,List.getElem?_map,List.getElem?_range,hk,hl]

/-- The semantic polynomial reads precisely the stored Boolean coefficients. -/
def phase (n : ℕ) (q : Data) (x : Fin n→F₂) : F₂ :=
  form Finset.univ (bit q.1) (fun i=>bit (rawLinear q i.val))
    (fun i j=>bit (entry q i.val j.val)) x

def gauss {K : Type*} [CommRing K] (n : ℕ) (q : Data) : K :=
  ∑x:Fin n→F₂,character (phase n q x)

end PlanarHom.BooleanQuadratic
