import PlanarHom.MaterializedRailCopy
import PlanarHom.PositiveFormulaRailRouting

/-! A materialized three-port clause termination after passive original wires. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree CountingCookLevin ParsimoniousBlockTemplate

def getRef (rs : List ℕ) (i : ℕ) : ℕ := rs[i]?.getD 0

theorem getRef_mem (rs : List ℕ) (i : ℕ) (hi : i<rs.length) : getRef rs i∈rs := by
  simpa [getRef,List.getElem?_eq_getElem hi] using List.getElem_mem hi

theorem read_getRef (rs : List ℕ) (xs : List Bool) (i : ℕ) (hi : i<rs.length) :
    readBit xs (getRef rs i)=readBit (rs.map (readBit xs)) i := by
  simp [getRef,readBit,List.getElem?_eq_getElem hi,List.getElem?_map]

@[simp] theorem step_test (xs : List Bool) (a b c : ℕ) : step xs (test a b c)=xs := by
  simp [step,test,Kind.template,termination,Template.auxiliary]

@[simp] theorem accepts_test (xs : List Bool) (a b c : ℕ) :
    Accepts [test a b c] xs ↔ ExactlyOne (readBit xs a) (readBit xs b) (readBit xs c) := by
  simp [Accepts,test,refs,Kind.template,termination]

def checkLayer (n m : ℕ) (rs : List ℕ) : LayerResult :=
  ⟨m+6*(rs.take n).length,wireRails m (rs.take n),
    wireProgram (rs.take n)++[test (getRef rs n) (getRef rs (n+1)) (getRef rs (n+2))]⟩

theorem checkLayer_wellFormed (n m : ℕ) (rs : List ℕ)
    (hr : ∀x∈rs,x<m) (hlen : rs.length=n+3) : (checkLayer n m rs).WellFormed m := by
  have hp := passive_wellFormed m (rs.take n) (fun x hx => hr x (List.mem_of_mem_take hx))
  have href (i : ℕ) (hi : i<rs.length) : getRef rs i<m+6*(rs.take n).length :=
    (hr _ (getRef_mem rs i hi)).trans_le (by omega)
  refine ⟨(valid_append m _ _).mpr ⟨hp.valid,?_⟩,?_,hp.rails_valid⟩
  · rw [wire_width]
    refine ⟨?_,trivial⟩
    intro i
    change Fin 3 at i
    fin_cases i
    · exact href n (by omega)
    · exact href (n+1) (by omega)
    · exact href (n+2) (by omega)
  · change width m (wireProgram (rs.take n)++[_])=_
    rw [width_append,wire_width]
    rfl

/-- Actual passive output values, including the effect of the final clause op. -/
theorem checkLayer_values (n m : ℕ) (rs : List ℕ) (xs : List Bool)
    (hxs : xs.length=m) (hr : ∀x∈rs,x<m) :
    (checkLayer n m rs).rails.map (readBit (execute (checkLayer n m rs).instructions xs))=
      (rs.map (readBit xs)).take n := by
  subst m
  change (wireRails xs.length (rs.take n)).map
    (readBit (execute (wireProgram (rs.take n)++[_]) xs))=_
  rw [execute_append]
  change (wireRails xs.length (rs.take n)).map (readBit (step (execute (wireProgram (rs.take n)) xs) _))=_
  rw [step_test,wireRails_values _ _ (fun r h => hr r (List.mem_of_mem_take h))]
  exact List.map_take

/-- The clause reads the three copied occurrence rails, never an implicit
logical variable or an unmaterialized edge. -/
theorem checkLayer_accepts (n m : ℕ) (rs : List ℕ) (xs : List Bool)
    (hxs : xs.length=m) (hr : ∀x∈rs,x<m) (hlen : rs.length=n+3) :
    Accepts (checkLayer n m rs).instructions xs ↔
      ExactlyOne (readBit (rs.map (readBit xs)) n) (readBit (rs.map (readBit xs)) (n+1))
        (readBit (rs.map (readBit xs)) (n+2)) := by
  change Accepts (wireProgram (rs.take n)++[_]) xs ↔ _
  rw [accepts_append]
  simp only [wireProgram_accepts,true_and,accepts_test]
  have hread (i : ℕ) (hi : i<rs.length) :
      readBit (execute (wireProgram (rs.take n)) xs) (getRef rs i)=readBit (rs.map (readBit xs)) i := by
    rw [execute_read_old _ _ _ (by rw [hxs]; exact hr _ (getRef_mem rs i hi)),read_getRef rs xs i hi]
  rw [hread n (by omega),hread (n+1) (by omega),hread (n+2) (by omega)]

end PlanarHom.PositiveBlockProgram
