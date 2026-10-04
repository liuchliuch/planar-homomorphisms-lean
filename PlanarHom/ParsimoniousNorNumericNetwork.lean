import PlanarHom.CountingNorProgramHardness

/-! Exact numeric one-in-three networks for all materialized NOR programs.
Out-of-range reads are explicitly replaced by the already fixed false wire. -/
noncomputable section
open Classical
namespace PlanarHom.ParsimoniousNorOneInThree
open CountingCookLevin

def checkedRef (n zero i : ℕ) : ℕ := if i<n then i else zero

def network (n zero : ℕ) : NorGates → Formula ℕ
  | [] => []
  | (x,y)::gs => numericGate n (checkedRef n zero x) (checkedRef n zero y) ++ network (n+4) zero gs

theorem readBit_take (xs : List Bool) (n i : ℕ) (hi : i<n) :
    readBit (xs.take n) i=readBit xs i := by simp [readBit,List.getElem?_take,hi]

theorem readBit_take_out (xs : List Bool) (n i : ℕ) (hi : n≤ i) : readBit (xs.take n) i=false := by
  simp [readBit,List.getElem?_eq_none (show (xs.take n).length≤ i by simp; omega)]

theorem checkedRef_read (xs : List Bool) (n zero i : ℕ) (hz : readBit xs zero=false) :
    readBit xs (checkedRef n zero i)=readBit (xs.take n) i := by
  by_cases hi : i<n
  · simp only [checkedRef,if_pos hi,readBit_take xs n i hi]
  · rw [checkedRef,if_neg hi,hz,readBit_take_out xs n i (by omega)]

theorem satisfies_append {V : Type} (f g : Formula V) (σ : V → Bool) :
    Satisfies (f++g) σ ↔ Satisfies f σ ∧ Satisfies g σ := by
  simp only [Satisfies,List.mem_append,forall_eq_or_imp]
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc),fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨hf,hg⟩ c (hc | hc)
    · exact hf c hc
    · exact hg c hc

/-- Local numeric clauses fix exactly the four fresh values. -/
theorem numericGate_iff (n x y : ℕ) (σ : ℕ → Bool) :
    Satisfies (numericGate n x y) σ ↔
      (fun i : Fin 4 => σ (n+i.val))=extension (σ x) (σ y) := by
  have h := gate_unique (σ x) (σ y) (fun i : Fin 4 => σ (n+i.val))
  simpa only [Satisfies,numericGate,Gate,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,Fin.val_zero,Nat.add_zero] using h

private theorem list_eq_of_read (xs ys : List Bool) (hlen : xs.length=ys.length)
    (h : ∀ i,i<xs.length → readBit xs i=readBit ys i) : xs=ys := by
  apply List.ext_getElem hlen
  intro i hi hj
  have he := h i hi
  simpa only [readBit,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some] using he

/-- The literal numeric gate is equivalent to the exact deterministic list
extension, not just to an existentially related assignment. -/
theorem numericGate_take_iff (xs : List Bool) (n zero x y : ℕ)
    (hn : n+4≤xs.length) (hz : readBit xs zero=false) :
    Satisfies (numericGate n (checkedRef n zero x) (checkedRef n zero y)) (readBit xs) ↔
      xs.take (n+4)=norStep (xs.take n) (x,y) := by
  rw [numericGate_iff,checkedRef_read xs n zero x hz,checkedRef_read xs n zero y hz]
  have htake : (xs.take n).length=n := List.length_take_of_le (by omega)
  constructor
  · intro h
    apply list_eq_of_read
    · simp [norStep,htake,List.length_take_of_le hn]
    · intro i hi
      have hin : i<n+4 := by simpa [List.length_take_of_le hn] using hi
      rw [readBit_take xs (n+4) i hin]
      by_cases hi' : i<n
      · rw [norStep_read_old _ _ _ (by simpa [htake] using hi'),readBit_take xs n i hi']
      · have hik : i-n<4 := by omega
        have he := congrFun h ⟨i-n,hik⟩
        have hii : n+(i-n)=i := by omega
        rw [hii] at he
        rw [he]
        simp only [norStep,readBit,List.getElem?_append_right (show (xs.take n).length≤ i by omega),
          htake,List.getElem?_ofFn,hik,↓reduceDIte,Option.getD_some]
  · intro h
    funext i
    have he := congrArg (fun zs => readBit zs (n+i.val)) h
    dsimp only at he
    rw [readBit_take xs (n+4) (n+i.val) (by omega)] at he
    simpa only [norStep,readBit,List.getElem?_append_right (show (xs.take n).length≤n+i.val by omega),
      htake,Nat.add_sub_cancel_left,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some] using he

/-- All earlier materialized values survive every later gate. -/
theorem runNor_take (gs : NorGates) (xs : List Bool) (n : ℕ) (hn : n≤xs.length) :
    (runNor gs xs).take n=xs.take n := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (runNor gs (norStep xs g)).take n=_
    rw [ih _ (by simp; omega)]
    simp [norStep,List.take_append_of_le_length hn]

/-- Every satisfying auxiliary assignment is the single deterministic NOR
execution on its initial prefix, including invalid-read fallback semantics. -/
theorem network_iff (gs : NorGates) (xs : List Bool) (n zero : ℕ)
    (hn : n+4*gs.length≤xs.length) (hz : readBit xs zero=false) :
    Satisfies (network n zero gs) (readBit xs) ↔
      xs.take (n+4*gs.length)=runNor gs (xs.take n) := by
  induction gs generalizing n with
  | nil => simp [network,Satisfies]
  | cons g gs ih =>
    rcases g with ⟨x,y⟩
    rw [network,satisfies_append,numericGate_take_iff xs n zero x y (by simp at hn; omega) hz,
      ih (n+4) (by simp at hn; omega)]
    have hN : n+4*(gs.length+1)=n+4+4*gs.length := by omega
    simp only [List.length_cons,hN]
    change _ ↔ xs.take (n+4+4*gs.length)=runNor gs (norStep (xs.take n) (x,y))
    constructor
    · rintro ⟨ha,hb⟩
      rwa [ha] at hb
    · intro h
      have he := congrArg (fun zs : List Bool => zs.take (n+4)) h
      have hlen : (norStep (xs.take n) (x,y)).length=n+4 := by
        simp [List.length_take_of_le (show n≤xs.length by simp at hn; omega)]
      dsimp only at he
      rw [List.take_take,Nat.min_eq_left (by omega),runNor_take _ _ _ (by omega)] at he
      have hnt : (norStep (xs.take n) (x,y)).take (n+4)=norStep (xs.take n) (x,y) :=
        List.take_of_length_le (by omega)
      rw [hnt] at he
      exact ⟨he,by rwa [he]⟩

end PlanarHom.ParsimoniousNorOneInThree
