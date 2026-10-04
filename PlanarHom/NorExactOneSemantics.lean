import PlanarHom.NorExactOneCompiler
import PlanarHom.ParsimoniousBooleanProgram

/-! Explicit accepting-input / satisfying-assignment bijections for the fully
materialized compiler, with every auxiliary variable uniquely determined. -/
noncomputable section
open Classical
namespace PlanarHom.NorExactOne
open Complexity CountingCookLevin ParsimoniousNorOneInThree

theorem list_eq_of_read (xs ys : List Bool) (hlen : xs.length=ys.length)
    (h : ∀ i,i<xs.length → readBit xs i=readBit ys i) : xs=ys := by
  apply List.ext_getElem hlen
  intro i hi hj
  have he := h i hi
  simpa only [readBit,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some] using he

theorem prefix_append_iff (xs ys : List Bool) (n : ℕ) (hn : n+ys.length≤xs.length) :
    xs.take (n+ys.length)=xs.take n++ys ↔
      ∀ i : Fin ys.length,readBit xs (n+i.val)=readBit ys i.val := by
  have htake : (xs.take n).length=n := List.length_take_of_le (by omega)
  constructor
  · intro h i
    have he := congrArg (fun zs => readBit zs (n+i.val)) h
    dsimp only at he
    rw [readBit_take xs (n+ys.length) (n+i.val) (by omega)] at he
    simpa [readBit,htake,List.getElem?_append_right] using he
  · intro h
    apply list_eq_of_read
    · simp [htake,List.length_take_of_le hn]
    · intro i hi
      have hit : i<n+ys.length := by simpa [List.length_take_of_le hn] using hi
      rw [readBit_take xs _ _ hit]
      by_cases hin : i<n
      · simp [readBit,List.getElem?_append_left (show i<(xs.take n).length by omega),
          List.getElem?_take,hin]
      · have hii : n+(i-n)=i := by omega
        have he := h ⟨i-n,by omega⟩
        rw [hii] at he
        simpa [readBit,htake,List.getElem?_append_right (show (xs.take n).length ≤ i by omega)] using he

theorem pin_iff (m t : ℕ) (σ : ℕ → Bool) :
    Satisfies (pin m t) σ ↔
      σ t=true ∧ σ m=false ∧ σ (m+1)=false ∧ σ (m+2)=false := by
  simpa only [Satisfies,pin,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq] using forceTrue_local (σ t) (σ m) (σ (m+1)) (σ (m+2))

theorem ground_iff (xs : List Bool) (n : ℕ) (hn : n+4≤xs.length) :
    Satisfies (pin (n+1) n) (readBit xs) ↔
      xs.take (n+4)=xs.take n++[true,false,false,false] := by
  rw [pin_iff]
  have hp := prefix_append_iff xs [true,false,false,false] n hn
  simp only [List.length_cons,List.length_nil] at hp
  rw [hp]
  constructor
  · rintro ⟨ht,hf,hi,hk⟩ i
    fin_cases i <;> simpa [readBit,Nat.add_assoc] using (by assumption : _)
  · intro h
    exact ⟨by simpa [readBit] using h 0,by simpa [readBit] using h 1,
      by simpa [readBit,Nat.add_assoc] using h 2,by simpa [readBit,Nat.add_assoc] using h 3⟩

theorem finish_iff (xs : List Bool) (m t : ℕ) (hm : m+3≤xs.length) :
    Satisfies (pin m t) (readBit xs) ↔
      readBit xs t=true ∧ xs.take (m+3)=xs.take m++[false,false,false] := by
  rw [pin_iff]
  have hp := prefix_append_iff xs [false,false,false] m hm
  simp only [List.length_cons,List.length_nil] at hp
  rw [hp]
  constructor
  · rintro ⟨ht,h0,h1,h2⟩
    refine ⟨ht,?_⟩
    intro i
    fin_cases i <;> simpa [readBit,Nat.add_assoc] using (by assumption : _)
  · rintro ⟨ht,h⟩
    exact ⟨ht,by simpa [readBit] using h 0,by simpa [readBit] using h 1,
      by simpa [readBit] using h 2⟩

/-- Fixed-width list and functional assignment views are literally inverse. -/
theorem ofFn_read_take (xs : List Bool) (n : ℕ) (hn : n≤xs.length) :
    List.ofFn (fun i : Fin n => readBit xs i.val)=xs.take n := by
  apply list_eq_of_read
  · simp [List.length_take_of_le hn]
  · intro i hi
    have hin : i<n := by simpa using hi
    simp [readBit,List.getElem?_ofFn,hin,List.getElem?_take]

theorem ofFn_read (xs : List Bool) (n : ℕ) (hn : xs.length=n) :
    List.ofFn (fun i : Fin n => readBit xs i.val)=xs := by
  rw [ofFn_read_take xs n (by omega),List.take_of_length_le (by omega)]

def extensionList (p : CountingNorProgram.Program) (w : Fin p.1 → Bool) : List Bool :=
  runNor p.2.1 (initialStore w)++[false,false,false]

@[simp] theorem extensionList_length (p : CountingNorProgram.Program) (w : Fin p.1 → Bool) :
    (extensionList p w).length=(compile p).1 := by simp [extensionList]

theorem extensionList_read_input (p : CountingNorProgram.Program) (w : Fin p.1 → Bool) (i : Fin p.1) :
    readBit (extensionList p w) i.val=w i := by
  have hi : i.val<(runNor p.2.1 (initialStore w)).length := by simp; omega
  simp only [extensionList,readBit,List.getElem?_append_left hi]
  change readBit (runNor p.2.1 (initialStore w)) i.val=w i
  rw [runNor_read_old _ _ _ (by simp; omega),initialStore_read]

/-- The output formula forces exactly the actual NOR execution followed by
three false acceptance auxiliaries, and nothing else. -/
theorem satisfies_compile_iff (p : CountingNorProgram.Program) (xs : List Bool)
    (hlen : xs.length=(compile p).1) :
    Satisfies (compile p).2 (readBit xs) ↔
      CountingNorProgram.accepts p (fun i => readBit xs i.val)=true ∧
      xs=extensionList p (fun i => readBit xs i.val) := by
  let m := p.1+4+4*p.2.1.length
  have hlen' : xs.length=m+3 := by simpa [m] using hlen
  have hin : p.1+4≤xs.length := by omega
  have hw : List.ofFn (fun i : Fin p.1 => readBit xs i.val)=xs.take p.1 :=
    ofFn_read_take xs p.1 (by omega)
  rw [compile_clauses,satisfies_append,satisfies_append,ground_iff xs p.1 hin]
  change (_ ∧ _) ∧ Satisfies (pin m (checkedRef m (p.1+1) p.2.2)) (readBit xs) ↔ _
  constructor
  · rintro ⟨⟨hg,hn⟩,hf⟩
    have hz : readBit xs (p.1+1)=false := by
      have he := congrArg (fun zs => readBit zs (p.1+1)) hg
      dsimp only at he
      rw [readBit_take xs (p.1+4) (p.1+1) (by omega)] at he
      simpa [readBit,List.getElem?_append_right,List.length_take_of_le (show p.1≤xs.length by omega)] using he
    have hrun := (network_iff p.2.1 xs (p.1+4) (p.1+1) (by omega) hz).mp hn
    have hinit : xs.take (p.1+4)=initialStore (fun i : Fin p.1 => readBit xs i.val) := by
      simpa [initialStore,hw] using hg
    rw [hinit] at hrun
    change xs.take m=_ at hrun
    have hfinal := (finish_iff xs m _ (by omega)).mp hf
    have hout : CountingNorProgram.accepts p (fun i => readBit xs i.val)=true := by
      rw [checkedRef_read xs m (p.1+1) p.2.2 hz] at hfinal
      simpa [CountingNorProgram.accepts,hrun] using hfinal.1
    refine ⟨hout,?_⟩
    simpa [extensionList,hrun,List.take_of_length_le (show xs.length≤m+3 by omega)] using hfinal.2
  · rintro ⟨ha,he⟩
    let w : Fin p.1 → Bool := fun i => readBit xs i.val
    have hinit : xs.take (p.1+4)=initialStore w := by
      rw [he]
      change (runNor p.2.1 (initialStore w)++[false,false,false]).take (p.1+4)=_
      rw [List.take_append_of_le_length (by simp),runNor_take _ _ _ (by simp),
        List.take_of_length_le (by simp)]
    have hg : xs.take (p.1+4)=xs.take p.1++[true,false,false,false] := by
      simpa [initialStore,w,hw] using hinit
    have hz : readBit xs (p.1+1)=false := by
      have hi : p.1+1<(initialStore w).length := by simp
      have he' := congrArg (fun zs => readBit zs (p.1+1)) hinit
      dsimp only at he'
      rw [readBit_take xs (p.1+4) (p.1+1) (by omega)] at he'
      simpa [initialStore,readBit,List.getElem?_append_right] using he'
    have hrun : xs.take m=runNor p.2.1 (initialStore w) := by
      rw [he]
      change (runNor p.2.1 (initialStore w)++[false,false,false]).take m=_
      have hl : (runNor p.2.1 (initialStore w)).length=m := by simp [m]
      rw [List.take_append_of_le_length (by omega),List.take_of_length_le (by omega)]
    refine ⟨⟨hg,(network_iff p.2.1 xs (p.1+4) (p.1+1) (by omega) hz).mpr ?_⟩,
      (finish_iff xs m _ (by omega)).mpr ?_⟩
    · simpa [hinit] using hrun
    · constructor
      · rw [checkedRef_read xs m (p.1+1) p.2.2 hz,hrun]
        exact ha
      · rw [List.take_of_length_le (by omega),hrun]
        exact he

/-- Satisfaction uses the declared finite assignment, with no hidden variables. -/
abbrev Solutions (f : NumericFormula) :=
  {σ : Fin f.1 → Bool // Satisfies f.2 (readBit (List.ofFn σ))}

def extend (p : CountingNorProgram.Program) (w : Fin p.1 → Bool) : Fin (compile p).1 → Bool :=
  fun i => readBit (extensionList p w) i.val

@[simp] theorem ofFn_extend (p : CountingNorProgram.Program) (w : Fin p.1 → Bool) :
    List.ofFn (extend p w)=extensionList p w :=
  ofFn_read _ _ (extensionList_length p w)

@[simp] theorem restrict_extend (p : CountingNorProgram.Program) (w : Fin p.1 → Bool) :
    (fun i : Fin p.1 => readBit (List.ofFn (extend p w)) i.val)=w := by
  funext i
  rw [ofFn_extend,extensionList_read_input]

/-- Explicit inverse maps: extend by actual execution, restrict to original
free input registers. Even unused free bits are preserved individually. -/
def solutionsEquiv (p : CountingNorProgram.Program) :
    {w : Fin p.1 → Bool // CountingNorProgram.accepts p w=true} ≃ Solutions (compile p) where
  toFun w := ⟨extend p w.val, by
    apply (satisfies_compile_iff p _ (by simp)).mpr
    rw [restrict_extend,ofFn_extend]
    exact ⟨w.property,rfl⟩⟩
  invFun σ := ⟨fun i => readBit (List.ofFn σ.val) i.val,
    ((satisfies_compile_iff p _ (by simp)).mp σ.property).1⟩
  left_inv w := by
    apply Subtype.ext
    exact restrict_extend p w.val
  right_inv σ := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [ofFn_extend]
    exact ((satisfies_compile_iff p _ (by simp)).mp σ.property).2.symm

/-- Exactly equal integer counts; there is no multiplicity or division factor. -/
theorem count_preserved (p : CountingNorProgram.Program) :
    Fintype.card (Solutions (compile p))=CountingNorProgram.count p :=
  (Fintype.card_congr (solutionsEquiv p)).symm

end PlanarHom.NorExactOne
