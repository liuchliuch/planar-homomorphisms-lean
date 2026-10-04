import PlanarHom.PositiveFanoutDrawing

/-! Concrete adjacent-swap routing. A selected original rail is brought next to
the occurrence-output region, copied once, then the original rail order is
restored by the inverse swap list. No arbitrary permutation primitive is used. -/
namespace PlanarHom.AdjacentRailRouting
variable {A : Type}

def swapAt : ℕ → List A → List A
  | 0,a::b::xs => b::a::xs
  | 0,xs => xs
  | i+1,a::xs => a::swapAt i xs
  | _+1,[] => []

def duplicateAt : ℕ → List A → List A
  | 0,a::xs => a::a::xs
  | i+1,a::xs => a::duplicateAt i xs
  | _,[] => []

def runSwaps (script : List ℕ) (xs : List A) : List A :=
  script.foldl (fun xs i => swapAt i xs) xs

def moveScript : ℕ → ℕ → List ℕ
  | _,0 => []
  | start,steps+1 => start::moveScript (start+1) steps

@[simp] theorem runSwaps_nil (xs : List A) : runSwaps [] xs=xs := rfl
@[simp] theorem runSwaps_cons (i : ℕ) (is : List ℕ) (xs : List A) :
    runSwaps (i::is) xs=runSwaps is (swapAt i xs) := rfl
@[simp] theorem runSwaps_append (is js : List ℕ) (xs : List A) :
    runSwaps (is++js) xs=runSwaps js (runSwaps is xs) := List.foldl_append

@[simp] theorem swapAt_involution (i : ℕ) (xs : List A) : swapAt i (swapAt i xs)=xs := by
  induction i generalizing xs with
  | zero => cases xs with
    | nil => rfl
    | cons a xs => cases xs <;> rfl
  | succ i ih => cases xs with
    | nil => rfl
    | cons a xs => simp [swapAt,ih]

@[simp] theorem swapAt_length (i : ℕ) (xs : List A) : (swapAt i xs).length=xs.length := by
  induction i generalizing xs with
  | zero => cases xs with
    | nil => rfl
    | cons a xs => cases xs <;> rfl
  | succ i ih => cases xs with
    | nil => rfl
    | cons a xs => simp [swapAt,ih]

/-- Reverse swaps are the actual inverse circuit, on every list. -/
@[simp] theorem runSwaps_reverse (is : List ℕ) (xs : List A) :
    runSwaps is.reverse (runSwaps is xs)=xs := by
  induction is generalizing xs with
  | nil => rfl
  | cons i is ih => simp only [List.reverse_cons,runSwaps_append,runSwaps_cons,runSwaps_nil,ih,swapAt_involution]

@[simp] theorem moveScript_length (start steps : ℕ) : (moveScript start steps).length=steps := by
  induction steps generalizing start with
  | zero => rfl
  | succ steps ih => simp [moveScript,ih]

/-- Exactly the adjacent positions start,...,start+steps-1 are emitted. -/
theorem moveScript_bounds (start steps i : ℕ) (hi : i∈moveScript start steps) :
    start ≤ i ∧ i < start+steps := by
  induction steps generalizing start with
  | zero => simp [moveScript] at hi
  | succ steps ih =>
    simp only [moveScript,List.mem_cons] at hi
    rcases hi with rfl | hi
    · omega
    · have h := ih (start+1) hi
      omega

private theorem swapAt_prefix (pre tail : List A) (x y : A) :
    swapAt pre.length (pre++x::y::tail)=pre++y::x::tail := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simp [swapAt,ih]

private theorem duplicateAt_prefix (pre tail : List A) (x : A) :
    duplicateAt pre.length (pre++x::tail)=pre++x::x::tail := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simp [duplicateAt,ih]

/-- Swapping the selected rail through a known suffix leaves all other rails
in their original relative order, including any already emitted occurrences. -/
theorem move_to_end (pre post tail : List A) (x : A) :
    runSwaps (moveScript pre.length post.length) (pre++x::(post++tail))=
      pre++post++x::tail := by
  induction post generalizing pre with
  | nil => simp [moveScript]
  | cons y post ih =>
    simp only [List.length_cons,moveScript,runSwaps_cons,List.cons_append]
    rw [swapAt_prefix]
    have h := ih (pre++[y])
    simpa [List.append_assoc] using h

/-- Actual macro, with no action on an invalid original address. -/
def copyCircuit (originals index : ℕ) (xs : List A) : List A :=
  if index<originals then
    let swaps := moveScript index (originals-1-index)
    runSwaps swaps.reverse (duplicateAt (originals-1) (runSwaps swaps xs))
  else xs

/-- One occurrence is inserted after all original rails and before all previous
occurrences, while every original rail is restored literally. -/
theorem copyCircuit_correct_split (pre post tail : List A) (x : A) :
    copyCircuit (pre.length+post.length+1) pre.length (pre++x::(post++tail))=
      pre++x::(post++x::tail) := by
  have hi : pre.length<pre.length+post.length+1 := by omega
  simp only [copyCircuit,if_pos hi]
  have hsteps : pre.length+post.length+1-1-pre.length=post.length := by omega
  rw [hsteps,move_to_end]
  have hn : pre.length+post.length+1-1=(pre++post).length := by simp
  rw [hn,duplicateAt_prefix]
  have he := move_to_end pre post (x::tail) x
  rw [←he,runSwaps_reverse]

/-- Both sweeps have linear length; each emitted crossing uses adjacent rails. -/
theorem copy_crossing_bound (originals index : ℕ) :
    2*(moveScript index (originals-1-index)).length≤2*originals := by
  rw [moveScript_length]
  omega

/-- The routing theorem for an arbitrary existing rail list and valid index. -/
theorem copyCircuit_correct (xs tail : List A) (i : ℕ) (hi : i<xs.length) :
    copyCircuit xs.length i (xs++tail)=xs++xs[i]::tail := by
  have hsplit : xs.take i++xs[i]::xs.drop (i+1)=xs := by
    rw [List.getElem_cons_drop hi,List.take_append_drop]
  have hp : (xs.take i).length=i := List.length_take_of_le hi.le
  have hn : (xs.take i).length+(xs.drop (i+1)).length+1=xs.length := by
    have h := congrArg List.length hsplit
    simp only [List.length_append,List.length_cons] at h
    omega
  have hin : xs.take i++xs[i]::(xs.drop (i+1)++tail)=xs++tail := by
    simpa only [List.append_assoc,List.cons_append] using congrArg (fun l => l++tail) hsplit
  have hout : xs.take i++xs[i]::(xs.drop (i+1)++xs[i]::tail)=xs++xs[i]::tail := by
    simpa only [List.append_assoc,List.cons_append] using congrArg (fun l => l++xs[i]::tail) hsplit
  have h := copyCircuit_correct_split (xs.take i) (xs.drop (i+1)) tail xs[i]
  rw [hn,hp,hin,hout] at h
  exact h

end PlanarHom.AdjacentRailRouting
