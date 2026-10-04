import PlanarHom.CodecDecodingBounds
import PlanarHom.RawBooleanListMachine
import PlanarHom.ListFoldMachines
import PlanarHom.ArithmeticCircuitPrimitives
import PlanarHom.ConditionalMachines

/-! NEW total escaped-frame parser. Its finite control reads every raw input
bit, including malformed words; later machines compile this literal scan. -/
namespace PlanarHom.RawFrameParser
open Complexity
abbrev State := Bool × (Bool × (Bits × Bits))
/-- done, expecting payload bit, reversed payload, reversed suffix. -/
def step (s:State) (b:Bool) : State :=
  if s.1 then (true,s.2.1,s.2.2.1,b::s.2.2.2)
  else if s.2.1 then (false,false,b::s.2.2.1,s.2.2.2)
  else if b then (false,true,s.2.2.1,s.2.2.2)
  else (true,false,s.2.2.1,s.2.2.2)

def initial : State := (false,false,[],[])
def scan (raw:Bits) : State := raw.foldl step initial
abbrev Result := Bool × (Bits × Bits)
def parse (raw:Bits) : Result :=
  let s:=scan raw
  (s.1,s.2.2.1.reverse,s.2.2.2.reverse)

def escaped : Bits→Bits
  | []=>[]
  | b::bs=>true::b::escaped bs

@[simp] theorem escaped_append (a b:Bits) : escaped (a++b)=escaped a++escaped b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,escaped,ih]

@[simp] theorem escaped_frame (w:Bits) : escaped w++[false]=BitEncoding.frame w := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp only [escaped,List.cons_append,ih,BitEncoding.frame]

 theorem step_done (s:State) (b:Bool) (h:s.1=true) : (step s b).1=true := by simp [step,h]

 theorem scan_frame (w acc tail:Bits) :
     (BitEncoding.frame w).foldl step (false,false,acc,tail)=(true,false,w.reverse++acc,tail) := by
   induction w generalizing acc with
   | nil => simp [BitEncoding.frame,step]
   | cons b bs ih => simpa [BitEncoding.frame,step,List.reverse_cons,List.append_assoc] using ih (b::acc)

 theorem scan_done (raw acc tail:Bits) (mode:Bool) :
     raw.foldl step (true,mode,acc,tail)=(true,mode,acc,raw.reverse++tail) := by
   induction raw generalizing tail with
   | nil => simp
   | cons b bs ih => simpa [List.foldl_cons,step,List.reverse_cons,List.append_assoc] using ih (b::tail)

 theorem parse_frame_append (word tail:Bits) : parse (BitEncoding.frame word++tail)=(true,word,tail) := by
   simp [parse,scan,initial,List.foldl_append,scan_frame,scan_done]

/-- Every unfinished state is an escaped prefix and every finished state is
exactly a complete first frame followed by the stored suffix. -/
 def Represents (raw:Bits) (s:State) : Prop :=
   if s.1 then raw=BitEncoding.frame s.2.2.1.reverse++s.2.2.2.reverse
   else raw=escaped s.2.2.1.reverse++(if s.2.1 then [true] else []) ∧ s.2.2.2=[]

 theorem represents_step (raw:Bits) (s:State) (b:Bool) (h:Represents raw s) :
     Represents (raw++[b]) (step s b) := by
   rcases s with ⟨done,mode,word,tail⟩
   cases done <;> cases mode <;> cases b
   all_goals simp only [Represents,step,Bool.false_eq_true,ite_false,ite_true,List.reverse_nil,List.append_nil] at h ⊢
   all_goals first | (rcases h with ⟨rfl,rfl⟩) | (subst raw)
   all_goals simp [List.reverse_cons,List.append_assoc,escaped_frame,escaped]

 theorem scan_represents (raw:Bits) : Represents raw (scan raw) := by
   induction raw using List.reverseRecOn with
   | nil => simp [Represents,scan,initial,escaped]
   | append_singleton raw b ih =>
     simpa only [scan,List.foldl_append,List.foldl_cons,List.foldl_nil] using represents_step raw (scan raw) b ih

 theorem parse_success (raw:Bits) (h:(parse raw).1=true) :
     BitEncoding.unframe raw=some ((parse raw).2.1,(parse raw).2.2) := by
   have hs:=scan_represents raw
   change (scan raw).1=true at h
   simp only [Represents,h,ite_true] at hs
   change BitEncoding.unframe raw=some ((scan raw).2.2.1.reverse,(scan raw).2.2.2.reverse)
   conv_lhs => rw [hs,BitEncoding.unframe_frame_append]

 theorem parse_of_unframe (raw word tail:Bits) (h:BitEncoding.unframe raw=some (word,tail)) :
     parse raw=(true,word,tail) := by
   rw [BitEncoding.unframe_spec _ _ _ h]
   exact parse_frame_append word tail

 theorem parse_spec (raw:Bits) :
     BitEncoding.unframe raw=if (parse raw).1 then some ((parse raw).2.1,(parse raw).2.2) else none := by
   cases h:(parse raw).1
   · cases hu:BitEncoding.unframe raw with
     | none=>rfl
     | some p=>
       have hp:=parse_of_unframe raw p.1 p.2 hu
       have hh:=congrArg Prod.fst hp
       simp [h] at hh
   · exact parse_success raw h
end PlanarHom.RawFrameParser
