import PlanarHom.RawFrameParserMachines

/-! NEW total parser for an entire list of escaped payload words. The loop
runs once per raw bit, so an oversized binary list header cannot cause a long
verification run. Header/count agreement is checked after this scan. -/
namespace PlanarHom.RawFramesParser
open Complexity
abbrev State := Bool × (Bits × List Bits)
def step (s:State) (b:Bool) : State :=
  if s.1 then (false,b::s.2.1,s.2.2)
  else if b then (true,s.2.1,s.2.2)
  else (false,[],s.2.1::s.2.2)
def initial : State := (false,[],[])
def scan (raw:Bits) : State := raw.foldl step initial
abbrev Result := Bool × List Bits
def parse (raw:Bits) : Result :=
  let s:=scan raw
  (!s.1 && s.2.1.isEmpty,s.2.2.reverse.map List.reverse)

theorem scan_frame (w acc:Bits) (words:List Bits) :
    (BitEncoding.frame w).foldl step (false,acc,words)=(false,[],(w.reverse++acc)::words) := by
  induction w generalizing acc with
  | nil => simp [BitEncoding.frame,step]
  | cons b bs ih => simpa [BitEncoding.frame,step,List.reverse_cons,List.append_assoc] using ih (b::acc)

theorem scan_frames (ws acc:List Bits) :
    (BitEncoding.frames ws).foldl step (false,[],acc)=(false,[],(ws.reverse.map List.reverse)++acc) := by
  induction ws generalizing acc with
  | nil => simp [BitEncoding.frames]
  | cons w ws ih =>
    simp only [BitEncoding.frames,List.foldl_append,scan_frame,List.append_nil]
    rw [ih]
    simp [List.reverse_cons,List.append_assoc]

theorem parse_frames (ws:List Bits) : parse (BitEncoding.frames ws)=(true,ws) := by
  simp [parse,scan,initial,scan_frames,List.map_reverse,List.map_map,Function.comp_def]

def Represents (raw:Bits) (s:State) : Prop :=
  raw=BitEncoding.frames (s.2.2.reverse.map List.reverse)++RawFrameParser.escaped s.2.1.reverse++
    (if s.1 then [true] else [])

theorem represents_step (raw:Bits) (s:State) (b:Bool) (h:Represents raw s) :
    Represents (raw++[b]) (step s b) := by
  rcases s with ⟨mode,word,words⟩
  unfold Represents at h
  subst raw
  cases mode <;> cases b
  all_goals simp [Represents,step,List.reverse_cons,List.map_append,List.append_assoc,
    RawFrameParser.escaped,RawFrameParser.escaped_frame,BitEncoding.frames]

theorem scan_represents (raw:Bits) : Represents raw (scan raw) := by
  induction raw using List.reverseRecOn with
  | nil => simp [Represents,scan,initial,RawFrameParser.escaped,BitEncoding.frames]
  | append_singleton raw b ih =>
    simpa only [scan,List.foldl_append,List.foldl_cons,List.foldl_nil] using represents_step raw (scan raw) b ih

theorem parse_success (raw:Bits) (h:(parse raw).1=true) : raw=BitEncoding.frames (parse raw).2 := by
  have hs:=scan_represents raw
  have hh : (Bool.not (scan raw).1=true ∧ (scan raw).2.1.isEmpty=true) := by
    simpa only [parse,Bool.and_eq_true] using h
  have hm:(scan raw).1=false := by simpa only [Bool.not_eq_true'] using hh.1
  have hw:(scan raw).2.1=[] := List.isEmpty_iff.mp hh.2
  simpa only [Represents,hm,hw,Bool.false_eq_true,ite_false,List.reverse_nil,RawFrameParser.escaped,List.append_nil,parse] using hs

def decodeFrames (n:ℕ) (raw:Bits) : Option (List Bits) := do
  let (ws,tail)←BitEncoding.unframes n raw
  if tail=[] then some ws else none

theorem decodeFrames_some_iff (n:ℕ) (raw:Bits) (ws:List Bits) :
    decodeFrames n raw=some ws ↔ raw=BitEncoding.frames ws ∧ ws.length=n := by
  constructor
  · intro h
    unfold decodeFrames at h
    cases hu:BitEncoding.unframes n raw with
    | none => simp [hu] at h
    | some p =>
      rcases p with ⟨words,tail⟩
      by_cases ht:tail=[]
      · subst tail
        have he:words=ws:=by simpa [hu] using h
        subst words
        obtain ⟨hl,hr⟩:=BitEncoding.unframes_spec n raw ws [] hu
        exact ⟨by simpa using hr,hl⟩
      · simp [hu,ht] at h
  · rintro ⟨rfl,rfl⟩
    simp [decodeFrames,BitEncoding.unframes_frames]

theorem decodeFrames_spec (n:ℕ) (raw:Bits) :
    decodeFrames n raw=if (parse raw).1 && decide ((parse raw).2.length=n) then some (parse raw).2 else none := by
  by_cases h:(parse raw).1=true ∧ (parse raw).2.length=n
  · have he:=parse_success raw h.1
    simp only [h.1,h.2,decide_true,Bool.and_self,ite_true]
    exact (decodeFrames_some_iff n raw _).mpr ⟨he,h.2⟩
  · have hfalse:((parse raw).1 && decide ((parse raw).2.length=n))=false := by
      cases hv:(parse raw).1 <;> simp_all
    rw [hfalse]
    cases hd:decodeFrames n raw with
    | none => rfl
    | some ws =>
      obtain ⟨hr,hn⟩:=(decodeFrames_some_iff n raw ws).mp hd
      have hp:parse raw=(true,ws) := by rw [hr,parse_frames]
      exact False.elim (h (by simp [hp,hn]))
end PlanarHom.RawFramesParser
