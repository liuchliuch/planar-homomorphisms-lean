import PlanarHom.IntegerStraightDrawing
import Mathlib.Tactic

/-! NEW reconstruction: an explicit unscaled integer segment model for every
radial tile. Short edges are square-grid sides or corners; the switched red
edges have unit horizontal span. All collision obligations are proved below. -/
namespace PlanarHom.RadialPottsTileGeometry
open IntegerStraightDrawing

def turn (s : Fin 4) (p : Point) : Point :=
  ![p,(p.2,-p.1),(-p.1,-p.2),(-p.2,p.1)] s

inductive Segment where
  | long (r : ℤ) (s : Fin 4) (a : ℤ)
  | side (r : ℤ) (s : Fin 4) (t : ℤ)
  | corner (r : ℤ) (s : Fin 4)
  | special (r : ℤ)
  deriving DecidableEq

def Segment.Valid (k : ℤ) : Segment → Prop
  | .long r _ a => 0≤r ∧ r<k ∧ 0≤a ∧ a≤r
  | .side r s t => 0≤r ∧ r<k ∧ 0≤t ∧ t<2*r ∧ (s≠0 ∨ t≠0)
  | .corner r s => 0≤r ∧ r<k ∧ (s≠0 ∨ r≠0)
  | .special r => 0≤r ∧ r<k

def Segment.start (k : ℤ) : Segment → Point
  | .long r s a => turn s (2*a-r,r+1)
  | .side r s t => turn s (t-r,r+1)
  | .corner r s => turn s (r,r+1)
  | .special r => (-r,r+1+(if r+1<k then 1 else 0))

def Segment.finish : Segment → Point
  | .long r s a => turn s (2*a-r,r+2)
  | .side r s t => turn s (t+1-r,r+1)
  | .corner r s => turn s (r+1,r)
  | .special r => (1-r,r)

set_option maxHeartbeats 4000000 in
/-- Every distinct pair of valid model segments has a literal exact integer
separation certificate, for every tile size simultaneously. -/
theorem Segment.separated (k : ℤ) (e f : Segment) (he : e.Valid k) (hf : f.Valid k)
    (hne : e≠f) : Separated (e.start k) e.finish (f.start k) f.finish := by
  cases e with
  | long r s a =>
    cases f with
    | long q z b =>
      fin_cases s <;>
        fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | side q z u =>
      fin_cases s <;>
        fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | corner q z =>
      fin_cases s <;>
        fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | special q =>
      fin_cases s <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals split_ifs at *
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
  | side r s t =>
    cases f with
    | long q z b =>
      fin_cases s <;>
        fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | side q z u =>
      fin_cases s <;>
        fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | corner q z =>
      fin_cases s <;>
        fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | special q =>
      fin_cases s <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals split_ifs at *
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
  | corner r s =>
    cases f with
    | long q z b =>
      fin_cases s <;>
        fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | side q z u =>
      fin_cases s <;>
        fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | corner q z =>
      fin_cases s <;>
        fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | special q =>
      fin_cases s <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals split_ifs at *
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
  | special r =>
    cases f with
    | long q z b =>
      fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals split_ifs at *
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | side q z u =>
      fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals split_ifs at *
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | corner q z =>
      fin_cases z <;>
        simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals split_ifs at *
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega
    | special q =>
      simp only [Segment.Valid,Segment.start,Segment.finish,turn] at he hf ⊢ <;>
        norm_num at he hf hne ⊢
      all_goals split_ifs at *
      all_goals simp only [Separated,sameSide,coordinateSeparate,orient,Prod.fst,Prod.snd] at *
      all_goals ring_nf at *
      all_goals omega

end PlanarHom.RadialPottsTileGeometry
