import PlanarHom.ArithmeticCircuitPrimitives
import PlanarHom.MachineOutputTransport

/-! Exact parameter-retaining codecs and actual framing transformations for dependent fields. -/
namespace PlanarHom.DependentFieldCodecs
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
variable {X : Type} {A : X → Type} (ex : BitEncoding X) (e : ∀ x, BitEncoding (A x))

/-- A literal parameter frame followed by that parameter's value word. -/
def sigma : BitEncoding (Σ x, A x) where
  encode p := BitEncoding.frame (ex.encode p.1) ++ (e p.1).encode p.2
  decode bits := do
    let (tag, payload) ← BitEncoding.unframe bits
    let x ← ex.decode tag
    let a ← (e x).decode payload
    return ⟨x,a⟩
  decode_encode p := by simp [BitEncoding.unframe_frame_append, ex.decode_encode, (e p.1).decode_encode]

/-- A pointwise view of accumulator words. Ignoring the fixed tag while decoding
is harmless: canonical traces always retain that same parameter. -/
def tagged (x : X) : BitEncoding (A x) where
  encode a := (sigma ex e).encode ⟨x,a⟩
  decode bits := do
    let (_, payload) ← BitEncoding.unframe bits
    (e x).decode payload
  decode_encode a := by simp [sigma, BitEncoding.unframe_frame_append, (e x).decode_encode]

/-- Source-(b) binary operator input: x, then the pair of same-field values. -/
def pair : BitEncoding (Σ x, A x × A x) := sigma ex (fun x => (e x).prod (e x))

/-- Original dependent fold input: x, an initial value, and a literal value list. -/
def input : BitEncoding (Σ x, A x × List (A x)) := sigma ex (fun x => (e x).prod (e x).list)

/-- The list-fold loop frames the complete tagged accumulator before each item. -/
def step : BitEncoding (Σ x, A x × A x) where
  encode p := BitEncoding.frame ((sigma ex e).encode ⟨p.1,p.2.1⟩) ++ (e p.1).encode p.2.2
  decode bits := do
    let (state, item) ← BitEncoding.unframe bits
    let p ← (sigma ex e).decode state
    let b ← (e p.1).decode item
    return ⟨p.1,(p.2,b)⟩
  decode_encode p := by simp [BitEncoding.unframe_frame_append, (sigma ex e).decode_encode, (e p.1).decode_encode]

/-- The prepared word contains exactly the loop's framed initial tagged state and list. -/
def prepared : BitEncoding (Σ x, A x × List (A x)) where
  encode p := BitEncoding.frame ((sigma ex e).encode ⟨p.1,p.2.1⟩) ++ (e p.1).list.encode p.2.2
  decode bits := do
    let (state, items) ← BitEncoding.unframe bits
    let p ← (sigma ex e).decode state
    let xs ← (e p.1).list.decode items
    return ⟨p.1,(p.2,xs)⟩
  decode_encode p := by simp [BitEncoding.unframe_frame_append, (sigma ex e).decode_encode, (e p.1).list.decode_encode]

@[simp] theorem tagged_encode (x : X) (a : A x) :
    (tagged ex e x).encode a = (sigma ex e).encode ⟨x,a⟩ := rfl

theorem step_sameWords (x : X) (a b : A x) :
    (step ex e).encode ⟨x,(a,b)⟩ = ((tagged ex e x).prod (e x)).encode (a,b) := rfl

theorem prepared_sameWords (x : X) (a : A x) (xs : List (A x)) :
    (prepared ex e).encode ⟨x,(a,xs)⟩ = ((tagged ex e x).prod (e x).list).encode (a,xs) := rfl

/-- Actual raw framing rebrackets a loop call into the supplied same-x operator codec. -/
theorem fp_step_to_pair : FP (step ex e) (pair ex e) id := by
  let bits := BitEncoding.bits
  have hv : FP (step ex e) ((bits.prod bits).prod bits)
      (fun p => ((ex.encode p.1,(e p.1).encode p.2.1),(e p.1).encode p.2.2)) :=
    fp_code_view _ _ _ (fun _ => rfl)
  have hl := hv.comp (fp_fst (bits.prod bits) bits)
  have hx := hl.comp (fp_fst bits bits)
  have ha := hl.comp (fp_snd bits bits)
  have hb := hv.comp (fp_snd (bits.prod bits) bits)
  exact (hx.pair (ha.pair hb)).transportOutput (fun _ => rfl)

/-- Actual preprocessing moves the parameter frame into the accumulator frame.
The list's exact canonical words are copied; no dependent decoding is made free. -/
theorem fp_prepare : FP (input ex e) (prepared ex e) id := by
  let bits := BitEncoding.bits
  have hv : FP (input ex e) (bits.prod (bits.prod bits))
      (fun p => (ex.encode p.1,((e p.1).encode p.2.1,(e p.1).list.encode p.2.2))) :=
    fp_code_view _ _ _ (fun _ => rfl)
  have hx := hv.comp (fp_fst bits (bits.prod bits))
  have ht := hv.comp (fp_snd bits (bits.prod bits))
  have ha := ht.comp (fp_fst bits bits)
  have hl := ht.comp (fp_snd bits bits)
  exact ((hx.pair ha).pair hl).transportOutput (fun _ => rfl)

end PlanarHom.DependentFieldCodecs
