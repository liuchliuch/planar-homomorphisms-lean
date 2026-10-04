import PlanarHom.ArithmeticCircuitPrimitives
import PlanarHom.MachineOutputTransport

/-! # Actual TM2 projection and assembly for a fixed number of encoded coordinates -/
namespace PlanarHom.FixedVectorMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines

/-- The framed coordinate payload without its statically known length header. -/
def payloadEncoding {α : Type} (e : BitEncoding α) (n : ℕ) : BitEncoding (Fin n→α) where
  encode f := BitEncoding.frames ((List.ofFn f).map e.encode)
  decode bits := (e.vector n).decode (BitEncoding.frame (BitEncoding.nat.encode n) ++ bits)
  decode_encode f := by
    have h := (e.vector n).decode_encode f
    simpa only [BitEncoding.vector,BitEncoding.list,List.length_ofFn] using h

@[simp] theorem payload_cons {α : Type} (e : BitEncoding α) (n : ℕ) (a : α) (f : Fin n→α) :
    (payloadEncoding e (n+1)).encode (Fin.cons a f) =
      BitEncoding.frame (e.encode a) ++ (payloadEncoding e n).encode f := by
  simp [payloadEncoding,List.ofFn_succ,BitEncoding.frames]

theorem fp_payload_cons {α : Type} (e : BitEncoding α) (n : ℕ) :
    FP (e.prod (payloadEncoding e n)) (payloadEncoding e (n+1))
      (fun p => Fin.cons p.1 p.2) :=
  fp_code_view _ _ _ (by intro p; exact payload_cons e n p.1 p.2)

theorem fp_payload_parts {α : Type} (e : BitEncoding α) (n : ℕ) :
    FP (payloadEncoding e (n+1)) (e.prod (payloadEncoding e n))
      (fun f => (f 0,fun i => f i.succ)) :=
  fp_code_view _ _ _ (by intro f; simp [BitEncoding.prod,payloadEncoding,List.ofFn_succ,BitEncoding.frames])

/-- Only a fixed number of real framed-pair projection programs is composed. -/
theorem fp_payload_coordinate {α : Type} (e : BitEncoding α) (n : ℕ) (i : Fin n) :
    FP (payloadEncoding e n) e (fun f => f i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (fp_payload_parts e n).comp (fp_fst e (payloadEncoding e n))
    · exact ((fp_payload_parts e n).comp (fp_snd e (payloadEncoding e n))).comp (ih j)

/-- Fixed-coordinate assembly copies its input through the actual pairing compiler. -/
theorem fp_payload_assemble {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β)
    (n : ℕ) (f : α→Fin n→β) (hf : ∀ i, FP ea eb (fun a => f a i)) :
    FP ea (payloadEncoding eb n) f := by
  induction n with
  | zero =>
    exact (fp_const ea (payloadEncoding eb 0) (Fin.elim0)).congr (fun a => by funext i; exact Fin.elim0 i)
  | succ n ih =>
    have hh := hf 0
    have ht := ih (fun a i => f a i.succ) (fun i => hf i.succ)
    exact ((hh.pair ht).comp (fp_payload_cons eb n)).congr (fun a => by
      funext i
      exact Fin.cases rfl (fun j => rfl) i)

theorem fp_vector_payload {α : Type} (e : BitEncoding α) (n : ℕ) :
    FP (e.vector n) (payloadEncoding e n) id := by
  have hv : FP (e.vector n) (BitEncoding.nat.prod (payloadEncoding e n)) (fun f => (n,f)) :=
    fp_code_view _ _ _ (by intro f; simp [BitEncoding.prod,BitEncoding.vector,BitEncoding.list,payloadEncoding])
  exact hv.comp (fp_snd _ _)

theorem fp_coordinate {α : Type} (e : BitEncoding α) (n : ℕ) (i : Fin n) :
    FP (e.vector n) e (fun f => f i) := (fp_vector_payload e n).comp (fp_payload_coordinate e n i)

/-- The emitted list-length header is the fixed dimension, with canonical binary coding. -/
theorem fp_assemble {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β)
    (n : ℕ) (f : α→Fin n→β) (hf : ∀ i, FP ea eb (fun a => f a i)) :
    FP ea (eb.vector n) f := by
  have h := (fp_const ea BitEncoding.nat n).pair (fp_payload_assemble ea eb n f hf)
  exact h.transportOutput (by intro a; simp [BitEncoding.prod,BitEncoding.vector,BitEncoding.list,payloadEncoding])

end PlanarHom.FixedVectorMachines
