import PlanarHom.DependentFieldCodecs
import PlanarHom.ListMapMachines
import PlanarHom.FixedVectorMachines

/-! Actual framing and payload programs for parameter-preserving dependent values. -/
namespace PlanarHom.DependentEncodingMachines
open Complexity PairProjectionMachines
variable {X : Type} {A B : X → Type} (ex : BitEncoding X)
variable (ea : ∀ x, BitEncoding (A x)) (eb : ∀ x, BitEncoding (B x))

 theorem fp_parameter : FP (DependentFieldCodecs.sigma ex ea) ex Sigma.fst := by
  have hv : FP (DependentFieldCodecs.sigma ex ea) (ex.prod BitEncoding.bits)
      (fun s => (s.1,(ea s.1).encode s.2)) := fp_code_view _ _ _ (fun _ => rfl)
  exact hv.comp (fp_fst _ _)

theorem fp_payload : FP (DependentFieldCodecs.sigma ex ea) BitEncoding.bits
    (fun s => (ea s.1).encode s.2) := by
  have hv : FP (DependentFieldCodecs.sigma ex ea) (ex.prod BitEncoding.bits)
      (fun s => (s.1,(ea s.1).encode s.2)) := fp_code_view _ _ _ (fun _ => rfl)
  exact hv.comp (fp_snd _ _)

variable {D : Type} {ed : BitEncoding D} {x : D → X}

theorem fp_assemble {a : ∀ d, A (x d)} (hx : FP ed ex x)
    (ha : FP ed BitEncoding.bits (fun d => (ea (x d)).encode (a d))) :
    FP ed (DependentFieldCodecs.sigma ex ea) (fun d => ⟨x d,a d⟩) :=
  (hx.pair ha).transportOutput (fun _ => rfl)

theorem fp_pair {a : ∀ d, A (x d)} {b : ∀ d, B (x d)}
    (ha : FP ed (DependentFieldCodecs.sigma ex ea) (fun d => ⟨x d,a d⟩))
    (hb : FP ed (DependentFieldCodecs.sigma ex eb) (fun d => ⟨x d,b d⟩)) :
    FP ed (DependentFieldCodecs.sigma ex (fun x => (ea x).prod (eb x)))
      (fun d => ⟨x d,(a d,b d)⟩) := by
  have hx := ha.comp (fp_parameter ex ea)
  have hab := (ha.comp (fp_payload ex ea)).pair (hb.comp (fp_payload ex eb))
  exact (hx.pair hab).transportOutput (fun _ => rfl)

theorem fp_fst : FP (DependentFieldCodecs.sigma ex (fun x => (ea x).prod (eb x)))
    (DependentFieldCodecs.sigma ex ea) (fun s => ⟨s.1,s.2.1⟩) := by
  have hv : FP (DependentFieldCodecs.sigma ex (fun x => (ea x).prod (eb x)))
      (ex.prod (BitEncoding.bits.prod BitEncoding.bits))
      (fun s => (s.1,((ea s.1).encode s.2.1,(eb s.1).encode s.2.2))) :=
    fp_code_view _ _ _ (fun _ => rfl)
  have hx := hv.comp (PairProjectionMachines.fp_fst _ _)
  have ha := (hv.comp (PairProjectionMachines.fp_snd _ _)).comp (PairProjectionMachines.fp_fst _ _)
  exact fp_assemble ex ea hx ha

theorem fp_snd : FP (DependentFieldCodecs.sigma ex (fun x => (ea x).prod (eb x)))
    (DependentFieldCodecs.sigma ex eb) (fun s => ⟨s.1,s.2.2⟩) := by
  have hv : FP (DependentFieldCodecs.sigma ex (fun x => (ea x).prod (eb x)))
      (ex.prod (BitEncoding.bits.prod BitEncoding.bits))
      (fun s => (s.1,((ea s.1).encode s.2.1,(eb s.1).encode s.2.2))) :=
    fp_code_view _ _ _ (fun _ => rfl)
  have hx := hv.comp (PairProjectionMachines.fp_fst _ _)
  have hb := (hv.comp (PairProjectionMachines.fp_snd _ _)).comp (PairProjectionMachines.fp_snd _ _)
  exact fp_assemble ex eb hx hb

/-- A list of values already computed with the same parameter can be stripped
of its repeated parameter frames by an ordinary actual list-map machine. -/
theorem fp_collect {as : ∀ d, List (A (x d))} (hx : FP ed ex x)
    (ha : FP ed (DependentFieldCodecs.sigma ex ea).list
      (fun d => (as d).map (fun a => (⟨x d,a⟩ : Σ x, A x)))) :
    FP ed (DependentFieldCodecs.sigma ex (fun x => (ea x).list)) (fun d => ⟨x d,as d⟩) := by
  have hwords := ha.comp (ListMapMachines.fp_map _ _ _ (fp_payload ex ea))
  exact (hx.pair hwords).transportOutput (fun d => by
    simp only [BitEncoding.prod, DependentFieldCodecs.sigma, BitEncoding.list,
      List.length_map, List.map_map, Function.comp_def, BitEncoding.bits, id_eq])

/-- A fixed coordinate is projected from the literal vector payload. -/
theorem fp_coordinate (t : ℕ) (i : Fin t) :
    FP (DependentFieldCodecs.sigma ex (fun x => (ea x).vector t))
      (DependentFieldCodecs.sigma ex ea) (fun s => ⟨s.1,s.2 i⟩) := by
  have hv : FP (DependentFieldCodecs.sigma ex (fun x => (ea x).vector t))
      (ex.prod (BitEncoding.bits.vector t))
      (fun s => (s.1,fun j => (ea s.1).encode (s.2 j))) :=
    fp_code_view _ _ _ (fun s => by
      simp only [DependentFieldCodecs.sigma, BitEncoding.prod, BitEncoding.vector,
        BitEncoding.list, List.length_ofFn, List.map_ofFn, Function.comp_def, BitEncoding.bits, id_eq])
  exact fp_assemble ex ea (hv.comp (PairProjectionMachines.fp_fst _ _))
    ((hv.comp (PairProjectionMachines.fp_snd _ _)).comp (FixedVectorMachines.fp_coordinate _ t i))

end PlanarHom.DependentEncodingMachines
