import PlanarHom.RepresentedQueryReduction
import PlanarHom.RepresentedSharpPHardness

/-! NEW: an actual represented oracle can be decoded and converted to the
canonical bytes of an ordinary promise problem. This is semantic output descent,
not an assumption that an oracle returns a preferred representation. -/
noncomputable section
namespace PlanarHom.RepresentedBit
open Complexity PairProjectionMachines

def Reduction.changeTarget {P Q P' : Problem} (r : Reduction P Q)
    (hv : ∀x, P'.valid x → P.valid x)
    (ha : ∀x, P'.valid x → ∀y, P.answer x y → P'.answer x y) : Reduction P' Q where
  machine := r.machine
  work := r.work
  queryCount := r.queryCount
  querySize := r.querySize
  computes := by
    intro oracle ho x hx
    obtain ⟨y,s,c,qs,hr,hy,hq,hn,hsize,hcost⟩ := r.computes oracle ho x (hv x hx)
    exact ⟨y,s,c,qs,hr,ha x hx y hy,hq,hn,hsize,hcost⟩

def bitsPresentation : Presentation Bits where
  Code := Bits
  encoding := BitEncoding.bits
  valid := fun _ => True
  value := id
  complete := fun x => ⟨x,trivial,rfl⟩
  normalizer := Classical.choice (fp_code_view (BitEncoding.ValidWord.encoding BitEncoding.bits)
    BitEncoding.bits BitEncoding.ValidWord.value (fun w => BitEncoding.ValidWord.value_eq rfl))

def canonicalRecovery {A K : Type} [Zero K] (P : PromiseProblem) (Q : Presentation K)
    (ea : BitEncoding A) (na : BitEncoding.Normalizer ea) (H : A → Prop)
    (target : A → Bits) (source : A → K)
    (hvalid : ∀raw, P.valid raw → ∃a, ea.decode raw = some a ∧ H a)
    (hvalue : ∀raw a, ea.decode raw = some a → H a → P.value raw = target a)
    (recover : Q.Code → Bits) (hr : FP Q.encoding BitEncoding.bits recover)
    (hcorrect : ∀a, H a → ∀c, Q.valid c → Q.value c = source a → recover c = target a) :
    Reduction (ofCanonical P) (Q.problem ea H source) := by
  let prepare : A → ℕ × List A := fun a => (0,[a])
  let fallback : Q.Code := Classical.choose (Q.complete 0)
  let post : ℕ × List Q.Code → Bits := fun p => recover (p.2.headD fallback)
  have hp : FP ea (BitEncoding.nat.prod ea.list) prepare :=
    (fp_const ea BitEncoding.nat 0).pair
      (((fp_id ea).pair (fp_const ea ea.list [])).comp (ListMutationMachines.fp_cons ea))
  have hpost : FP (BitEncoding.nat.prod Q.encoding.list) BitEncoding.bits post :=
    ((fp_snd _ _).comp (ListDecompositionMachines.fp_headD Q.encoding fallback)).comp hr
  have r := presentationPipeline Q bitsPresentation ea BitEncoding.nat ea na BitEncoding.natNormalizer
    H H target source prepare post hp hpost
    (fun a ha x hx => (List.mem_singleton.mp hx) ▸ ha)
    (by
      intro a ha bs hbs
      change List.Forall₂ _ [a] bs at hbs
      cases hbs with
      | cons hb rest =>
        cases rest
        exact ⟨trivial,hcorrect a ha _ hb.1 hb.2⟩)
  apply r.changeTarget
  · intro raw hv
    exact hvalid raw hv
  · intro raw hv out ho
    obtain ⟨a,hd,ha⟩ := hvalid raw hv
    obtain ⟨c,hc,hct,hcv⟩ := ho a hd ha
    have he : out = c := Option.some.inj hc
    change out = P.value raw
    exact he.trans (hcv.trans (hvalue raw a hd ha).symm)

end PlanarHom.RepresentedBit
