import PlanarHom.MixedPlanarCode
import PlanarHom.FieldNaturalExtraction
import PlanarHom.ArithmeticCircuitPrimitives

/-! NEW literal graph-to-homogeneous mixed-code serialization. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.ZeroOneMixedMembership
open Complexity Complexity.MixedCode PairProjectionMachines

def lift (g : GraphCode) : MixedCode := ⟨g.vertices,g.edges.map (fun e=>(e.1,e.2,0)),[]⟩

theorem lift_valid (g : GraphCode) (hg : g.Valid) : (lift g).Valid 1 0 := by
  constructor
  · intro e he
    change e∈g.edges.map (fun a=>(a.1,a.2,0)) at he
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp he
    change a.1<g.vertices ∧ a.2<g.vertices ∧ 0<1
    exact ⟨(hg a ha).1,(hg a ha).2,by decide⟩
  · intro u hu
    simp [lift] at hu

theorem lift_underlying (g : GraphCode) : (lift g).underlying=g := by
  cases g
  simp [lift,MixedCode.underlying,List.map_map,Function.comp_def]

theorem fp_lift : FP GraphCode.encoding MixedCode.encoding lift := by
  have hv : FP GraphCode.encoding BitEncoding.unaryNat GraphCode.vertices:=
    (fp_fst BitEncoding.unaryNat (BitEncoding.nat.prod BitEncoding.nat).list).transportInput
      (fun g : GraphCode=>(g.vertices,g.edges)) (fun _=>rfl)
  have he : FP GraphCode.encoding (BitEncoding.nat.prod BitEncoding.nat).list GraphCode.edges:=
    (fp_snd BitEncoding.unaryNat (BitEncoding.nat.prod BitEncoding.nat).list).transportInput
      (fun g : GraphCode=>(g.vertices,g.edges)) (fun _=>rfl)
  have hf:= (fp_fst BitEncoding.nat BitEncoding.nat).pair
    ((fp_snd BitEncoding.nat BitEncoding.nat).pair (fp_const _ BitEncoding.nat 0))
  have hl:=he.comp (ListMapMachines.fp_map _ _ (fun e : ℕ×ℕ=>(e.1,e.2,0)) hf)
  exact (hv.pair (hl.pair (fp_const _ (BitEncoding.nat.prod BitEncoding.nat).list []))).transportOutput (fun _=>rfl)

theorem evaluate_lift {C K : Type} [Fintype C] [CommSemiring K] (g : GraphCode) (hg : g.Valid)
    (M : Matrix C C K) (w : C→K) :
    (lift g).evaluate (lift_valid g hg) (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w=g.evaluate hg M w := by
  rw [evaluate_homogeneous]
  have h:=((lift g).underlyingIncidenceEquiv (lift_valid g hg)).partition M w
  have hc (a b : GraphCode) (ha : a.Valid) (hb : b.Valid) (he : a=b) :
      a.evaluate ha M w=b.evaluate hb M w := by subst b; rfl
  exact h.symm.trans (hc _ _ _ hg (lift_underlying g))

end PlanarHom.ZeroOneMixedMembership
