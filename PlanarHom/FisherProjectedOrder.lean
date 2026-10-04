import PlanarHom.FisherIncidenceOrdering
import PlanarHom.PlanarRadialTails
import Mathlib.Data.Finset.Sort

/-! An incidence ordering derived from actual separated geometric ports.
The ordering is strictly monotone under a generic linear projection, which
is the geometric property used to build noncrossing local paths. -/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.Fisher
open MultiGraph

def linearProjection (a : ℝ) (p : Plane) : ℝ := p.1 + a * p.2

/-- A finite collection of distinct plane points has an injective linear
projection. The finite forbidden slopes are explicitly identified. -/
theorem exists_injective_linearProjection {T : Type*} [Fintype T]
    (p : T → Plane) (hp : Function.Injective p) :
    ∃ a : ℝ, Function.Injective (fun t => linearProjection a (p t)) := by
  let bad : Finset ℝ := Finset.univ.image (fun t : T × T =>
    ((p t.2).1 - (p t.1).1) / ((p t.1).2 - (p t.2).2))
  obtain ⟨a, ha⟩ := bad.exists_notMem
  refine ⟨a, ?_⟩
  intro u v h
  apply hp
  by_cases hy : (p u).2 = (p v).2
  · apply Prod.ext
    · dsimp [linearProjection] at h
      rw [hy] at h
      linarith
    · exact hy
  · have hd : (p u).2 - (p v).2 ≠ 0 := sub_ne_zero.mpr hy
    have he : a = ((p v).1 - (p u).1) / ((p u).2 - (p v).2) := by
      apply (eq_div_iff hd).mpr
      dsimp [linearProjection] at h
      nlinarith
    exact (ha (Finset.mem_image.mpr ⟨(u,v), Finset.mem_univ _, he.symm⟩)).elim

/-- A strictly increasing enumeration of an arbitrary finite injectively
projected point family, derived through the induced linear order. -/
def increasingEnumeration {T : Type*} [Fintype T] (f : T → ℝ)
    (hf : Function.Injective f) : Fin (Fintype.card T) ≃ T := by
  letI : LinearOrder T := LinearOrder.lift' f hf
  exact (Fintype.orderIsoFinOfCardEq T rfl).toEquiv

theorem increasingEnumeration_strictMono {T : Type*} [Fintype T] (f : T → ℝ)
    (hf : Function.Injective f) : StrictMono (fun i => f (increasingEnumeration f hf i)) := by
  letI : LinearOrder T := LinearOrder.lift' f hf
  exact (Fintype.orderIsoFinOfCardEq T rfl).strictMono

variable {V E : Type*} [Fintype E] {G : MultiGraph V E}

/-- The ordering induced by one actual injectively projected endpoint family. -/
def projectedIncidenceOrdering (port : E × Bool → Plane) (a : ℝ)
    (hinj : Function.Injective (fun d => linearProjection a (port d))) :
    G.IncidenceOrdering where
  degree v := Fintype.card (G.VertexDarts v)
  atVertex v := increasingEnumeration (fun d : G.VertexDarts v => linearProjection a (port d.1))
    (fun _ _ h => Subtype.ext (hinj h))

theorem projectedIncidenceOrdering_strictMono (port : E × Bool → Plane) (a : ℝ)
    (hinj : Function.Injective (fun d => linearProjection a (port d))) (v : V) :
    StrictMono (fun i => linearProjection a
      (port ((projectedIncidenceOrdering (G := G) port a hinj).darts ⟨v,i⟩))) := by
  simpa [projectedIncidenceOrdering, IncidenceOrdering.darts] using
    increasingEnumeration_strictMono
      (fun d : G.VertexDarts v => linearProjection a (port d.1))
      (fun _ _ h => Subtype.ext (hinj h))

/-- The needed geometric order exists for the real ports obtained by trimming
an ordinary drawing. This is not an arbitrary combinatorial rotation. -/
theorem exists_projected_incidenceOrdering {d : PlaneDrawing G} {r : ℝ}
    (T : d.Trimming r) :
    ∃ a : ℝ, ∃ o : G.IncidenceOrdering,
      ∀ v, StrictMono (fun i => linearProjection a (T.port (o.darts ⟨v,i⟩))) := by
  obtain ⟨a, ha⟩ := exists_injective_linearProjection T.port T.port_injective
  exact ⟨a, projectedIncidenceOrdering T.port a ha,
    projectedIncidenceOrdering_strictMono T.port a ha⟩

end PlanarHom.Fisher
