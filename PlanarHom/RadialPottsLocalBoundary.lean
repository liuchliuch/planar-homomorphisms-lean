import PlanarHom.RadialPottsSwitchConnectivity
import PlanarHom.RadialPottsAssembly

/-! NEW reconstruction: a uniform two-state local boundary interface, derived
from the full red/blue connectivity proofs. Every local component has exactly
its two displayed ports and every interior vertex reaches the first port. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPottsTile.OnionBoundary
open MultiGraph RadialPotts.Assembly

def localGraph (k : ℕ) (choice : Bool) := if choice then blueGraph k else switchedRedGraph k

def localComponent {k : ℕ} (choice : Bool) (v : RadialPottsTile.Vertex k) : Component k :=
  if choice then component ((rotateVertex k).symm v) else component v

def sourcePort {k : ℕ} (choice : Bool) (p : Component k) : Port k :=
  (if choice then rotateSide ⟨2*p.1.val,by have := p.1.isLt; omega⟩
    else ⟨2*p.1.val,by have := p.1.isLt; omega⟩,p.2)

def targetPort {k : ℕ} (choice : Bool) (p : Component k) : Port k :=
  (if choice then rotateSide ⟨2*p.1.val+1,by have := p.1.isLt; omega⟩
    else ⟨2*p.1.val+1,by have := p.1.isLt; omega⟩,reverseLane p.2)

theorem local_connected_iff {k : ℕ} (choice : Bool) (u v : RadialPottsTile.Vertex k) :
    (localGraph k choice).componentSetoid Finset.univ u v ↔ localComponent choice u=localComponent choice v := by
  cases choice
  · exact switched_red_connected_iff u v
  · exact blue_connected_iff u v

@[simp] theorem localComponent_source {k : ℕ} (choice : Bool) (p : Component k) :
    localComponent choice (.inr (sourcePort choice p))=p := by
  cases choice
  · exact component_canonicalPort p
  · change component ((rotateVertex k).symm ((rotateVertex k) (canonicalPort p)))=p
    rw [Equiv.symm_apply_apply,component_canonicalPort]

private theorem component_target_red {k : ℕ} (p : Component k) :
    component (.inr (targetPort false p))=p := by
  rcases p with ⟨c,a⟩
  have ha := a.isLt
  fin_cases c <;> apply Prod.ext <;> apply Fin.ext <;>
    simp [component,targetPort,reverseLane] <;> omega

@[simp] theorem localComponent_target {k : ℕ} (choice : Bool) (p : Component k) :
    localComponent choice (.inr (targetPort choice p))=p := by
  cases choice
  · exact component_target_red p
  · change component ((rotateVertex k).symm ((rotateVertex k) (.inr (targetPort false p))))=p
    rw [Equiv.symm_apply_apply]
    exact component_target_red p

private theorem red_port_cases {k : ℕ} (p : Port k) :
    p=sourcePort false (localComponent false (.inr p)) ∨ p=targetPort false (localComponent false (.inr p)) := by
  rcases p with ⟨s,a⟩
  have ha := a.isLt
  fin_cases s
  all_goals first
    | (left; apply Prod.ext <;> apply Fin.ext <;> simp [sourcePort,localComponent,component] <;> omega)
    | (right; apply Prod.ext <;> apply Fin.ext <;> simp [targetPort,localComponent,component,reverseLane] <;> omega)

/-- The component has precisely the two explicit boundary ports. -/
theorem local_port_cases {k : ℕ} (choice : Bool) (p : Port k) :
    p=sourcePort choice (localComponent choice (.inr p)) ∨
      p=targetPort choice (localComponent choice (.inr p)) := by
  cases choice
  · exact red_port_cases p
  · have h := red_port_cases (rotateSide.symm p.1,p.2)
    rcases h with h | h
    · left
      have he := congrArg (fun r : Port k => (rotateSide r.1,r.2)) h
      simpa [sourcePort,localComponent,rotateVertex_symm_port] using he
    · right
      have he := congrArg (fun r : Port k => (rotateSide r.1,r.2)) h
      simpa [targetPort,localComponent,rotateVertex_symm_port] using he

/-- No interior-only component is left over. -/
theorem local_vertex_to_source {k : ℕ} (choice : Bool) (v : RadialPottsTile.Vertex k) :
    (localGraph k choice).componentSetoid Finset.univ v
      (.inr (sourcePort choice (localComponent choice v))) := by
  apply (local_connected_iff choice _ _).mpr
  rw [localComponent_source]

theorem local_port_pair {k : ℕ} (choice : Bool) (p : Component k) :
    (localGraph k choice).componentSetoid Finset.univ (.inr (sourcePort choice p)) (.inr (targetPort choice p)) := by
  apply (local_connected_iff choice _ _).mpr
  rw [localComponent_source,localComponent_target]
end PlanarHom.RadialPottsTile.OnionBoundary
