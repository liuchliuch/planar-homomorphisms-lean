import PlanarHom.OccurrenceKasteleynPeeling

/-!
NEW compatibility adaptation: recovered source body is retained except for the
explicit `root` argument in the final Peelable subset application. This is an
elaboration adjustment to the reconstructed explicit subset binder.

# Dual connectivity supplies all finite face pivots

A literal edge has two incident face labels, which may coincide at a bridge.
The only boundary compatibility axiom is its occurrence-count parity. Dual
connectivity then proves the cut property used by the actual peeling program.
No orientation or matching-sign theorem is assumed by this interface.

The data here are a finite dual incidence table, not a definition of planarity:
ordinary drawings, finite face boundaries, genus zero, and the later
alternating-cycle sign theorem remain separate geometric obligations.
-/

namespace PlanarHom.MultiGraph.Kasteleyn

variable {F E : Type*} [DecidableEq F] [DecidableEq E]

/-- Both sides of every actual edge occurrence. Bridges have equal face labels;
parallel edges have separate entries, even if their endpoints coincide. -/
structure DualIncidence (F E : Type*) where
  left : E → F
  right : E → F

/-- Undirected adjacency in the literal dual multigraph. Self-adjacencies are
harmless and cannot cross any cut. -/
def DualIncidence.Adj (D : DualIncidence F E) (u v : F) : Prop :=
  ∃ e, (D.left e = u ∧ D.right e = v) ∨ (D.left e = v ∧ D.right e = u)

/-- Boundary parity is derived from the two sides of an occurrence; repeated
opposite traversals of a bridge therefore have even incidence in its face. -/
def DualIncidence.Compatible (D : DualIncidence F E) (boundary : Boundaries F E) : Prop :=
  ∀ e f, incidenceParity e (boundary f) =
    (decide (D.left e = f) ^^ decide (D.right e = f))

/-- Every dual face can be reached from the distinguished exterior face. -/
def DualIncidence.RootedConnected (D : DualIncidence F E) (root : F) : Prop :=
  ∀ f, Relation.ReflTransGen D.Adj root f

/-- Any path from outside a finite face collection to inside crosses its cut.
This argument uses reachability only, not geometric separation or Jordan curves. -/
theorem reach_crosses_cut (R : F → F → Prop) (fs : List F) (root f : F)
    (h : Relation.ReflTransGen R root f) (hr : root ∉ fs) (hf : f ∈ fs) :
    ∃ u v, u ∉ fs ∧ v ∈ fs ∧ R u v := by
  induction h with
  | refl => exact (hr hf).elim
  | @tail b c hab hbc ih =>
    by_cases hb : b ∈ fs
    · exact ih hb
    · exact ⟨b,c,hb,hf,hbc⟩

/-- Connected dual data force an exclusive pivot for every nonempty collection
that omits the exterior face. The program finds it by scanning the boundaries. -/
theorem DualIncidence.hasPivot (D : DualIncidence F E) (boundary : Boundaries F E)
    (hc : D.Compatible boundary) (root : F) (hconn : D.RootedConnected root)
    (fs : List F) (hr : root ∉ fs) (hne : fs ≠ []) : HasPivot boundary fs := by
  obtain ⟨f,hf⟩ := List.exists_mem_of_ne_nil fs hne
  obtain ⟨u,v,hu,hv,e,hedge⟩ := reach_crosses_cut D.Adj fs root f (hconn f) hr hf
  have huv : u ≠ v := fun h => hu (h ▸ hv)
  refine ⟨v,hv,e,?_,?_⟩
  · rw [hc e v]
    rcases hedge with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;> simp [hl,hr,huv,huv.symm]
  · intro g hg hgv
    have hug : u ≠ g := fun h => hu (h ▸ hg)
    rw [hc e g]
    rcases hedge with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;>
      simp [hl,hr,hug,hgv.symm]

/-- Local form suitable for numeric encodings: only the represented face labels
need be reachable. Unused natural-number labels need no artificial dual edges. -/
theorem DualIncidence.hasPivot_of_reachable (D : DualIncidence F E)
    (boundary : Boundaries F E) (hc : D.Compatible boundary) (root : F)
    (fs : List F) (hconn : ∀ f ∈ fs, Relation.ReflTransGen D.Adj root f)
    (hr : root ∉ fs) (hne : fs ≠ []) : HasPivot boundary fs := by
  obtain ⟨f,hf⟩ := List.exists_mem_of_ne_nil fs hne
  obtain ⟨u,v,hu,hv,e,hedge⟩ := reach_crosses_cut D.Adj fs root f (hconn f hf) hr hf
  have huv : u ≠ v := fun h => hu (h ▸ hv)
  refine ⟨v,hv,e,?_,?_⟩
  · rw [hc e v]
    rcases hedge with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;> simp [hl,hr,huv]
  · intro g hg hgv
    have hug : u ≠ g := fun h => hu (h ▸ hg)
    rw [hc e g]
    rcases hedge with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;> simp [hl,hr,hug,hgv.symm]

/-- The finite-table connectivity hypothesis is inherited by every residual
list considered by the actual peeling program. -/
theorem DualIncidence.peelable_of_reachable (D : DualIncidence F E)
    (boundary : Boundaries F E) (hc : D.Compatible boundary) (root : F)
    (fs : List F) (hconn : ∀ f ∈ fs, Relation.ReflTransGen D.Adj root f)
    (hr : root ∉ fs) : Peelable boundary fs := by
  intro us hsub hne
  exact D.hasPivot_of_reachable boundary hc root us
    (fun f hf => hconn f (hsub f hf)) (fun h => hr (hsub root h)) hne

/-- The cut invariant required by recursive peeling follows from plain dual
connectivity and the incidence parity of literal boundary lists. -/
theorem DualIncidence.peelable (D : DualIncidence F E)
    (boundary : Boundaries F E) (hc : D.Compatible boundary)
    (root : F) (hconn : D.RootedConnected root) (fs : List F)
    (hr : root ∉ fs) : Peelable boundary fs := by
  intro us hsub hne
  exact D.hasPivot boundary hc root hconn us (fun h => hr (hsub root h)) hne

/-- Fully computed clockwise-odd orientation on all listed non-exterior faces.
The list may be empty, so isolated-vertex and edgeless drawings need no special
orientation witness. This theorem assumes no solved orientation or pivot order. -/
theorem DualIncidence.orientFaces_correct (D : DualIncidence F E)
    (boundary : Boundaries F E) (hc : D.Compatible boundary)
    (root : F) (hconn : D.RootedConnected root) (fs : List F)
    (hn : fs.Nodup) (hr : root ∉ fs) (initial : E → Bool) :
    ∀ f ∈ fs, FaceOdd (orientFaces boundary fs initial) (boundary f) :=
  Kasteleyn.orientFaces_correct boundary fs hn
    (D.peelable boundary hc root hconn fs hr) initial

/-- A primal bridge cannot be selected as an odd-incidence face pivot. This is
proved from its equal dual endpoints rather than suppressing its repeated darts. -/
theorem DualIncidence.bridge_even (D : DualIncidence F E) (boundary : Boundaries F E)
    (hc : D.Compatible boundary) (e : E) (he : D.left e = D.right e) (f : F) :
    incidenceParity e (boundary f) = false := by rw [hc e f,he]; simp

end PlanarHom.MultiGraph.Kasteleyn
