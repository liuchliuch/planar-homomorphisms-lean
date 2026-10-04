import PlanarHom.Complexity
import PlanarHom.PlanarEmbedding

/-!
# The planar promise for ordinary binary graph inputs

A graph code stores only a unary vertex count and the endpoint-occurrence list.
Planarity is existential over actual plane drawings of its incidence multigraph;
no drawing, rotation system, or ribbon certificate is added to the input. This
module supplies no planarity-recognition machine or bit-complexity claim.
-/

noncomputable section
namespace PlanarHom.Complexity.GraphCode

/-- The finite abstract graph encoded by an endpoint-valid code is planar. -/
def PlanarValid (g : GraphCode) : Prop :=
  ∃ h : g.Valid, (g.toMultiGraph h).Planar

theorem PlanarValid.valid {g : GraphCode} (h : g.PlanarValid) : g.Valid := h.1

/-- Proof irrelevance makes the planar promise independent of which endpoint
validity proof is used to construct the finite incidence graph. -/
theorem planarValid_iff (g : GraphCode) (h : g.Valid) :
    g.PlanarValid ↔ (g.toMultiGraph h).Planar := by
  constructor
  · rintro ⟨h',hp⟩
    exact hp
  · exact fun hp => ⟨h,hp⟩

/-- The bit-level promise checks a decoded abstract graph, without requiring an
embedding certificate among the serialized input bits. -/
def PlanarInput (bits : Bits) : Prop :=
  ∃ g : GraphCode, encoding.decode bits = some g ∧ g.PlanarValid

@[simp] theorem planarInput_encode_iff (g : GraphCode) :
    PlanarInput (encoding.encode g) ↔ g.PlanarValid := by
  simp [PlanarInput, encoding.decode_encode]

/-- Malformed binary words cannot be valid planar oracle queries. -/
theorem not_planarInput_of_decode_none {bits : Bits}
    (h : encoding.decode bits = none) : ¬ PlanarInput bits := by
  rintro ⟨g,hg,_⟩
  rw [h] at hg
  cases hg

/-- Supply any separately specified exact bit-valued evaluation semantics. The
promise is the actual raw-code planar promise, not embedded-input planarity. -/
def planarPromise (value : Bits → Bits) : PromiseProblem where
  valid := PlanarInput
  value := value

@[simp] theorem planarPromise_valid (value : Bits → Bits) (bits : Bits) :
    (planarPromise value).valid bits ↔ PlanarInput bits := Iff.rfl

end PlanarHom.Complexity.GraphCode
