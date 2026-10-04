import PlanarHom.SurfaceRawEmbeddingCode
import PlanarHom.GraphCodeNormalization
import PlanarHom.PromisePolynomialTime

/-! NEW normalization of every successfully decoded supplied-surface raw word.
Complement and rotation lists are parsed by the existing structural machines. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceRawEmbedding
open Complexity

theorem bool_valid_raw (w : BitEncoding.ValidWord BitEncoding.bool) :
    BitEncoding.bool.encode w.value=w.raw := by
  have h := w.decode_raw
  rcases w with ⟨raw,hraw⟩
  cases raw with
  | nil =>
      obtain ⟨a,ha⟩ := hraw
      cases ha
  | cons b tail =>
      cases tail with
      | nil =>
          have hb : b=BitEncoding.ValidWord.value (⟨[b],hraw⟩ : BitEncoding.ValidWord BitEncoding.bool) := by
            exact Option.some.inj h
          change [BitEncoding.ValidWord.value (⟨[b],hraw⟩ : BitEncoding.ValidWord BitEncoding.bool)]=[b]
          rw [←hb]
      | cons c rest =>
          obtain ⟨a,ha⟩ := hraw
          cases ha

def boolNormalizer : BitEncoding.Normalizer BitEncoding.bool :=
  Classical.choice (fp_code_view (BitEncoding.ValidWord.encoding BitEncoding.bool) BitEncoding.bool
    BitEncoding.ValidWord.value bool_valid_raw)

def complementNormalizer : BitEncoding.Normalizer complementCode := by
  apply BitEncoding.retractNormalizer
    (BitEncoding.nat.list.prod (BitEncoding.nat.list.prod BitEncoding.nat.list))
    (fun c:ComplementCode => (c.genera,c.dartRegion,c.isolatedRegion))
    (fun p => ⟨p.1,p.2.1,p.2.2⟩)
    (by intro c;cases c;rfl) (by intro p;rcases p with ⟨a,b,c⟩;rfl)
  exact BitEncoding.prodNormalizer (BitEncoding.listNormalizer BitEncoding.natNormalizer)
    (BitEncoding.prodNormalizer (BitEncoding.listNormalizer BitEncoding.natNormalizer)
      (BitEncoding.listNormalizer BitEncoding.natNormalizer))

def normalizer : BitEncoding.Normalizer inputCode :=
  BitEncoding.prodNormalizer MixedCode.normalizer
    (BitEncoding.prodNormalizer
      (BitEncoding.listNormalizer (BitEncoding.listNormalizer
        (BitEncoding.prodNormalizer BitEncoding.natNormalizer boolNormalizer))) complementNormalizer)

end PlanarHom.SurfaceRawEmbedding
