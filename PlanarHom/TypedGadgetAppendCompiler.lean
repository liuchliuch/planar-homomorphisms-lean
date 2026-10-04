import PlanarHom.TypedGadgetAppendTyping
import PlanarHom.EdgeGadgetNetworkReduction

/-! An actual finite compiler for arbitrary typed two-terminal templates.
The exact typed-domain promise is preserved, including all retained unaries,
old vertex assignments, loops, isolates, and occurrence multiplicities. -/
noncomputable section
open Classical
namespace PlanarHom.TypedGadgetAppend
open Complexity PrescribedDomains FixedGadgetNetwork EdgeSubstitution
variable {bt ut dt : ℕ}

/-- The endpoint contract is checked separately for every fixed template and
all domain pairs permitted by the target label. -/
def FamilyTyping (ts : List Template)
    (B : Fin bt → Fin dt → Fin dt → Prop)
    (BT : Fin ts.length → Fin dt → Fin dt → Prop) : Prop :=
  ∀ l x y, BT l x y → ∃ tag,TemplateTyping (ut:=ut) B (ts.get l) tag ∧ tag 0=x ∧ tag 1=y

/-- Extend a finite host assignment only for proof bookkeeping. Actual new
vertices get their own template tags, never this arbitrary default. -/
def totalTag {n : ℕ} (δ : Fin n → Fin dt) (fallback : Fin dt) : ℕ → Fin dt :=
  fun v => if h : v<n then δ ⟨v,h⟩ else fallback

@[simp] theorem totalTag_old {n : ℕ} (δ : Fin n → Fin dt) (fallback : Fin dt)
    (v : Fin n) : totalTag δ fallback v.val=δ v := by simp [totalTag]

theorem substitute_encodedGraph (ts : List Template)
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (BT : Fin ts.length → Fin dt → Fin dt → Prop) (fallback : Fin dt)
    (ht : ∀ t∈ts,t.code.Valid bt (ut+dt)) (hb : ∀t∈ts,t.boundary=2)
    (hp : ∀t (h:t∈ts),TwoTerminal.PlanarEdgeGadget (t.edgeGadget (hb t h) (ht t h)))
    (hfamily : FamilyTyping (ut:=ut) ts B BT)
    {g : MixedCode} (hg : EncodedGraph BT T g) :
    EncodedGraph B T (substitute ts g) := by
  obtain ⟨original,hvalid,δ,htyped,hplanar,hdecode⟩ := hg
  rw [MixedCode.encoding.decode_encode] at hdecode
  have he : g=withDomains (unaryTypes:=ut) original δ := Option.some.inj hdecode
  subst g
  let H := withDomains (unaryTypes:=ut) original δ
  let tag := totalTag δ fallback
  have hv : H.Valid ts.length (ut+dt) := withDomains_valid original hvalid δ
  have hn := network_valid ts ht hb H hv
  have hbase : Tagged B T original.unaries (network H).base tag := by
    refine ⟨hn.1,?_,?_,hvalid.2,?_⟩
    · change original.unaries ++ domainOccurrences original δ =
        original.unaries ++ domains ut original.vertices tag
      congr 1
      apply List.ext_getElem
      · simp [domainOccurrences,domains]
      · intro i hi hj
        have hi' : i<original.vertices := by simpa [domainOccurrences] using hi
        simp [domainOccurrences,domains,tag,totalTag,hi']
    · simp [network]
    · intro u hu
      simpa only [tag,totalTag,dif_pos (hvalid.2 u hu).1] using htyped.2 u hu
  have htags : ∀ a∈(network H).gates,∃ fresh,
      TemplateTyping (ut:=ut) B (gateTemplate ts a) fresh ∧
        ∀v,v<(gateTemplate ts a).boundary → tag (a.2.getD v 0)=fresh v := by
    intro a ha
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
    have hev := hvalid.1 e he
    let l : Fin ts.length := ⟨e.2.2,hev.2.2⟩
    obtain ⟨fresh,hfresh,hs,hd⟩ := hfamily l (δ ⟨e.1,hev.1⟩) (δ ⟨e.2.1,hev.2.1⟩)
      (htyped.1 e he)
    have hget : gateTemplate ts (gate e)=ts.get l := by
      exact List.getD_eq_getElem ts emptyTemplate hev.2.2
    refine ⟨fresh,by rwa [hget],?_⟩
    intro v hv'
    have htwo : (gateTemplate ts (gate e)).boundary=2 := by
      rw [hget]
      exact hb _ (List.get_mem _ _)
    have hv2 : v=0 ∨ v=1 := by omega
    rcases hv2 with rfl|rfl
    · simpa only [gate,List.getD_cons_zero,tag,totalTag,dif_pos hev.1] using hs.symm
    · simpa only [gate,List.getD_cons_succ,List.getD_cons_zero,tag,totalTag,dif_pos hev.2.1] using hd.symm
  obtain ⟨out,hout,_⟩ := compile_tagged ts B T original.unaries original.vertices tag
    (network H).gates hn.2.2 htags (network H).base tag hbase (by rfl) (by intros; rfl)
  exact hout.encodedGraph (substitute_planarValid ts ht hb hp H ⟨hv,hplanar⟩).2

/-- Promise preservation applies to every successfully decoded raw input,
without silently imposing a canonical encoding on the target oracle. -/
theorem substitute_encodedInput (ts : List Template)
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (BT : Fin ts.length → Fin dt → Fin dt → Prop) (fallback : Fin dt)
    (ht : ∀ t∈ts,t.code.Valid bt (ut+dt)) (hb : ∀t∈ts,t.boundary=2)
    (hp : ∀t (h:t∈ts),TwoTerminal.PlanarEdgeGadget (t.edgeGadget (hb t h) (ht t h)))
    (hfamily : FamilyTyping (ut:=ut) ts B BT)
    (raw : Bits) (g : MixedCode) (hd : MixedCode.encoding.decode raw=some g)
    (hg : EncodedInput BT T raw) :
    EncodedInput B T (MixedCode.encoding.encode (substitute ts g)) := by
  have hgraph : EncodedGraph BT T g :=
    (encodedInput_congr_decode BT T (hd.trans (MixedCode.encoding.decode_encode g).symm)).mp hg
  exact substitute_encodedGraph ts B T BT fallback ht hb hp hfamily hgraph

end PlanarHom.TypedGadgetAppend
