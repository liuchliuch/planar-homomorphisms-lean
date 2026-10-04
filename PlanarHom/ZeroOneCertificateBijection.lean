import PlanarHom.ZeroOneHomCertificates

/-! NEW parsimonious certificate semantics. Accepted fixed-length binary
words correspond bijectively to literal vertex color assignments satisfying
every original edge occurrence; padding contributes no multiplicity. -/
noncomputable section
open Classical
namespace PlanarHom.ZeroOneSharpPMembership
open Complexity

abbrev Certificate (q:ℕ) (R:Relation q) (g:GraphCode) (L:ℕ) :=
  {w:Fin (L*q)→Bool // verifyGraph q R g (List.ofFn w)=true}

def certificateColor {q L:ℕ} {R:Relation q} {g:GraphCode} (w:Certificate q R g L) : Fin g.vertices→Fin q :=
  fun v=>Classical.choose (((verifyGraph_true q R g _).mp w.property).2.1 v.val v.isLt)

theorem certificateColor_matches {q L:ℕ} {R:Relation q} {g:GraphCode}
    (w:Certificate q R g L) (v:Fin g.vertices) :
    Matches q (List.ofFn w.val) v.val (certificateColor w v) :=
  Classical.choose_spec (((verifyGraph_true q R g _).mp w.property).2.1 v.val v.isLt)

theorem certificateColor_hom {q L:ℕ} {R:Relation q} {g:GraphCode} (hg:g.Valid)
    (w:Certificate q R g L) : IsHom q R g hg (certificateColor w) := by
  intro e
  obtain ⟨c,d,hc,hd,hr⟩:=((verifyGraph_true q R g _).mp w.property).2.2.1 (g.edges.get e) (List.get_mem _ _)
  have hsrc:=matches_unique (certificateColor_matches w ((g.toMultiGraph hg).src e)) hc
  have hdst:=matches_unique (certificateColor_matches w ((g.toMultiGraph hg).dst e)) hd
  simpa only [hsrc,hdst] using hr

theorem verify_padded {q L:ℕ} {R:Relation q} {g:GraphCode} (hg:g.Valid)
    (hL:g.vertices≤L) (c:Hom q R g hg) :
    verifyGraph q R g (List.ofFn (paddedWord c.val L))=true := by
  apply (verifyGraph_true q R g _).mpr
  refine ⟨hg,?_,?_,(padding_true _ _ _).mp (paddedWord_padding c.val)⟩
  · intro v hv
    exact ⟨c.val ⟨v,hv⟩,paddedWord_matches c.val hL ⟨v,hv⟩⟩
  · intro e he
    obtain ⟨i,rfl⟩:=List.mem_iff_get.mp he
    refine ⟨c.val ((g.toMultiGraph hg).src i),c.val ((g.toMultiGraph hg).dst i),
      paddedWord_matches c.val hL ((g.toMultiGraph hg).src i),
      paddedWord_matches c.val hL ((g.toMultiGraph hg).dst i),c.property i⟩

theorem reconstruct_certificate {q L:ℕ} {R:Relation q} {g:GraphCode}
    (w:Certificate q R g L) : paddedWord (certificateColor w) L=w.val := by
  funext k
  by_cases hk:k.val<g.vertices*q
  · let p:Fin g.vertices×Fin q:=finProdFinEquiv.symm ⟨k.val,hk⟩
    have hp:finProdFinEquiv p=(⟨k.val,hk⟩:Fin (g.vertices*q)) := finProdFinEquiv.apply_symm_apply _
    have hv:k.val=q*p.1.val+p.2.val := by
      have h:=congrArg Fin.val hp
      simp only [finProdFinEquiv,Equiv.coe_fn_mk] at h
      omega
    have hm:=certificateColor_matches w p.1 p.2
    rw [←hv,getBit_ofFn _ _ k.isLt] at hm
    change w.val k=decide (certificateColor w p.1=p.2) at hm
    simpa only [paddedWord,dif_pos hk,oneHotWord,p] using hm.symm
  · have hm:=((verifyGraph_true q R g _).mp w.property).2.2.2 k.val (by simpa using k.isLt) (by omega)
    rw [getBit_ofFn _ _ k.isLt] at hm
    simpa only [paddedWord,dif_neg hk] using hm.symm

def certificateEquiv (q:ℕ) (R:Relation q) (g:GraphCode) (hg:g.Valid) (L:ℕ) (hL:g.vertices≤L) :
    Certificate q R g L ≃ Hom q R g hg where
  toFun w:=⟨certificateColor w,certificateColor_hom hg w⟩
  invFun c:=⟨paddedWord c.val L,verify_padded hg hL c⟩
  left_inv w:=Subtype.ext (reconstruct_certificate w)
  right_inv c:=by
    apply Subtype.ext
    funext v
    exact matches_unique (certificateColor_matches ⟨paddedWord c.val L,verify_padded hg hL c⟩ v)
      (paddedWord_matches c.val hL v)

theorem certificate_card (q:ℕ) (R:Relation q) (g:GraphCode) (hg:g.Valid) (L:ℕ) (hL:g.vertices≤L) :
    Fintype.card (Certificate q R g L)=count q R g hg :=
  Fintype.card_congr (certificateEquiv q R g hg L hL)
end PlanarHom.ZeroOneSharpPMembership
