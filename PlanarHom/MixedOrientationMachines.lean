import PlanarHom.MixedOrientationMetadata
import PlanarHom.PlanarityLRPrimitiveMachines

noncomputable section
open Classical
namespace PlanarHom.MixedOrientation
open Complexity Complexity.MixedCode PrescribedDomains PairProjectionMachines ArithmeticCircuitPrimitives
variable {b u:ℕ}

abbrev unaryEncoding := BitEncoding.nat.prod BitEncoding.nat

def rootTest (u:ℕ) (a:ℕ×ℕ) : Bool := decide (a.1=0 ∧ u≤a.2)
def rootSide (u:ℕ) (g:MixedCode) : Bool := decide (((g.unaries.filter (rootTest u)).headD (0,u)).2=u+1)

theorem fp_strip (u:ℕ) : FP MixedCode.encoding MixedCode.encoding (strip u) := by
  have hle:=((fp_const unaryEncoding BitEncoding.nat u).pair (fp_snd BitEncoding.nat BitEncoding.nat)).comp
    PlanarityLRRawConstraints.fp_le
  have ht:FP unaryEncoding BitEncoding.bool (fun a=>decide (a.2<u)):=
    (hle.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr (fun a=>by
      change Bool.not (decide (u≤a.2)) = decide (a.2<u)
      by_cases h:a.2<u
      · simp [h,Nat.not_le.mpr h]
      · simp [h,Nat.le_of_not_gt h])
  have hu:=MixedCode.fp_unaries.comp (ListFilterMachines.fp_filter unaryEncoding _ ht)
  exact (MixedCode.fp_vertices.pair (MixedCode.fp_edges.pair hu)).transportOutput (fun _=>rfl)

theorem fp_rootTest (u:ℕ) : FP unaryEncoding BitEncoding.bool (rootTest u) := by
  have hv:=((fp_fst BitEncoding.nat BitEncoding.nat).pair (fp_const unaryEncoding BitEncoding.nat 0)).comp
    NatListSumMachines.fp_equal
  have hl:=((fp_const unaryEncoding BitEncoding.nat u).pair (fp_snd BitEncoding.nat BitEncoding.nat)).comp
    PlanarityLRRawConstraints.fp_le
  exact ((hv.pair hl).comp (fp_bool_gate (fun p=>p.1&&p.2))).congr (fun a=>by simp [rootTest])

theorem fp_rootSide (u:ℕ) : FP MixedCode.encoding BitEncoding.bool (rootSide u) := by
  have hf:=MixedCode.fp_unaries.comp (ListFilterMachines.fp_filter unaryEncoding _ (fp_rootTest u))
  have hl:=(hf.comp (ListDecompositionMachines.fp_headD unaryEncoding (0,u))).comp (fp_snd BitEncoding.nat BitEncoding.nat)
  exact (hl.pair (fp_const _ BitEncoding.nat (u+1))).comp NatListSumMachines.fp_equal

theorem rootSide_tags (g:MixedCode) (δ:Fin g.vertices→Fin 2) (ht:Tags u g δ) (hn:0<g.vertices) :
    rootSide u g=decide (δ ⟨0,hn⟩=1) := by
  have hp:=ht.filter (rootTest u)
  have ho:((strip u g).unaries.filter (rootTest u))=[]:=by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hl: a.2<u:=of_decide_eq_true (List.mem_filter.mp ha).2
    simp [rootTest,show ¬u≤a.2 by omega]
  have hd:((domainOccurrences (unaryTypes:=u) g δ).filter (rootTest u)).Perm [(0,u+(δ ⟨0,hn⟩).val)] := by
    apply (List.perm_ext_iff_of_nodup ((domains_nodup g δ).filter _) (List.nodup_singleton _)).mpr
    intro a
    simp only [List.mem_filter,domainOccurrences,List.mem_ofFn,List.mem_singleton]
    constructor
    · rintro ⟨⟨v,rfl⟩,hv⟩
      have hz:v.val=0:=(of_decide_eq_true hv).1
      have he:v=⟨0,hn⟩:=Fin.ext hz
      subst v
      rfl
    · intro ha
      subst a
      exact ⟨⟨⟨0,hn⟩,rfl⟩,by simp [rootTest]⟩
  simp only [List.filter_append,ho,List.nil_append] at hp
  have he:=List.perm_singleton.mp (hp.trans hd)
  rw [rootSide,he]
  simp only [List.headD_cons,Nat.add_right_inj]
  congr 1
  exact propext ⟨fun h=>Fin.ext h,fun h=>congrArg Fin.val h⟩

def prepareSides {s₀ s₁:ℕ} (graphs₀:Fin s₀→FiniteMixedRooted b u)
    (graphs₁:Fin s₁→FiniteMixedRooted b u) (g:MixedCode) : Bool×List MixedCode :=
  (rootSide u g,if rootSide u g then (FixedRealMixedRootRestriction.prepare graphs₁ (0,strip u g)).2
    else (FixedRealMixedRootRestriction.prepare graphs₀ (0,strip u g)).2)

theorem fp_prepareSides {s₀ s₁:ℕ} (graphs₀:Fin s₀→FiniteMixedRooted b u)
    (graphs₁:Fin s₁→FiniteMixedRooted b u) :
    FP MixedCode.encoding (BitEncoding.bool.prod MixedCode.encoding.list) (prepareSides graphs₀ graphs₁) := by
  have hg:=(fp_const MixedCode.encoding BitEncoding.nat 0).pair (fp_strip u)
  have h₀:=(hg.comp (FixedRealMixedRootRestriction.fp_prepare graphs₀)).comp
    (fp_snd BitEncoding.nat MixedCode.encoding.list)
  have h₁:=(hg.comp (FixedRealMixedRootRestriction.fp_prepare graphs₁)).comp
    (fp_snd BitEncoding.nat MixedCode.encoding.list)
  exact ((fp_rootSide u).pair ((fp_rootSide u).ite h₁ h₀)).congr (fun g=>by simp only [Function.comp_apply,prepareSides,rootSide,decide_eq_true_eq])

end PlanarHom.MixedOrientation
