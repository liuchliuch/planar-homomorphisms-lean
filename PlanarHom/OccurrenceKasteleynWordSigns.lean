import PlanarHom.OccurrenceKasteleynWordBase
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
variable {V : Type*} [LinearOrder V]

theorem orientedPairSign_exchange (a b c d : V) (ps : List (V × V))
    (hn:(pairWord ((a,b)::(c,d)::ps)).Nodup) :
    orientedPairSign ((a,b)::(c,d)::ps)=orientedPairSign ((a,d)::(b,c)::ps) := by
  have hh : a≠b ∧ a≠c ∧ a≠d ∧ a∉pairWord ps ∧ b≠c ∧ b≠d ∧
      b∉pairWord ps ∧ c≠d ∧ c∉pairWord ps ∧ d∉pairWord ps ∧ (pairWord ps).Nodup := by
    simp only [pairWord_cons,List.nodup_cons,List.mem_cons,not_or] at hn
    tauto
  have hordered : ∀q∈(ps.map normalizePair).toFinset,q.1<q.2 := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    simpa [normalizePair] using (pairWord_nodup_endpoints hh.2.2.2.2.2.2.2.2.2.2 hp).symm
  have hav : ∀q∈(ps.map normalizePair).toFinset,
      (q.1≠a ∧ q.1≠c ∧ q.1≠b ∧ q.1≠d) ∧ (q.2≠a ∧ q.2≠c ∧ q.2≠b ∧ q.2≠d) := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have h1:=fst_mem_pairWord hp
    have h2:=snd_mem_pairWord hp
    have hm : ∀x∈pairWord ps,x≠a ∧ x≠c ∧ x≠b ∧ x≠d := by
      intro x hx
      exact ⟨fun h=>hh.2.2.2.1 (h ▸ hx),fun h=>hh.2.2.2.2.2.2.2.2.1 (h ▸ hx),
        fun h=>hh.2.2.2.2.2.2.1 (h ▸ hx),fun h=>hh.2.2.2.2.2.2.2.2.2.1 (h ▸ hx)⟩
    rcases le_total p.1 p.2 with h|h
    · simpa [normalizePair,min_eq_left h,max_eq_right h] using And.intro (hm _ h1) (hm _ h2)
    · simpa [normalizePair,min_eq_right h,max_eq_left h] using And.intro (hm _ h2) (hm _ h1)
  have hx := pairingSign_exchange_partners (ps.map normalizePair).toFinset a c b d
    hh.2.1 hh.1 hh.2.2.1 hh.2.2.2.2.1.symm hh.2.2.2.2.2.2.2.1 hh.2.2.2.2.2.1 hordered hav
  have hr := orderSign_reverse hh.2.2.2.2.1
  simp only [orientedPairSign,List.map_cons,List.toFinset_cons,List.prod_cons,
    normalizePair_eq_ordered,orderSign] at hr ⊢
  have hp : orderedEndpointPair c b=orderedEndpointPair b c := by
    rw [←normalizePair_eq_ordered,←normalizePair_eq_ordered,normalizePair_reverse]
  rw [hr,hp] at hx
  nlinarith [congrArg (fun z=> z*(ps.map (fun p=>endpointOrderSign p.1 p.2)).prod) hx]

/-- Pairing the one-place left shift of the endpoint word. -/
def rotatePairs (a b : V) : List (V×V) → List (V×V)
  | [] => [(b,a)]
  | (c,d)::ps => (b,c)::rotatePairs a d ps
@[simp] theorem pairWord_rotatePairs (a b : V) (ps : List (V×V)) :
    pairWord (rotatePairs a b ps)=b::(pairWord ps++[a]) := by
  induction ps generalizing b with
  | nil => rfl
  | cons p ps ih => simp [rotatePairs,ih]

theorem orientedPairSign_rotate (a b : V) (ps common : List (V×V))
    (hn:(pairWord (((a,b)::ps)++common)).Nodup) :
    orientedPairSign (((a,b)::ps)++common) =
      -orientedPairSign (rotatePairs a b ps++common) := by
  induction ps generalizing b common with
  | nil =>
    have hab : a≠b := pairWord_nodup_endpoints (p:=(a,b)) hn (by simp)
    simpa [rotatePairs] using congrArg Neg.neg (orientedPairSign_reverse a b common hab).symm
  | cons p ps ih =>
    rcases p with ⟨c,d⟩
    have hx := orientedPairSign_exchange a b c d (ps++common) (by simpa using hn)
    have hp : ((a,d)::(b,c)::(ps++common)).Perm (((a,d)::ps)++((b,c)::common)) := by
      simpa only [List.cons_append] using List.Perm.cons (a,d) (List.perm_middle.symm : ((b,c)::(ps++common)).Perm (ps++(b,c)::common))
    have hn' : (pairWord (((a,d)::ps)++((b,c)::common))).Nodup := by
      have hpw : (pairWord ps ++ [b,c] ++ pairWord common).Perm
          ([b,c] ++ pairWord ps ++ pairWord common) :=
        List.Perm.append_right _ List.perm_append_comm
      have hm : (d::b::c::(pairWord ps++pairWord common)).Perm
          (b::c::d::(pairWord ps++pairWord common)) := by
        exact (List.perm_middle (a:=d) (l₁:=[b,c]) (l₂:=pairWord ps++pairWord common)).symm
      simp only [List.cons_append,List.nil_append,List.append_assoc] at hpw
      have hw := List.Perm.cons a ((List.Perm.cons d hpw).trans hm)
      simp only [pairWord_append,pairWord_cons,List.cons_append]
      apply hw.nodup_iff.mpr
      simpa only [pairWord_append,pairWord_cons,List.cons_append] using hn
    have hi := ih d ((b,c)::common) hn'
    have hq : (rotatePairs a d ps++(b,c)::common).Perm ((b,c)::(rotatePairs a d ps++common)) := List.perm_middle
    rw [List.cons_append,List.cons_append,hx,orientedPairSign_perm hp,hi,
      orientedPairSign_perm hq]
    rfl

/-- The literal oriented sign changes by minus under a one-place rotation of
an even, distinct endpoint word, with any disjoint common matching retained. -/
theorem orientedPairSign_rotate_word (ps qs common : List (V×V)) (a : V) (rest : List V)
    (hl : pairWord ps=a::rest) (hr : pairWord qs=rest++[a])
    (hn : (pairWord (ps++common)).Nodup) :
    orientedPairSign (ps++common) = -orientedPairSign (qs++common) := by
  cases ps with
  | nil => simp at hl
  | cons p ps =>
    rcases p with ⟨x,y⟩
    have hh : x=a ∧ y::pairWord ps=rest := by simpa using hl
    obtain ⟨hxa,hrst⟩ := hh
    subst x
    subst rest
    have hq : qs=rotatePairs a y ps := by
      have hword : pairWord qs=pairWord (rotatePairs a y ps) := by
        simpa using hr
      simpa only [pairChunks_pairWord] using congrArg pairChunks hword
    rw [hq]
    exact orientedPairSign_rotate a y ps common hn

end PlanarHom.MultiGraph
