import PlanarHom.FixedGadgetNetworkMachines

/-! Explicit source-size bounds for all raw networks, without validity promises.
Binary endpoints in arbitrary port lists are charged by their actual bit lengths. -/
namespace PlanarHom.FixedGadgetNetwork
open Complexity ListFlattenMachines

private def natSize (v : ℕ) : ℕ := (BitEncoding.nat.encode v).length
private def portsSize (ps : List ℕ) : ℕ := (BitEncoding.nat.list.encode ps).length

private theorem member_natSize (ps : List ℕ) (v : ℕ) (hv : v∈ps) : natSize v≤portsSize ps := by
  have h := ListMapMachines.mem_le_sum_map natSize hv
  have hp := payloadSize_le_word BitEncoding.nat ps
  rw [payloadSize_eq] at hp
  change 2*(ps.map natSize).sum+ps.length≤portsSize ps at hp
  omega

private theorem getD_natSize (ps : List ℕ) (v : ℕ) : natSize (ps.getD v 0)≤portsSize ps := by
  rw [List.getD_eq_getElem?_getD,List.getD_getElem?]
  split_ifs with hv
  · exact member_natSize ps _ (List.getElem_mem hv)
  · have h := encodeNat_length_le 0
    change natSize 0≤0 at h
    omega

private theorem remapVertex_size (t : Template) (offset : ℕ) (ps : List ℕ) (v : ℕ) :
    natSize (remapVertex t offset ps v)≤offset+portsSize ps+v := by
  unfold remapVertex
  split_ifs
  · exact (getD_natSize ps v).trans (by omega)
  · have h := encodeNat_length_le (offset+(v-t.boundary))
    change natSize (offset+(v-t.boundary))≤offset+(v-t.boundary) at h
    omega

private def edgeCost (e : ℕ × ℕ × ℕ) : ℕ := e.1+e.2.1+e.2.2+1
private def unaryCost (u : ℕ × ℕ) : ℕ := u.1+u.2+1

private theorem edge_size (t : Template) (offset : ℕ) (ps : List ℕ) (e : ℕ × ℕ × ℕ) :
    (edgeItemEncoding.encode (remapEdge t offset ps e)).length ≤
      4*edgeCost e*(offset+portsSize ps+1) := by
  have hs := remapVertex_size t offset ps e.1
  have hd := remapVertex_size t offset ps e.2.1
  have hl := encodeNat_length_le e.2.2
  simp only [edgeItemEncoding,remapEdge,BitEncoding.prod_length]
  change 2*natSize (remapVertex t offset ps e.1)+
    (2*natSize (remapVertex t offset ps e.2.1)+natSize e.2.2+1)+1≤_
  change natSize e.2.2≤e.2.2 at hl
  dsimp only [edgeCost]
  nlinarith

private theorem unary_size (t : Template) (offset : ℕ) (ps : List ℕ) (u : ℕ × ℕ) :
    (unaryItemEncoding.encode (remapUnary t offset ps u)).length ≤
      4*unaryCost u*(offset+portsSize ps+1) := by
  have hv := remapVertex_size t offset ps u.1
  have hl := encodeNat_length_le u.2
  simp only [unaryItemEncoding,remapUnary,BitEncoding.prod_length]
  change 2*natSize (remapVertex t offset ps u.1)+natSize u.2+1≤_
  change natSize u.2≤u.2 at hl
  dsimp only [unaryCost]
  nlinarith

private theorem payloadSize_cons {A : Type} (e : BitEncoding A) (a : A) (as : List A) :
    payloadSize e (a::as)=2*(e.encode a).length+1+payloadSize e as := by
  simp only [payloadSize_eq,List.map_cons,List.sum_cons,List.length_cons]
  omega

private theorem remap_edges_payload (t : Template) (offset : ℕ) (ps : List ℕ)
    (es : List (ℕ × ℕ × ℕ)) :
    payloadSize edgeItemEncoding (es.map (remapEdge t offset ps))≤
      9*(es.map edgeCost).sum*(offset+portsSize ps+1) := by
  induction es with
  | nil => simp [payloadSize,BitEncoding.frames]
  | cons e es ih =>
    have he := edge_size t offset ps e
    have hc : 1≤edgeCost e := by simp [edgeCost]
    simp only [List.map_cons,List.sum_cons,payloadSize_cons]
    nlinarith

private theorem remap_unaries_payload (t : Template) (offset : ℕ) (ps : List ℕ)
    (us : List (ℕ × ℕ)) :
    payloadSize unaryItemEncoding (us.map (remapUnary t offset ps))≤
      9*(us.map unaryCost).sum*(offset+portsSize ps+1) := by
  induction us with
  | nil => simp [payloadSize,BitEncoding.frames]
  | cons u us ih =>
    have hu := unary_size t offset ps u
    have hc : 1≤unaryCost u := by simp [unaryCost]
    simp only [List.map_cons,List.sum_cons,payloadSize_cons]
    nlinarith

/-- A fixed, explicit integer computed only from the family description. -/
def templateCost (t : Template) : ℕ :=
  t.privateCount+9*((t.edges.map edgeCost).sum+(t.unaries.map unaryCost).sum)

def familyCost (ts : List Template) : ℕ := (ts.map templateCost).sum

def contentSize (g : MixedCode) : ℕ :=
  payloadSize edgeItemEncoding g.edges+payloadSize unaryItemEncoding g.unaries

theorem attachTemplate_contentSize (t : Template) (g : MixedCode) (ps : List ℕ) :
    contentSize (attachTemplate t g ps)≤contentSize g+
      templateCost t*(g.vertices+(BitEncoding.nat.list.encode ps).length+1) := by
  have he := remap_edges_payload t g.vertices ps t.edges
  have hu := remap_unaries_payload t g.vertices ps t.unaries
  simp only [contentSize,attachTemplate,payloadSize_append]
  dsimp only [templateCost,portsSize] at *
  nlinarith

theorem gateTemplate_cost (ts : List Template) (a : Gate) :
    templateCost (gateTemplate ts a)≤familyCost ts := by
  by_cases h:a.1<ts.length
  · exact ListMapMachines.mem_le_sum_map templateCost (gateTemplate_mem h)
  · simp [gateTemplate,List.getD_eq_getElem?_getD,h,templateCost,emptyTemplate]

theorem gateTemplate_privateCount (ts : List Template) (a : Gate) :
    (gateTemplate ts a).privateCount≤familyCost ts := by
  have h := gateTemplate_cost ts a
  unfold templateCost at h
  omega

/-- A uniform fold bound with a materialized vertex cap and arbitrary raw ports. -/
theorem compile_contentSize (ts : List Template) (g : MixedCode) (as : List Gate)
    (V P : ℕ) (hv : g.vertices+as.length*familyCost ts≤V)
    (hp : ∀a∈as,(BitEncoding.nat.list.encode a.2).length≤P) :
    contentSize (compile ts ⟨g,as⟩)≤contentSize g+as.length*familyCost ts*(V+P+1) := by
  induction as generalizing g with
  | nil => simp [compile]
  | cons a as ih =>
    have ha := gateTemplate_privateCount ts a
    have ht := gateTemplate_cost ts a
    have hgV : g.vertices≤V := by omega
    have hport := hp a (by simp)
    have hs := attachTemplate_contentSize (gateTemplate ts a) g a.2
    have hm := Nat.mul_le_mul ht (show g.vertices+(BitEncoding.nat.list.encode a.2).length+1≤V+P+1 by omega)
    have hnext : (compileStep ts g a).vertices+as.length*familyCost ts≤V := by
      change g.vertices+(gateTemplate ts a).privateCount+as.length*familyCost ts≤V
      simp only [List.length_cons] at hv
      nlinarith
    have hi := ih (compileStep ts g a) hnext (fun b hb=>hp b (by simp [hb]))
    change contentSize (compile ts ⟨compileStep ts g a,as⟩)≤_
    change contentSize (compileStep ts g a)≤_ at hs
    simp only [List.length_cons]
    nlinarith

private theorem mixed_length (g : MixedCode) :
    (MixedCode.encoding.encode g).length=
      2*g.vertices+2*(edgeItemEncoding.list.encode g.edges).length+
        (unaryItemEncoding.list.encode g.unaries).length+2 := by
  simp only [MixedCode.encoding,BitEncoding.retract,BitEncoding.prod_length,BitEncoding.unaryNat_length]
  dsimp only [edgeItemEncoding,unaryItemEncoding]
  omega

private theorem contentSize_le_length (g : MixedCode) : contentSize g≤(MixedCode.encoding.encode g).length := by
  have he := payloadSize_le_word edgeItemEncoding g.edges
  have hu := payloadSize_le_word unaryItemEncoding g.unaries
  rw [mixed_length]
  unfold contentSize
  omega

private theorem mixed_length_le_contentSize (g : MixedCode) :
    (MixedCode.encoding.encode g).length≤2*g.vertices+6*contentSize g+5 := by
  have he := word_length_le_payload edgeItemEncoding g.edges
  have hu := word_length_le_payload unaryItemEncoding g.unaries
  rw [mixed_length]
  unfold contentSize
  omega

/-- A concrete quadratic prefix bound covers every network, including malformed
labels, excessive/missing ports and invalid old graph indices. -/
theorem compile_prefix_size_bound (ts : List Template) (g : MixedCode) (as : List Gate) (i : ℕ) :
    (MixedCode.encoding.encode (compile ts ⟨g,as.take i⟩)).length≤
      (Polynomial.C (20*(familyCost ts+1)^2)*(Polynomial.X+1)^2).eval
        ((MixedCode.encoding.prod gateEncoding.list).encode (g,as)).length := by
  let N := ((MixedCode.encoding.prod gateEncoding.list).encode (g,as)).length
  let K := familyCost ts
  have hN : N=2*(MixedCode.encoding.encode g).length+(gateEncoding.list.encode as).length+1 :=
    BitEncoding.prod_length _ _ _
  have hg : (MixedCode.encoding.encode g).length≤N := by omega
  have hv : g.vertices≤N := by have h:=mixed_length g; omega
  have ha : as.length≤N := (BitEncoding.list_length_le gateEncoding as).trans (by omega)
  have htake : (as.take i).length≤N := by rw [List.length_take]; omega
  have hp : ∀a∈as.take i,(BitEncoding.nat.list.encode a.2).length≤N := by
    intro a hm
    have h := ListMapMachines.mem_le_sum_map (fun a=>(gateEncoding.encode a).length)
      (List.mem_of_mem_take hm)
    have hl := payloadSize_le_word gateEncoding as
    rw [payloadSize_eq] at hl
    have he : (gateEncoding.encode a).length=2*(BitEncoding.nat.encode a.1).length+
        (BitEncoding.nat.list.encode a.2).length+1 := BitEncoding.prod_length _ _ _
    dsimp only at h
    omega
  have hV : g.vertices+(as.take i).length*K≤N+N*K := Nat.add_le_add hv (Nat.mul_le_mul_right K htake)
  have hcontent := compile_contentSize ts g (as.take i) (N+N*K) N hV hp
  have hbase := (contentSize_le_length g).trans hg
  have hverts : (compile ts ⟨g,as.take i⟩).vertices≤N+N*K := by
    rw [compile_vertices]
    exact (Nat.add_le_add_left (ListMapMachines.sum_map_le_mul
      (fun a=>(gateTemplate ts a).privateCount) (as.take i) K
      (fun a _=>gateTemplate_privateCount ts a)) g.vertices).trans hV
  have hout := mixed_length_le_contentSize (compile ts ⟨g,as.take i⟩)
  have hmul := Nat.mul_le_mul_right (K*(N+N*K+N+1)) htake
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one]
  change _≤20*(K+1)^2*(N+1)^2
  change contentSize (compile ts ⟨g,as.take i⟩)≤contentSize g+(as.take i).length*K*(N+N*K+N+1) at hcontent
  nlinarith

end PlanarHom.FixedGadgetNetwork
