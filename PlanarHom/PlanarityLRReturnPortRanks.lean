import PlanarHom.PlanarityLRDirectedRootMembership

/-! NEW concrete per-occurrence component ranks and common-fork port membership. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open PlanarityDepthFirstSearch

def directedEdgeRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (e : Fin g.edges.length) : Fin g.vertices :=
  ⟨componentRoot g (source g e.val),(componentRoot_spec g (source_target_valid g hg e.isLt).1).1⟩

def directedPortRank (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (a : Dart (Fin g.edges.length)) : ℕ :=
  (directedRootPorts g hg rows (directedEdgeRoot g hg a.1)).idxOf a

theorem directedPortRank_eq_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) (a : Dart (Fin g.edges.length))
    (hroot : componentRoot g (source g a.1.val)=r.val) :
    directedPortRank g hg rows a=(directedRootPorts g hg rows r).idxOf a := by
  have he : directedEdgeRoot g hg a.1=r := Fin.ext hroot
  rw [directedPortRank,he]

theorem return_source_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (e : ℕ) (b : Fin g.edges.length) (hb : b.val∈returns g e) :
    componentRoot g (source g b.val)=componentRoot g (source g e) :=
  (componentRoot_eq_of_desc g (source_target_valid g hg b.isLt).1
    (returns_source_descendant g hg e hb)).symm

theorem return_port_mem_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) (hr : height g r.val=0)
    (e : ℕ) (b : Fin g.edges.length) (hb : b.val∈returns g e)
    (hroot : componentRoot g (source g e)=r.val) (bit : Bool) :
    (b,bit)∈directedRootPorts g hg rows r := by
  have hback := mem_returns_back g e hb
  have hf : isTree g b.val=false := (of_decide_eq_true hback).2.1
  have hs := (return_source_componentRoot g hg e b hb).trans hroot
  apply mem_directedRootPorts_of_component g hg rows r hr (b,bit) hf
  cases bit
  · change componentRoot g (target g b.val)=r.val
    exact (componentRoot_eq_of_desc g (source_target_valid g hg b.isLt).1
      (Or.inr (back_target_ancestor g hg hback))).trans hs
  · exact hs

theorem return_port_rank_eq_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices)
    (e : ℕ) (b : Fin g.edges.length) (hb : b.val∈returns g e)
    (hroot : componentRoot g (source g e)=r.val) (bit : Bool) :
    directedPortRank g hg rows (b,bit)=(directedRootPorts g hg rows r).idxOf (b,bit) :=
  directedPortRank_eq_root g hg rows r (b,bit) ((return_source_componentRoot g hg e b hb).trans hroot)

theorem outgoing_return_port_mem_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r v : Fin g.vertices) (hr : height g r.val=0)
    (hroot : componentRoot g v.val=r.val) (e : ℕ) (he : e∈outgoing g v.val)
    (b : Fin g.edges.length) (hb : b.val∈returns g e) (bit : Bool) :
    (b,bit)∈directedRootPorts g hg rows r :=
  return_port_mem_root g hg rows r hr e b hb
    ((congrArg (componentRoot g) (outgoing_spec g he).2.2).trans hroot) bit

theorem outgoing_return_port_rank_eq_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r v : Fin g.vertices)
    (hroot : componentRoot g v.val=r.val) (e : ℕ) (he : e∈outgoing g v.val)
    (b : Fin g.edges.length) (hb : b.val∈returns g e) (bit : Bool) :
    directedPortRank g hg rows (b,bit)=(directedRootPorts g hg rows r).idxOf (b,bit) :=
  return_port_rank_eq_root g hg rows r e b hb
    ((congrArg (componentRoot g) (outgoing_spec g he).2.2).trans hroot) bit

theorem fork_return_ports_mem_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r v : Fin g.vertices) (hr : height g r.val=0)
    (hroot : componentRoot g v.val=r.val) (e f : ℕ)
    (he : e∈outgoing g v.val) (hf : f∈outgoing g v.val)
    (b c : Fin g.edges.length) (hb : b.val∈returns g e) (hc : c.val∈returns g f) :
    (b,true)∈directedRootPorts g hg rows r ∧ (b,false)∈directedRootPorts g hg rows r ∧
    (c,true)∈directedRootPorts g hg rows r ∧ (c,false)∈directedRootPorts g hg rows r :=
  ⟨outgoing_return_port_mem_root g hg rows r v hr hroot e he b hb true,
   outgoing_return_port_mem_root g hg rows r v hr hroot e he b hb false,
   outgoing_return_port_mem_root g hg rows r v hr hroot f hf c hc true,
   outgoing_return_port_mem_root g hg rows r v hr hroot f hf c hc false⟩

end PlanarHom.PlanarityLRRealization
