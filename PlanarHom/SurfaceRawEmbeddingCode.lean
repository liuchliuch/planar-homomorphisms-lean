import PlanarHom.SurfaceRawGenusBounds
import PlanarHom.PlanarityRowFaceCodeProgram
import PlanarHom.PairProjectionMachines

/-! NEW raw supplied-surface format. Inputs contain ordinary graph code,
ordinary cyclic row lists, and three finite natural-number tables: complement
genera, a complement-region label per dart, and a label per original vertex
(used only for isolated vertices). All semantic gluing data are extracted from
those tables; no homology basis, signs, genus bounds, or solver are supplied. -/
namespace PlanarHom.SurfaceRawEmbedding
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
open SurfaceRibbonComplement

structure ComplementCode where
  genera : List ℕ
  dartRegion : List ℕ
  isolatedRegion : List ℕ
  deriving DecidableEq

 def complementCode : BitEncoding ComplementCode :=
  (BitEncoding.nat.list.prod (BitEncoding.nat.list.prod BitEncoding.nat.list)).retract
    (fun c=>(c.genera,c.dartRegion,c.isolatedRegion))
    (fun p=>⟨p.1,p.2.1,p.2.2⟩) (by intro c; cases c; rfl)

 def dartIndex {m : ℕ} (a : Dart (Fin m)) : ℕ := 2*a.1.val+if a.2 then 1 else 0
 def ComplementCode.dartLabel (c : ComplementCode) {m : ℕ} (a : Dart (Fin m)) : ℕ :=
  c.dartRegion[dartIndex a]?.getD 0
 def ComplementCode.isolatedLabel (c : ComplementCode) (v : ℕ) : ℕ :=
  c.isolatedRegion[v]?.getD 0

/-- Entirely finite table validation against the supplied literal row system. -/
structure ComplementCode.WellFormed (c : ComplementCode) (g : MixedCode)
    {bt ut : ℕ} (hg : g.Valid bt ut) (R : RotationRows (g.toMultiGraph hg)) : Prop where
  regions_pos : 0<c.genera.length
  dart_length : c.dartRegion.length=2*g.edges.length
  isolated_length : c.isolatedRegion.length=g.vertices
  dart_bound : ∀a:Dart (Fin g.edges.length),c.dartLabel a<c.genera.length
  face_step : ∀a:Dart (Fin g.edges.length),c.dartLabel (R.facePerm a)=c.dartLabel a
  isolated_bound : ∀v:Fin g.vertices,c.isolatedLabel v.val<c.genera.length

namespace ComplementCode
variable {c : ComplementCode} {g : MixedCode} {bt ut : ℕ} {hg : g.Valid bt ut}
variable {R : RotationRows (g.toMultiGraph hg)}

 theorem label_eq_of_sameCycle (h : c.WellFormed g hg R) (a b : Dart (Fin g.edges.length))
    (hab:R.facePerm.SameCycle a b) : c.dartLabel a=c.dartLabel b := by
  obtain ⟨n,hn⟩:=hab.exists_nat_pow_eq
  have hi:∀n,c.dartLabel (R.facePerm^[n] a)=c.dartLabel a := by
    intro n
    induction n with
    | zero=>rfl
    | succ n ih=>rw [Function.iterate_succ_apply',h.face_step,ih]
  have hh:=hi n
  rw [Equiv.Perm.iterate_eq_pow,hn] at hh
  exact hh.symm

 def faceRegion (h : c.WellFormed g hg R) : R.Face→Fin c.genera.length :=
  Quotient.lift (fun a=>⟨c.dartLabel a,h.dart_bound a⟩)
    (fun a b hab=>Fin.ext (label_eq_of_sameCycle h a b hab))

 def toData (h : c.WellFormed g hg R) : Data R where
  regions:=c.genera.length
  regionGenus j:=c.genera[j.val]?.getD 0
  attachment
    | .inl f=>faceRegion h f
    | .inr v=>⟨c.isolatedLabel v.val.val,h.isolated_bound v.val⟩

 @[simp] theorem toData_face (h : c.WellFormed g hg R) (a : Dart (Fin g.edges.length)) :
    ((toData h).attachment (.inl (R.faceOf a))).val=c.dartLabel a := rfl
 @[simp] theorem toData_isolated (h : c.WellFormed g hg R) (v : Isolated (G:=g.toMultiGraph hg)) :
    ((toData h).attachment (.inr v)).val=c.isolatedLabel v.val.val := rfl

/-- The genus promise checks the actual finite gluing data extracted above. -/
 def Valid (c : ComplementCode) (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg)) (ambient : ℕ) : Prop :=
  ∃h:c.WellFormed g hg R,(toData h).Valid ambient

 theorem component_genus_bound (h : c.Valid g hg R ambient) (r : PlanarityLRRealization.Root g) :
    componentGenus g hg R r≤ambient := by
  obtain ⟨hw,hg⟩:=h
  exact component_genus_le g _ R (toData hw) hg r

 theorem component_has_genus (h : c.Valid g hg R ambient) (r : PlanarityLRRealization.Root g)
    [Nonempty (PlanarityLRRealization.ComponentEdge g r.val.val)] :
    ∃k≤ambient,(componentRows g hg r.val.val R).HasGenus k := by
  obtain ⟨hw,hg⟩:=h
  exact nonempty_component_genus g _ R (toData hw) hg r

end ComplementCode

abbrev Input := MixedCode×PlanarityRowFaceCode.Rows×ComplementCode
 def inputCode : BitEncoding Input :=
  MixedCode.encoding.prod (PlanarityRowFaceCode.rowsCode.prod complementCode)

 def Input.Valid (bt ut ambient : ℕ) (p : Input) : Prop :=
  ∃hg:p.1.Valid bt ut,∃R:RotationRows (p.1.toMultiGraph hg),
    PlanarityRowFaceCode.Realizes p.1 hg p.2.1 R ∧ p.2.2.Valid p.1 hg R ambient

 def graphRows (p : Input) : MixedCode×PlanarityRowFaceCode.Rows := (p.1,p.2.1)

 theorem fp_graphRows : FP inputCode PlanarityRowFaceCode.inputCode graphRows :=
  (PairProjectionMachines.fp_fst MixedCode.encoding (PlanarityRowFaceCode.rowsCode.prod complementCode)).pair
    ((PairProjectionMachines.fp_snd MixedCode.encoding (PlanarityRowFaceCode.rowsCode.prod complementCode)).comp
      (PairProjectionMachines.fp_fst PlanarityRowFaceCode.rowsCode complementCode))

end PlanarHom.SurfaceRawEmbedding
