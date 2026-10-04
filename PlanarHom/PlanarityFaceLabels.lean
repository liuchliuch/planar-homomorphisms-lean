import PlanarHom.PlanarityLRFaceRepresentatives
import PlanarHom.PlanarityFaceRootMachines

/-! NEW exact numeric labels and literal table lookup for computed face cycles. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRRealization

 def faceId (g : MixedCode) (bits : List Bool) (a : Dart) : ℕ :=
   (representatives g bits).idxOf (representative g bits a)
 def boundaryById (g : MixedCode) (bits : List Bool) (f : ℕ) : List Dart :=
   MultiGraph.Kasteleyn.tableBoundary (fullTable g bits) f

 theorem dart_idxOf_decidable (xs : List Dart) (a : Dart) :
    xs.idxOf a = @List.idxOf Dart instBEqOfDecidableEq a xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.idxOf_cons,Bool.beq_eq_decide_eq,ih]

 theorem lookup_unique {A B : Type} [BEq A] [LawfulBEq A] (xs : List (A×B))
    (k : A) (v : B) (hm : (k,v)∈xs) (hu : ∀p∈xs,p.1=k→p.2=v) : xs.lookup k=some v := by
  induction xs with
  | nil => simp at hm
  | cons p xs ih =>
    rcases p with ⟨j,w⟩
    by_cases hp:j=k
    · have hv : w=v := hu (j,w) (List.mem_cons_self ..) hp
      simp [List.lookup_cons,hp,hv]
    · have htail:(k,v)∈xs := by
        rcases List.mem_cons.mp hm with he | he
        · exact (hp (congrArg Prod.fst he).symm).elim
        · exact he
      have hkj : (k==j)=false := beq_eq_false_iff_ne.mpr (Ne.symm hp)
      simpa only [List.lookup_cons,hkj] using
        ih htail (fun q hq=>hu q (List.mem_cons_of_mem _ hq))

 theorem fullTable_lookup (g : MixedCode) (bits : List Bool) {f : ℕ} {a : Dart}
    (hf : (representatives g bits)[f]?=some a) :
    (fullTable g bits).lookup f=some (boundary g bits a) := by
  apply lookup_unique
  · exact List.mem_map.mpr ⟨(a,f),(List.mk_mem_zipIdx_iff_getElem?).mpr hf,rfl⟩
  · intro q hq hqf
    obtain ⟨⟨b,i⟩,hi,rfl⟩:=List.mem_map.mp hq
    change i=f at hqf
    subst i
    have hbf:=(List.mk_mem_zipIdx_iff_getElem?).mp hi
    have he:b=a:=Option.some.inj (hbf.symm.trans hf)
    simpa only [he]

 theorem fullTable_lookup_none (g : MixedCode) (bits : List Bool) {f : ℕ}
    (hf : (representatives g bits)[f]?=none) : (fullTable g bits).lookup f=none := by
  apply List.lookup_eq_none_iff.mpr
  intro q hq
  obtain ⟨⟨a,i⟩,hi,rfl⟩:=List.mem_map.mp hq
  have hif:=(List.mk_mem_zipIdx_iff_getElem?).mp hi
  have hne:f≠i := by intro h; subst i; simp [hf] at hif
  simp [bne,Bool.beq_eq_decide_eq,hne]

 theorem boundaryById_eq (g : MixedCode) (bits : List Bool) {f : ℕ} {a : Dart}
    (hf : (representatives g bits)[f]?=some a) : boundaryById g bits f=boundary g bits a := by
  simp only [boundaryById,MultiGraph.Kasteleyn.tableBoundary,fullTable_lookup g bits hf,Option.getD_some]

 theorem boundaryById_eq_nil (g : MixedCode) (bits : List Bool) {f : ℕ}
    (hf : (representatives g bits)[f]?=none) : boundaryById g bits f=[] := by
  simp only [boundaryById,MultiGraph.Kasteleyn.tableBoundary,fullTable_lookup_none g bits hf,Option.getD_none]

 theorem representative_mem_of_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) :
    representative g bits a∈representatives g bits := by
  simpa only [erase_liftDart] using representative_mem_representatives g hg bits (liftDart a ha)

 theorem faceId_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) : faceId g bits a<(representatives g bits).length :=
   List.idxOf_lt_length_of_mem (representative_mem_of_valid g hg bits ha)

 theorem boundaryById_faceId (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) :
    boundaryById g bits (faceId g bits a)=boundary g bits (representative g bits a) :=
   boundaryById_eq g bits (by
     simpa only [faceId,dart_idxOf_decidable] using
       List.getElem?_idxOf (representative_mem_of_valid g hg bits ha))

 theorem mem_boundary_iff_representative (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a b : Dart} (ha : a.1<g.edges.length)
    (hb : b∈representatives g bits) : a∈boundary g bits b ↔ representative g bits a=b := by
  have hr:=representative_mem_of_valid g hg bits ha
  have hm:a∈boundary g bits (representative g bits a) := by
    simpa only [erase_liftDart] using mem_representative_boundary g hg bits (liftDart a ha)
  constructor
  · intro hab
    by_contra hne
    exact (representative_boundaries_disjoint g hg bits hr hb hne) hm hab
  · intro he
    simpa only [he] using hm

 theorem mem_boundaryById_iff (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) (f : ℕ) :
    a∈boundaryById g bits f ↔ faceId g bits a=f := by
  cases hf:(representatives g bits)[f]? with
  | none =>
    rw [boundaryById_eq_nil g bits hf]
    have hi:=faceId_lt g hg bits ha
    have hn:=List.getElem?_eq_none_iff.mp hf
    simp only [List.not_mem_nil,false_iff]
    omega
  | some b =>
    have hb:=List.mem_of_getElem? hf
    rw [boundaryById_eq g bits hf,mem_boundary_iff_representative g hg bits ha hb]
    have hidx:(representatives g bits).idxOf b=f := by
      obtain ⟨hi,he⟩:=List.getElem?_eq_some_iff.mp hf
      rw [← he]
      simpa only [dart_idxOf_decidable] using List.idxOf_getElem (representatives_nodup g bits) f hi
    change representative g bits a=b ↔ (representatives g bits).idxOf (representative g bits a)=f
    rw [← hidx]
    simpa only [dart_idxOf_decidable] using (List.idxOf_inj (representative_mem_of_valid g hg bits ha) hb).symm

 theorem boundaryById_nodup (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (f : ℕ) : (boundaryById g bits f).Nodup := by
  cases hf:(representatives g bits)[f]? with
  | none => simp [boundaryById_eq_nil g bits hf]
  | some a =>
    rw [boundaryById_eq g bits hf]
    have ha:=representative_index_of_mem g bits (List.mem_of_getElem? hf)
    simpa only [erase_liftDart] using boundary_nodup g hg bits (liftDart a ha)

 theorem boundaryById_index_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (f : ℕ) {a : Dart} (ha : a∈boundaryById g bits f) : a.1<g.edges.length := by
  cases hf:(representatives g bits)[f]? with
  | none => simp [boundaryById_eq_nil g bits hf] at ha
  | some b =>
    rw [boundaryById_eq g bits hf] at ha
    exact (mem_all_boundaries g hg bits a).mp (List.mem_flatMap.mpr ⟨b,List.mem_of_getElem? hf,ha⟩)

end PlanarHom.PlanarityFaceCode
