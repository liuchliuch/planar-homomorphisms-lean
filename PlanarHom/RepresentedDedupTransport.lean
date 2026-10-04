import PlanarHom.ListDedupMachines

/-! Stable filtering/deduplication commutes with a semantic value map whenever
its actual Boolean key tests agree. Injectivity of the code-value map is not
required, so noncanonical representatives are handled faithfully. -/
namespace PlanarHom.RepresentedDedupTransport
open ListDedupMachines
variable {A B:Type}

theorem map_step (f:A→B) (ta:A×A→Bool) (tb:B×B→Bool)
    (ht:∀a b,ta (a,b)=tb (f a,f b)) (acc:List A) (a:A) :
    (step ta acc a).map f=step tb (acc.map f) (f a) := by
  have he:acc.any (fun b=>ta (a,b))=(acc.map f).any (fun b=>tb (f a,b)) := by
    simp only [List.any_map,Function.comp_def,ht]
  simp only [step,he]
  split <;> simp

theorem map_fold (f:A→B) (ta:A×A→Bool) (tb:B×B→Bool)
    (ht:∀a b,ta (a,b)=tb (f a,f b)) (xs acc:List A) :
    (xs.foldl (step ta) acc).map f=(xs.map f).foldl (step tb) (acc.map f) := by
  induction xs generalizing acc with
  | nil=>rfl
  | cons a xs ih=>simp only [List.foldl_cons,List.map_cons,ih,map_step f ta tb ht]

theorem map_dedup (f:A→B) (ta:A×A→Bool) (tb:B×B→Bool)
    (ht:∀a b,ta (a,b)=tb (f a,f b)) (xs:List A) :
    (dedup ta xs).map f=dedup tb (xs.map f) :=
  map_fold f ta tb ht xs []

theorem map_filter (f:A→B) (pa:A→Bool) (pb:B→Bool)
    (hp:∀a,pa a=pb (f a)) (xs:List A) :
    (xs.filter pa).map f=(xs.map f).filter pb := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>simp only [List.filter_cons,List.map_cons,hp]; split <;> simp [ih]

end PlanarHom.RepresentedDedupTransport
