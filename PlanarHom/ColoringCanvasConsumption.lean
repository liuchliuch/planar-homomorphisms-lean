import PlanarHom.ColoringCanvasInputOrigins

/-! NEW single-consumption invariant of the actual ordered frontier run.
Fresh output names cannot reintroduce a signal removed by an earlier cell. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree

 theorem Cell.right_names_nodup (c:Cell) : (c.rightFrontier.map Prod.fst).Nodup := by
   rw [rightFrontier_names]
   rcases c with ⟨col,row,s,base,args⟩
   cases s <;> simp [Cell.outputRefs] <;> omega

 theorem Cell.right_names_bounds (c:Cell) (x:ℕ) (hx:x∈c.rightFrontier.map Prod.fst) :
     c.base≤x ∧ x<c.base+c.fresh := by
   rw [rightFrontier_names] at hx
   obtain ⟨j,rfl⟩:=c.output_mem x hx
   have hj:=j.isLt
   have hh:=c.shape.outputs_add_auxiliaries
   change c.shape.outputCount+c.shape.auxiliaryCount=c.fresh at hh
   omega

 theorem replacement_nodup (pre input output post:List ℕ) (m:ℕ)
     (hn:(pre++input++post).Nodup) (ho:output.Nodup)
     (hb:∀x∈pre++input++post,x<m) (hf:∀x∈output,m≤x) :
     (pre++output++post).Nodup ∧ List.Disjoint input (pre++output++post) := by
   obtain ⟨hpi,hq,hpiq⟩:=List.nodup_append'.mp hn
   obtain ⟨hp,hi,hpi⟩:=List.nodup_append'.mp hpi
   have hpq:List.Disjoint pre post := by
     apply List.disjoint_left.mpr
     intro x hx hy
     exact List.disjoint_left.mp hpiq (List.mem_append_left _ hx) hy
   have hiq:List.Disjoint input post := by
     apply List.disjoint_left.mpr
     intro x hx hy
     exact List.disjoint_left.mp hpiq (List.mem_append_right _ hx) hy
   have hpo:List.Disjoint pre output := by
     apply List.disjoint_left.mpr
     intro x hx hy
     have hl:=hb x (by simp [hx])
     have hr:=hf x hy
     omega
   have hoq:List.Disjoint output post := by
     apply List.disjoint_left.mpr
     intro x hx hy
     have hl:=hb x (by simp [hy])
     have hr:=hf x hx
     omega
   have hio:List.Disjoint input output := by
     apply List.disjoint_left.mpr
     intro x hx hy
     have hl:=hb x (by simp [hx])
     have hr:=hf x hy
     omega
   constructor
   · apply List.nodup_append'.mpr
     refine ⟨List.nodup_append'.mpr ⟨hp,ho,hpo⟩,hq,?_⟩
     simpa only [List.disjoint_append_left] using And.intro hpq hoq
   · simpa only [List.disjoint_append_right] using And.intro (And.intro hpi.symm hio) hiq

 theorem FrontierRun.consumed_nodup_origin {xs ys:List PortData} {cs:List Cell}
     (h:FrontierRun xs cs ys) (m:ℕ) (hb:BaseSequence m cs)
     (hn:(xs.map Prod.fst).Nodup) (hlt:∀x∈xs.map Prod.fst,x<m) :
     ((leftFrontier cs).map Prod.fst).Nodup ∧
       ∀x∈(leftFrontier cs).map Prod.fst,x∈xs.map Prod.fst ∨ m≤x := by
   induction h generalizing m with
   | nil xs => simp [leftFrontier]
   | cons pre post c cs ys h ih =>
     have hbase:c.base=m:=hb.1
     simp only [List.map_append] at hn hlt
     have hout:=c.right_names_nodup
     have hbounds:∀x∈c.rightFrontier.map Prod.fst,m≤x ∧ x<m+c.fresh := by
       intro x hx
       simpa only [hbase] using c.right_names_bounds x hx
     obtain ⟨hnew,hdis⟩:=replacement_nodup (pre.map Prod.fst) (c.leftFrontier.map Prod.fst)
       (c.rightFrontier.map Prod.fst) (post.map Prod.fst) m hn hout hlt (fun x hx=>(hbounds x hx).1)
     have hnewBound:∀x∈(pre++c.rightFrontier++post).map Prod.fst,x<m+c.fresh := by
       intro x hx
       simp only [List.map_append,List.mem_append] at hx
       rcases hx with (hx|hx)|hx
       · have hh:=hlt x (by simp [hx]); omega
       · exact (hbounds x hx).2
       · have hh:=hlt x (by simp [hx]); omega
     have ht:=ih (m+c.fresh) hb.2 (by simpa only [List.map_append] using hnew) hnewBound
     simp only [leftFrontier_cons,List.map_append]
     constructor
     · apply List.nodup_append'.mpr
       refine ⟨(List.nodup_append'.mp (List.nodup_append'.mp hn).1).2.1,ht.1,?_⟩
       apply List.disjoint_left.mpr
       intro x hx hy
       rcases ht.2 x hy with hh|hh
       · exact List.disjoint_left.mp hdis hx (by simpa only [List.map_append] using hh)
       · have hl:=hlt x (by simp [hx]); omega
     · intro x hx
       rcases List.mem_append.mp hx with hx|hx
       · exact Or.inl (by simp [hx])
       · rcases ht.2 x hx with hh|hh
         · simp only [List.map_append,List.mem_append] at hh
           rcases hh with (hh|hh)|hh
           · exact Or.inl (by simp [hh])
           · exact Or.inr (hbounds x hh).1
           · exact Or.inl (by simp [hh])
         · exact Or.inr (by omega)

 theorem railFrontier_map_names (col row:ℕ) (xs:List ℕ) :
     (railFrontier col row xs).map Prod.fst=xs := by
   induction xs generalizing row with
   | nil => rfl
   | cons x xs ih => simp [railFrontier,ih]

 theorem canvas_consumed_names_nodup (f:NumericFormula) (hf:NumericValid f) :
     ((leftFrontier (canvas f)).map Prod.fst).Nodup := by
   apply (FrontierRun.consumed_nodup_origin (canvas_frontierRun f hf) f.1 (canvas_bases f hf) ?_ ?_).1
   · rw [railFrontier_map_names]
     exact List.nodup_range
   · rw [railFrontier_map_names]
     exact fun x hx=>List.mem_range.mp hx
end PlanarHom.PositiveBlockProgram
