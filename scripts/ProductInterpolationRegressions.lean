import PlanarHom.DomainProductInterpolationReductions
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open ProductCompatibility ProductInterpolationPreparationMachines

noncomputable def ratBasis : Module.Basis (Fin 1) ℚ ℚ:=Module.Basis.singleton (Fin 1) ℚ

def sourceUnary : Fin 2→Fin 2→ℚ:=fun l _=>if l.val=0 then 2 else -5
def targetUnary : Fin 2→Fin 2→ℚ:=fun l _=>if l.val=0 then 3 else -5
def binary : Fin 1→Matrix (Fin 2) (Fin 2) ℚ:=fun _ _ _=>1
def weights : Fin 2→ℚ:=fun _=>1

theorem unchanged : ∀l : Fin 2,l.val≠(0 : Fin 2).val→targetUnary l=sourceUnary l:=by
  intro l hl
  change l.val≠0 at hl
  funext i
  simp only [sourceUnary,targetUnary,if_neg hl]
theorem zeros : ∀i,sourceUnary 0 i=0→targetUnary 0 i=0:=by
  intro i h
  norm_num [sourceUnary] at h
theorem products : HasProductMaps (sourceUnary 0) (targetUnary 0):=by
  apply hasProductMaps_of_compatible
  intro xs ys hlen _ _ _
  change (xs.map (fun _=>(3 : ℚ))).prod=(ys.map (fun _=>(3 : ℚ))).prod
  simp [hlen]

noncomputable def ordinaryReduction:=unaryProductReduction ratBasis binary sourceUnary targetUnary weights 0
  unchanged zeros products

def domains : Fin 1→Set (Fin 2):=fun _=>{0}
def binaryTyping : Fin 1→Fin 1→Fin 1→Prop:=fun _ _ _=>True
def unaryTyping : Fin 2→Fin 1→Prop:=fun _ _=>True
noncomputable def prescribedDomainReduction:=domainUnaryProductReduction ratBasis binary sourceUnary targetUnary
  weights domains binaryTyping unaryTyping 0 unchanged zeros products

-- Equal source products collide: one ORIGINAL source/target pair survives.
#guard ExponentProductTables.representatives (sourceUnary 0) (targetUnary 0) 2==[(4,9)]
#guard ExponentProductTables.representatives (fun _ : Fin 2=>(0 : ℚ)) (fun _=>(0 : ℚ)) 3==[]
#guard ExponentProductTables.representatives (fun _ : Fin 2=>(0 : ℚ)) (fun _=>(0 : ℚ)) 0==[(1,1)]

-- The signed unchanged factor is retained in the actual recovery arithmetic.
#guard recoverContext (sourceUnary 0) (metadataFor (sourceUnary 0) (targetUnary 0) 2,[-40])==(-90 : ℚ)
#guard recoverContext (sourceUnary 0) (metadataFor (sourceUnary 0) (targetUnary 0) 2,[-20])==(-45 : ℚ)

-- Occurrence order, parallel loops, and all companion labels are retained.
def graph : MixedCode:=⟨1,[(0,(0,0)),(0,(0,0))],[(0,0),(0,1),(0,0)]⟩
#guard (unaryPreparation (sourceUnary 0) (targetUnary 0) 0 graph).2==[graph]
#guard (graph.parallelUnaryLabel 0 3).edges==graph.edges
#guard (graph.parallelUnaryLabel 0 3).unaries==[(0,0),(0,0),(0,0),(0,1),(0,0),(0,0),(0,0)]
#print axioms ordinaryReduction
#print axioms prescribedDomainReduction
