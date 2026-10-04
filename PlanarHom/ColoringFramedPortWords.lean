import PlanarHom.ColoringFramedMacroFamily

/-! NEW literal physical triple-order words of every fixed macro, including
the fan's reversed logical output labels. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedMacro
open PositiveBlockProgram

 theorem leftPort_word (s : CellShape) : List.ofFn (leftPort s)=
    s.leftPorts.flatMap (fun p=>[(p,(2:Fin 3)),(p,1),(p,0)]) := by
  cases s <;> decide +kernel
 theorem rightPort_word (s : CellShape) : List.ofFn (rightPort s)=
    s.rightPorts.flatMap (fun p=>[(p,(2:Fin 3)),(p,1),(p,0)]) := by
  cases s <;> decide +kernel

 def rightOutput : (s : CellShape)→Fin (rightCount s)→Fin s.outputCount
  | .wireTop,_ | .wireBottom,_ | .wireDown,_ => ⟨0,by decide⟩
  | .cross,i => ⟨i.val/3,by change i.val/3<2; have := i.isLt; change i.val<6 at this; omega⟩
  | .fan,i => ⟨1-i.val/3,by change 1-i.val/3<2; omega⟩
  | .test,i => i.elim0

 theorem rightPort_fresh (c : Cell) (i : Fin (rightCount c.shape)) :
    (rightPort c.shape i).1=c.freshPort (rightOutput c.shape i) := by
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> fin_cases i <;> apply Fin.ext
  all_goals norm_num [rightPort,rightOutput,Cell.freshPort,CellShape.kind,Kind.template,ParsimoniousBlockTemplate.fanout,ParsimoniousBlockTemplate.equality,ParsimoniousBlockTemplate.crossover,CellShape.portCount,CellShape.outputCount]

end PlanarHom.ColoringEmitter.FramedMacro
