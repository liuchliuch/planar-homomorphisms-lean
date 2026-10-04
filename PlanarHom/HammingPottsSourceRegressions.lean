import PlanarHom.HammingPottsToSource

noncomputable section
namespace PlanarHom.HammingPottsSourceRegressions
open Complexity HammingPottsTensorPartition

example : selectedMultiplicity (fun _ : Fin 1=>3) 3 = 1 := by simp [selectedMultiplicity]
example : selectedMultiplicity (fun _ : Fin 1=>3) 2 = 0 := by simp [selectedMultiplicity]
example : discardedColors (fun _ : Fin 1=>3) 3 = 1 := by simp [discardedColors]
example : discardedColors (fun _ : Fin 1=>3) 2 = 3 := by simp [discardedColors]
example : selectedMultiplicity (fun r : Fin 0=>r.elim0) 3 = 0 := by simp [selectedMultiplicity]
example : discardedColors (fun r : Fin 0=>r.elim0) 3 = 1 := by simp [discardedColors]
example : BitEncoding.unaryNat.decode [false,false] = some 2 := rfl
example : BitEncoding.unaryNat.decode [true,true] = some 2 := rfl

end PlanarHom.HammingPottsSourceRegressions

#eval (PlanarHom.UniformSquaredDistanceKernel.prepare 0
  (2,⟨2,[(0,1,0)],[]⟩)).2.map (fun p=>(p.1,p.2.vertices,p.2.edges))
#eval (PlanarHom.UniformSquaredDistanceKernel.prepare 0
  (3,⟨1,[(0,0,0)],[]⟩)).2.map (fun p=>(p.1,p.2.vertices,p.2.edges))
#eval (PlanarHom.UniformSquaredDistanceKernel.prepare 0
  (1,⟨2,[(0,1,0),(0,1,0)],[]⟩)).2.map (fun p=>(p.1,p.2.vertices,p.2.edges))
#eval (PlanarHom.UniformSquaredDistanceKernel.prepare 1
  (2,⟨2,[(0,1,0)],[]⟩)).2.map (fun p=>(p.1,p.2.vertices,p.2.edges))
#eval (PlanarHom.UniformSquaredDistanceKernel.prepare 0
  (4,⟨3,[],[]⟩)).2.map (fun p=>(p.1,p.2.vertices,p.2.edges))
#eval (PlanarHom.HammingPottsRecoveryReduction.prepare ⟨2,[(0,1,0)],[]⟩).1
#eval (PlanarHom.HammingPottsRecoveryReduction.prepare ⟨0,[],[]⟩).2.length
