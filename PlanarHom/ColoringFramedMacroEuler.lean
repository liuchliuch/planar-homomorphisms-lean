import PlanarHom.IndexedRotationEuler
import PlanarHom.ColoringMacroTestFramedRotation
import PlanarHom.ColoringMacroWireFramedRotation
import PlanarHom.ColoringMacroCrossFramedRotation
import PlanarHom.ColoringMacroFanFramedRotation

noncomputable section
open Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PlanarHom.ColoringMacroFaces
open MultiGraph FinitePermutationCycles RadialPotts.Assembly
namespace TestFramed
theorem full_euler : Fintype.card (Fin 118)+count (subsetBoundary framedRotation Finset.univ)=
    Fintype.card (Fin 285)+2*framedGraph.componentCount Finset.univ :=
  IndexedRotationCertificate.euler (n:=118) (m:=285) host permutation connectivityCertificate euler
end TestFramed
namespace WireFramed
theorem full_euler : Fintype.card (Fin 534)+count (subsetBoundary framedRotation Finset.univ)=
    Fintype.card (Fin 1323)+2*framedGraph.componentCount Finset.univ :=
  IndexedRotationCertificate.euler (n:=534) (m:=1323) host permutation connectivityCertificate euler
end WireFramed
namespace CrossFramed
theorem full_euler : Fintype.card (Fin 1274)+count (subsetBoundary framedRotation Finset.univ)=
    Fintype.card (Fin 3168)+2*framedGraph.componentCount Finset.univ :=
  IndexedRotationCertificate.euler (n:=1274) (m:=3168) host permutation connectivityCertificate euler
end CrossFramed
namespace FanFramed
theorem full_euler : Fintype.card (Fin 1058)+count (subsetBoundary framedRotation Finset.univ)=
    Fintype.card (Fin 2632)+2*framedGraph.componentCount Finset.univ :=
  IndexedRotationCertificate.euler (n:=1058) (m:=2632) host permutation connectivityCertificate euler
end FanFramed
end PlanarHom.ColoringMacroFaces
