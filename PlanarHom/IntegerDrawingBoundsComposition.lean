import PlanarHom.IntegerDrawingSpatialCertificate
namespace PlanarHom.IntegerDrawingSpatialCertificate.Tree
variable {α : Type} {check : Box → α → Bool}
theorem bounds_node {b : Box} {l r : Tree α}
    (hlb : l.box.sub b) (hrb : r.box.sub b)
    (hl : l.bounds check=true) (hr : r.bounds check=true) :
    (Tree.node b l r).bounds check=true := by
  simp only [bounds,decide_eq_true hlb,decide_eq_true hrb,hl,hr,Bool.and_self]
end PlanarHom.IntegerDrawingSpatialCertificate.Tree
