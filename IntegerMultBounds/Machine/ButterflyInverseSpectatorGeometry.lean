import IntegerMultBounds.Machine.ButterflySpectatorGeometry
import IntegerMultBounds.Machine.ButterflyInverseAxisArray

/-! An actual inverse axis keeps every outer-row spectator and global coordinate.
Its output exchanges physical butterfly roles during the paid merge. -/
namespace IntegerMultBounds.Machine.ButterflyInverseSpectatorGeometry
noncomputable section
open ButterflySpectatorGeometry

def applyAxis (rows D t R p : ℕ) (ht : t<D) (f : Array rows D R) :=
  unshape rows D t R p ht (ButterflyInverseAxisRouting.transformed (reshape rows D t R p ht f))

theorem width_apply (rows D t R p : ℕ) (ht : t<D) (f : Array rows D R) (hw : Width rows D R p f) :
    Width rows D R p (applyAxis rows D t R p ht f) := by
  intro i
  unfold applyAxis unshape ButterflyAxisSerialization.joined
  exact ButterflyInverseAxisRouting.transformed_width (reshape rows D t R p ht f) (ButterflyGuard.width p D)
    (fun h j k => hw _) _ _ _

end
end IntegerMultBounds.Machine.ButterflyInverseSpectatorGeometry
