import IntegerMultBounds.Machine.RecursiveScalarCoordinates

/-! Actual viewed shift/scaling transport back to the original heterogeneous
field coordinates. The physical wrapper restores the original headers; these
lemmas identify its output permutation with the original ordered instruction. -/
namespace IntegerMultBounds.Machine.RecursiveScalarTransport
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection layout)
open RecursiveScalarSelection (first second compile)
open RecursiveScalarCoordinates
variable {m b t : ℕ} {v : Descriptor}
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- Retain the spectator fields while executing the actual scalar instruction. -/
def execute (op : OrderedAffine.Op (Fin (m+m)) (ZMod (modulus b))) (x : Address m b v) : Address m b v :=
  match op with
  | .scale i r => update x i (r*field x i)
  | .shift i j r => update x i (field x i+r*field x j)

theorem field_update (x : Address m b v) (i : Fin (m+m)) (z : ZMod (modulus b)) :
    field (update x i z) = Function.update (field x) i z := by
  funext j
  induction j using Fin.addCases with
  | left j => simp only [field,Fin.addCases_left,update]
  | right j => simp only [field,Fin.addCases_right,update]

/-- The packed-coordinate execution has the actual ordered-affine semantics. -/
theorem field_execute (op : OrderedAffine.Op (Fin (m+m)) (ZMod (modulus b))) (x : Address m b v) :
    field (execute op x) = OrderedAffine.execute op (field x) := by
  cases op <;> exact field_update _ _ _

private theorem shift_eq (s : Selection m) (x : Address m b v) (r : ℚ) (hd : r.den < prime) :
    RecursiveInterchangeShift.shiftAddress r (viewAddress s x) =
      setSecond s x (field x (second s)+Swap.Modular.ratMod (modulus b) r*field x (first s)) := by
  unfold RecursiveInterchangeShift.shiftAddress setSecond
  congr 1
  apply Fin.ext
  have hh := RecursiveInterchangeShift.shiftAddress_d r hd (viewAddress s x)
  cases s with
  | cross i j =>
    simp only [RecursiveInterchangeShift.shiftAddress,first_value,second_value,layout,
      RecursiveAffineViews.cross,RecursiveInterchangeLayout.child,ZMod.val_add] at hh ⊢
    erw [ZMod.natCast_zmod_val] at hh
    exact hh
  | within g j i hj =>
    cases g <;>
      simp only [RecursiveInterchangeShift.shiftAddress,first_value,second_value,layout,
        RecursiveAffineDimensionsClean.view,RecursiveAffineViews.withinH,RecursiveAffineViews.withinD,
        ZMod.val_add] at hh ⊢
    all_goals erw [ZMod.natCast_zmod_val] at hh; exact hh

private theorem scale_second_eq (s : Selection m) (x : Address m b v) (r : ℚ) :
    RecursiveInterchangeScaling.scaleAddress r (viewAddress s x) .d =
      setSecond s x (Swap.Modular.ratMod (modulus b) r*field x (second s)) := by
  dsimp only [RecursiveInterchangeScaling.scaleAddress,setSecond]
  congr 1
  apply Fin.ext
  cases s with
  | cross i j =>
    simp only [FlatAffineScalingArray.coordinate,second_value,layout,RecursiveAffineViews.cross,
      RecursiveInterchangeLayout.child]
    erw [ZMod.natCast_zmod_val]
    rfl
  | within g j i hj =>
    cases g <;>
      simp only [FlatAffineScalingArray.coordinate,second_value,layout,RecursiveAffineDimensionsClean.view,
        RecursiveAffineViews.withinH,RecursiveAffineViews.withinD]
    all_goals erw [ZMod.natCast_zmod_val]; rfl

private theorem scale_first_eq (x : Address m b v) (i j : Fin m) (r : ℚ) :
    RecursiveInterchangeScaling.scaleAddress r (viewAddress (.cross i j) x) .h =
      setCrossFirst x i j (Swap.Modular.ratMod (modulus b) r*x.h i) := by
  dsimp only [RecursiveInterchangeScaling.scaleAddress,setCrossFirst]
  congr 1
  apply Fin.ext
  have hh := first_value (.cross i j) x
  simp only [first,field_h] at hh
  change (Swap.Modular.ratMod (modulus b) r*((crossAddress x i j).h.val : ZMod (modulus b))).val = _
  erw [hh,ZMod.natCast_zmod_val]

/-- The actual controlled rotation changes the originally numbered target. -/
theorem shift_index (s : Selection m) (hw : v.width=m*b) (x : Address m b v) (r : ℚ) (hd : r.den < prime) :
    Fin.cast (RecursiveViewRoleBank.layout_volume s b v hw)
      (RecursiveInterchangeScaling.index (RecursiveInterchangeShift.shiftAddress r (viewAddress s x))) =
      index hw (execute (.shift (second s) (first s) (Swap.Modular.ratMod (modulus b) r)) x) := by
  rw [shift_eq s x r hd]
  exact setSecond_index s hw x _

/-- The actual scaling of a view's second coordinate changes the original target. -/
theorem scale_second_index (s : Selection m) (hw : v.width=m*b) (x : Address m b v) (r : ℚ) :
    Fin.cast (RecursiveViewRoleBank.layout_volume s b v hw)
      (RecursiveInterchangeScaling.index (RecursiveInterchangeScaling.scaleAddress r (viewAddress s x) .d)) =
      index hw (execute (.scale (second s) (Swap.Modular.ratMod (modulus b) r)) x) := by
  rw [scale_second_eq]
  exact setSecond_index s hw x _

/-- The actual H scaling through a cross view changes the original H target. -/
theorem scale_first_index (hw : v.width=m*b) (x : Address m b v) (i j : Fin m) (r : ℚ) :
    Fin.cast (RecursiveViewRoleBank.layout_volume (.cross i j) b v hw)
      (RecursiveInterchangeScaling.index (RecursiveInterchangeScaling.scaleAddress r (viewAddress (.cross i j) x) .h)) =
      index hw (execute (.scale (AffineFieldCoordinates.hIndex i) (Swap.Modular.ratMod (modulus b) r)) x) := by
  rw [scale_first_eq]
  simpa only [execute,field_h] using setCrossFirst_index hw x i j (Swap.Modular.ratMod (modulus b) r*x.h i)

/-- The paid view/shift/restore wrapper transports original field coordinates. -/
theorem shift_entry (s : Selection m) (wire : Fin t) (r : ℚ) (hd : r.den < prime)
    (hw : v.width=m*b) (data : RecursiveViewedAction.Data t v) (x : Address m b v) :
    RecursiveViewedAction.array s (.shift wire r hd) b v hw data wire
      (index hw (execute (.shift (second s) (first s) (Swap.Modular.ratMod (modulus b) r)) x)) =
        data wire (index hw x) := by
  rw [← shift_index s hw x r hd]
  simp only [RecursiveViewedAction.array,RecursiveAffineViews.array,RecursiveViewedAction.transform,
    Function.update_self,Fin.cast_cast,Fin.cast_eq_self]
  rw [RecursiveInterchangeShift.array_entry]
  change data wire (Fin.cast (RecursiveViewRoleBank.layout_volume s b v hw)
    (RecursiveInterchangeScaling.index (viewAddress s x))) = _
  rw [view_index]

/-- The paid view/scaling/restore wrapper transports original target fields. -/
theorem scale_second_entry (s : Selection m) (wire : Fin t) (r : ℚ)
    (hr : Shared50AffineCoefficients.ScaleOccurs r) (hw : v.width=m*b)
    (data : RecursiveViewedAction.Data t v) (x : Address m b v) :
    RecursiveViewedAction.array s (.scale wire r hr .d) b v hw data wire
      (index hw (execute (.scale (second s) (Swap.Modular.ratMod (modulus b) r)) x)) =
        data wire (index hw x) := by
  rw [← scale_second_index s hw x r]
  simp only [RecursiveViewedAction.array,RecursiveAffineViews.array,RecursiveViewedAction.transform,
    Function.update_self,Fin.cast_cast,Fin.cast_eq_self]
  rw [RecursiveInterchangeScaling.array_entry]
  change data wire (Fin.cast (RecursiveViewRoleBank.layout_volume s b v hw)
    (RecursiveInterchangeScaling.index (viewAddress s x))) = _
  rw [view_index]

/-- Scaling H through a cross view transports the original H coordinate. -/
theorem scale_first_entry (wire : Fin t) (i j : Fin m) (r : ℚ)
    (hr : Shared50AffineCoefficients.ScaleOccurs r) (hw : v.width=m*b)
    (data : RecursiveViewedAction.Data t v) (x : Address m b v) :
    RecursiveViewedAction.array (.cross i j) (.scale wire r hr .h) b v hw data wire
      (index hw (execute (.scale (AffineFieldCoordinates.hIndex i) (Swap.Modular.ratMod (modulus b) r)) x)) =
        data wire (index hw x) := by
  rw [← scale_first_index hw x i j r]
  simp only [RecursiveViewedAction.array,RecursiveAffineViews.array,RecursiveViewedAction.transform,
    Function.update_self,Fin.cast_cast,Fin.cast_eq_self]
  rw [RecursiveInterchangeScaling.array_entry]
  change data wire (Fin.cast (RecursiveViewRoleBank.layout_volume (.cross i j) b v hw)
    (RecursiveInterchangeScaling.index (viewAddress (.cross i j) x))) = _
  rw [view_index]

/-- The chosen static wrapper executes the exact original scalar instruction. -/
theorem compile_entry (wire : Fin t) (op : FlatCoordinateSchedule.Op (m+m)) (hw : v.width=m*b)
    (data : RecursiveViewedAction.Data t v) (x : Address m b v) :
    RecursiveViewedAction.array (compile wire op).selection (compile wire op).action b v hw data wire
      (index hw (execute (op.action b) x)) = data wire (index hw x) := by
  have he := congrArg (OrderedAffine.mapOp (Swap.Modular.ratMod (modulus b)))
    (RecursiveScalarSelection.compile_rational wire op)
  change OrderedAffine.mapOp (Swap.Modular.ratMod (modulus b)) (compile wire op).rational = op.action b at he
  rw [← he]
  cases op with
  | scale target r hr =>
    dsimp only [compile]
    split
    · exact scale_first_entry wire _ _ r hr hw data x
    · exact scale_second_entry _ wire r hr hw data x
  | shift target control earlier r hr =>
    dsimp only [compile]
    split
    · exact shift_entry _ wire r _ hw data x
    · split <;> exact shift_entry _ wire r _ hw data x

/-- A scalar wrapper preserves every role other than its designated wire. -/
theorem compile_other (wire : Fin t) (op : FlatCoordinateSchedule.Op (m+m)) (hw : v.width=m*b)
    (data : RecursiveViewedAction.Data t v) (other : Fin t) (hne : other ≠ wire) :
    RecursiveViewedAction.array (compile wire op).selection (compile wire op).action b v hw data other = data other := by
  cases op with
  | scale target r hr =>
    dsimp only [compile]
    split <;> funext i <;>
      simp only [RecursiveViewedAction.array,RecursiveViewedAction.transform,RecursiveViewedAction.viewData,
        RecursiveAffineViews.array,Function.update_of_ne hne,Fin.cast_cast,Fin.cast_eq_self]
  | shift target control earlier r hr =>
    dsimp only [compile]
    split
    · funext i
      simp only [RecursiveViewedAction.array,RecursiveViewedAction.transform,RecursiveViewedAction.viewData,
        RecursiveAffineViews.array,Function.update_of_ne hne,Fin.cast_cast,Fin.cast_eq_self]
    · split <;> funext i <;>
        simp only [RecursiveViewedAction.array,RecursiveViewedAction.transform,RecursiveViewedAction.viewData,
          RecursiveAffineViews.array,Function.update_of_ne hne,Fin.cast_cast,Fin.cast_eq_self]

end
end IntegerMultBounds.Machine.RecursiveScalarTransport
