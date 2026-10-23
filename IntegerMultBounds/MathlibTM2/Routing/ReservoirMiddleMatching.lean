module

public import IntegerMultBounds.MathlibTM2.Routing.MiddleMatchingShears
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirPlacement
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirPartition

/-! Actual reservoir placement turns a reservoir-fixing matching into an
explicit involution on the repair's middle field. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)

include hfit hw in
theorem reservoirMiddle_fit : w + (n - 3 * w) ≤ n := by omega

theorem reservoirPlacedMatching_fixes (mate : Fin n → Fin n)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q)
    (q : Fin n) (hq : q.val < w ∨ w + (n - 3 * w) ≤ q.val) :
    placedSource (reservoirPlacement n H hfit w hw k) mate q = q := by
  have hborrow : q.val < w ∨ n - 2 * w ≤ q.val := by omega
  have hm := hfix _ (reservoirPlacement_borrowed_mem n H hfit w hw k q hborrow)
  simp only [placedSource, hm, Equiv.symm_apply_apply]

def reservoirMiddleMatching (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q) : Fin (n - 3 * w) → Fin (n - 3 * w) :=
  middleMatching w (n - 3 * w) (reservoirMiddle_fit n H hfit w hw)
    (placedSource (reservoirPlacement n H hfit w hw k) mate)
    (placedMatching_involutive mate hinv (reservoirPlacement n H hfit w hw k))
    (reservoirPlacedMatching_fixes n H hfit w hw k mate hfix)

theorem reservoirMiddleMatching_involutive (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q) :
    Function.Involutive (reservoirMiddleMatching n H hfit w hw k mate hinv hfix) :=
  middleMatching_involutive _ _ _ _ _ _

theorem reservoirMiddleMatching_coordinate (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q) (q : Fin (n - 3 * w)) :
    reservoirPlacement n H hfit w hw k
        (middleCoordinate w (n - 3 * w) (reservoirMiddle_fit n H hfit w hw)
          (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q)) =
      mate (reservoirPlacement n H hfit w hw k
        (middleCoordinate w (n - 3 * w) (reservoirMiddle_fit n H hfit w hw) q)) := by
  rw [reservoirMiddleMatching, middleMatching_coordinate]
  simp only [placedSource, Equiv.apply_symm_apply]

/-- The scalar table-conversion pipeline: embed the local query, place it,
look up its physical mate, undo placement, then subtract the middle offset. -/
theorem reservoirMiddleMatching_value (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q) (q : Fin (n - 3 * w)) :
    (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val =
      ((reservoirPlacement n H hfit w hw k).symm
        (mate (reservoirPlacement n H hfit w hw k
          (middleCoordinate w (n - 3 * w) (reservoirMiddle_fit n H hfit w hw) q)))).val - w := by
  rfl

/-- Inverse placement of a looked-up mate remains inside the middle field,
so the final scalar subtraction is ordinary subtraction without underflow. -/
theorem reservoirMiddleMatching_lookup_bounds (mate : Fin n → Fin n)
    (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q) (q : Fin (n - 3 * w)) :
    let r := (reservoirPlacement n H hfit w hw k).symm
      (mate (reservoirPlacement n H hfit w hw k
        (middleCoordinate w (n - 3 * w) (reservoirMiddle_fit n H hfit w hw) q)))
    w ≤ r.val ∧ r.val < w + (n - 3 * w) := by
  exact middleMatching_interval w (n - 3 * w) (reservoirMiddle_fit n H hfit w hw)
    (placedSource (reservoirPlacement n H hfit w hw k) mate)
    (placedMatching_involutive mate hinv (reservoirPlacement n H hfit w hw k))
    (reservoirPlacedMatching_fixes n H hfit w hw k mate hfix) q

/-- Each actual reservoir class meets the concrete restriction preconditions. -/
theorem reservoirClassPlaced_fixes (mate : Fin n → Fin n) (q : Fin n)
    (hq : q.val < w ∨ w + (n - 3 * w) ≤ q.val) :
    placedSource (reservoirPlacement n H hfit w hw k)
      (matchingClass (routingReservoir n H hfit) mate k) q = q := by
  apply reservoirPlacedMatching_fixes n H hfit w hw k _ _ q hq
  intro i hi
  exact matchingClass_fixes (routingReservoir n H hfit) mate
    (routingReservoir_disjoint n H hfit) k i hi

/-- Three middle-field shears for one concrete reservoir class recover its
original physical action after placement is undone. -/
theorem reservoirClassMiddleShears_eq (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (x : Fin n → Bool) :
    let e := reservoirPlacement n H hfit w hw k
    let cls := matchingClass (routingReservoir n H hfit) mate k
    let hcls := matchingClass_involutive (routingReservoir n H hfit) mate hinv k
    placeAddress e.symm
      (matchingShears (placedSource e cls)
        (middleMatchingTargets w (n - 3 * w) (reservoirMiddle_fit n H hfit w hw)
          (placedSource e cls) (placedMatching_involutive cls hcls e)
          (reservoirClassPlaced_fixes n H hfit w hw k mate)) (placeAddress e x)) =
      fun q => x (cls q) := by
  exact placedMiddleMatchingShears_eq w (n - 3 * w) (reservoirMiddle_fit n H hfit w hw)
    (matchingClass (routingReservoir n H hfit) mate k)
    (matchingClass_involutive (routingReservoir n H hfit) mate hinv k)
    (reservoirPlacement n H hfit w hw k) (reservoirClassPlaced_fixes n H hfit w hw k mate) x

end IntegerMultBounds.MathlibTM2.Routing
