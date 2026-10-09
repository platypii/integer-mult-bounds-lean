import IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalBack

/-! Original-index semantics of both compact swap/rotation/swap schedules.
The middle stream acts at the current, actually swapped address. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalConjugation
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open ActivePrefixLayoutGeometry (backWidth)
open ActivePrefixDirtyControlConjugationData (FullArray tSwap uSwap)
open ActivePrefixDirtyControlGlobalSwap (index t_entry u_entry t_involutive u_involutive)
open ActivePrefixLayoutSwap (swapT)
open ActivePrefixDirtyControlUSwapGeometry (swapU)

variable (s : Shape) (p : Parameters s) {rows : ℕ}
def tResult (V : List Bool) (array : FullArray s rows) :=
  tSwap s rows (p.n*p.b) p.compactFits
    (ActivePrefixDirtyControlGlobalBack.result s p V (tSwap s rows (p.n*p.b) p.compactFits array))
def uResult (V : List Bool) (array : FullArray s rows) :=
  uSwap s rows (p.n*p.b) p.compactFits
    (ActivePrefixDirtyControlGlobalBack.result s p V (uSwap s rows (p.n*p.b) p.compactFits array))
def tDestination (V : List Bool) (x : Address s p rows) :=
  swapT s p (ActivePrefixDirtyControlGlobalBack.destination s p V (swapT s p x))
def uDestination (V : List Bool) (x : Address s p rows) :=
  swapU s p (ActivePrefixDirtyControlGlobalBack.destination s p V (swapU s p x))

theorem t_entry (V : List Bool)
    (hV : V.length=(rows*2^(backWidth s (p.n*p.q) p.before p.after))*(p.n*p.b))
    (array : FullArray s rows) (x : Address s p rows) :
    tResult s p V array (index s p (tDestination s p V x))=array (index s p x) := by
  unfold tResult tDestination
  rw [ActivePrefixDirtyControlGlobalSwap.t_entry,t_involutive,
    ActivePrefixDirtyControlGlobalBack.entry s p V hV,ActivePrefixDirtyControlGlobalSwap.t_entry,t_involutive]

theorem u_entry (V : List Bool)
    (hV : V.length=(rows*2^(backWidth s (p.n*p.q) p.before p.after))*(p.n*p.b))
    (array : FullArray s rows) (x : Address s p rows) :
    uResult s p V array (index s p (uDestination s p V x))=array (index s p x) := by
  unfold uResult uDestination
  rw [ActivePrefixDirtyControlGlobalSwap.u_entry,u_involutive,
    ActivePrefixDirtyControlGlobalBack.entry s p V hV,ActivePrefixDirtyControlGlobalSwap.u_entry,u_involutive]

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalConjugation
