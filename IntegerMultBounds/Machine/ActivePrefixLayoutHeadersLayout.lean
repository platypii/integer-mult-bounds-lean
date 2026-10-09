import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersPlaced
import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersGeometry

/-! Physical caller-placed layout-header preparation with its cost absorbed
by the original full array volume. Computed starts, n+1 and suffix begin blank.
Original H/B/F reservation-width synthesis remains upstream. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutHeadersLayout
noncomputable section
open ActivePrefixLayoutHeadersData ActivePrefixLayoutHeadersGeometry
open ActivePrefixLayoutHeadersPlaced
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
variable {a t : ℕ}

/-- Preparation from original layout widths and gadget controls, retaining
all originals and arbitrary array/spectator tapes in the caller. -/
theorem produces (mode : Mode) (caller : Tapes t a) (focus : Fin 24 → Fin t)
    (hf : Function.Injective focus) (s : Shape) (p : Parameters s) (offset rows : ℕ)
    (hfit : offset+p.f*p.q≤room s p mode) (hrows : 0<rows) (hrecord : s.bits+1≤s.payload)
    (hs : Fin 14 → List Bool) (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=originalValues (inputs s p offset rows) i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program mode focus hf) (fun v => v=CleanSubbank.bank (s := 43) caller)
      (fun v => v=CleanSubbank.bank (s := 43) (result caller focus mode (inputs s p offset rows)))
      (ActivePrefixLayoutHeadersBudget.constant*(rows*s.recordWidth)) := by
  have hp : 0<s.payload := by omega
  exact ActivePrefixLayoutHeadersPlaced.produces caller focus hf mode (inputs s p offset rows)
    p.compactFits hs hsrc hv hc (rows*s.recordWidth)
    (by unfold Shape.recordWidth; positivity) hp
    (originals_bound s p offset rows mode hfit hrows hrecord) (suffix_bound s p offset rows mode hrows)

/-- Post-use cleanup retains original descriptors and all caller spectators,
with the same containing-volume bound and clean private workspace. -/
theorem cleans (mode : Mode) (caller : Tapes t a) (focus : Fin 24 → Fin t)
    (hf : Function.Injective focus) (s : Shape) (p : Parameters s) (offset rows : ℕ)
    (hfit : offset+p.f*p.q≤room s p mode) (hrows : 0<rows) (hrecord : s.bits+1≤s.payload)
    (hs : Fin 14 → List Bool) (hsrc : SharedBank.payload caller focus=outputs mode (inputs s p offset rows))
    (hv : ∀ i, Counter.value (hs i)=originalValues (inputs s p offset rows) i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (cleanupProgram focus hf) (fun v => v=CleanSubbank.bank (s := 43) caller)
      (fun v => v=CleanSubbank.bank (s := 43) (restored caller focus hs))
      (ActivePrefixLayoutHeadersBudget.cleanupConstant*(rows*s.recordWidth)) := by
  have hp : 0<s.payload := by omega
  exact ActivePrefixLayoutHeadersPlaced.cleans caller focus hf mode (inputs s p offset rows)
    hs hsrc hv hc (rows*s.recordWidth) (by unfold Shape.recordWidth; positivity)
    (originals_bound s p offset rows mode hfit hrows hrecord) (suffix_bound s p offset rows mode hrows)

end
end IntegerMultBounds.Machine.ActivePrefixLayoutHeadersLayout
