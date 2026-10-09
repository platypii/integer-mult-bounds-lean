import IntegerMultBounds.Machine.PackedPrefixRepeatHeadersBudget
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedData

/-! The prefix-source setup cost in the actual unchanged global reservation.
The gap is the real carved control gap; every intermediate header and L fit
within the complete reserved array. No setup-volume oracle is assumed. -/
namespace IntegerMultBounds.Machine.PackedPrefixRepeatHeadersReserved
noncomputable section
open CompactGadgetReservationShape
open PackedPrefixRepeatHeaders
open CompactGadgetReservationHeadersWords
open CompactGadgetReservationHeadersCost
open CompactGadgetReservationHeadersCarvedData (gap)
variable {t a : ℕ}

theorem geometry_bounds (s : Shape) (n q b rows : ℕ)
    (hrows : 0<rows) (hp : 0<s.payload) (hb : n*b≤s.H) :
    s.axes*s.guard≤rows*s.recordWidth ∧
      repetitions s.axes s.guard n q b (gap s (n*b) .control)≤rows*s.recordWidth := by
  have hrecord : s.recordWidth≤rows*s.recordWidth := Nat.le_mul_of_pos_left _ hrows
  have hpower : 2^s.bits≤rows*s.recordWidth :=
    (Nat.le_mul_of_pos_right _ hp).trans hrecord
  have hHbit : s.H≤s.bits := by unfold Shape.bits; omega
  have hH : s.axes*s.guard≤rows*s.recordWidth :=
    hHbit.trans ((Nat.lt_pow_self (n := s.bits) (by decide : 1<2)).le.trans hpower)
  refine ⟨hH,?_⟩
  change 2^(s.H-n*q)*2^(n*b)*2^((s.H-n*b)+s.F+s.active*s.chunk)≤_
  rw [←pow_add,←pow_add]
  apply (Nat.pow_le_pow_right (by decide : 0<2) _).trans hpower
  unfold Shape.bits
  omega

theorem construction_bound (hs : Fin 7 → List Bool) (s : Shape) (n q b rows : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values s.axes s.guard n q b (gap s (n*b) .control) rows i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hG : 0<s.guard) (hq : 0<q) (hb : 0<b) (hcapq : n*q≤s.H) (hcapb : n*b≤s.H)
    (hr : 0<rows) (hp : 0<s.payload) :
    CompactGadgetReservationHeadersOps.bound schedule (initial hs)≤
      15*coefficient*(rows*s.recordWidth) := by
  have hg := geometry_bounds s n q b rows hr hp hcapb
  apply PackedPrefixRepeatHeadersBudget.construction_bound hs s.axes s.guard n q b
    (gap s (n*b) .control) rows (rows*s.recordWidth) hv hc hG hq hb hcapq
    (CompactGadgetReservationHeadersCarvedData.gap_pos _ _ _) _ hg.1 hg.2
  unfold Shape.recordWidth
  positivity

theorem constructs (caller : Tapes t a) (focus : Fin 8 → Fin t)
    (hf : Function.Injective focus) (hs : Fin 7 → List Bool) (s : Shape) (n q b rows : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values s.axes s.guard n q b (gap s (n*b) .control) rows i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hG : 0<s.guard) (hq : 0<q) (hb : 0<b) (hcapq : n*q≤s.H) (hcapb : n*b≤s.H)
    (hr : 0<rows) (hp : 0<s.payload)
    (hi : SharedBank.payload caller focus=PackedPrefixRepeatHeadersPlaced.inputPayload hs) :
    HoareTime (PackedPrefixRepeatHeadersPlaced.program focus hf)
      (fun v => v=CleanSubbank.bank (s := 40) caller)
      (fun v => v=CleanSubbank.bank (s := 40)
        (PackedPrefixRepeatHeadersPlaced.result caller focus s.axes s.guard n q b (gap s (n*b) .control)))
      (15*coefficient*(rows*s.recordWidth)) :=
  (PackedPrefixRepeatHeadersPlaced.constructs caller focus hf hs s.axes s.guard n q b
    (gap s (n*b) .control) rows hv hc hG hq hb hcapq hi).consequence
      (fun _ h => h) (fun _ h => h)
      (construction_bound hs s n q b rows hv hc hG hq hb hcapq hcapb hr hp)

theorem cleans (caller : Tapes t a) (focus : Fin 8 → Fin t)
    (hf : Function.Injective focus) (hs : Fin 7 → List Bool) (s : Shape) (n q b rows : ℕ)
    (hcapb : n*b≤s.H) (hr : 0<rows) (hp : 0<s.payload)
    (hi : SharedBank.payload caller focus=PackedPrefixRepeatHeadersPlaced.inputPayload hs) :
    HoareTime (PackedPrefixRepeatHeadersPlaced.cleanupProgram focus hf)
      (fun v => v=CleanSubbank.bank (s := 40)
        (PackedPrefixRepeatHeadersPlaced.result caller focus s.axes s.guard n q b (gap s (n*b) .control)))
      (fun v => v=CleanSubbank.bank (s := 40) caller)
      (8*(rows*s.recordWidth)) := by
  apply (PackedPrefixRepeatHeadersPlaced.cleans caller focus hf hs s.axes s.guard n q b
    (gap s (n*b) .control) hi).consequence (fun _ h => h) (fun _ h => h)
  apply PackedPrefixRepeatHeadersBudget.cleanup_bound
  · unfold Shape.recordWidth; positivity
  · exact (geometry_bounds s n q b rows hr hp hcapb).2

end
end IntegerMultBounds.Machine.PackedPrefixRepeatHeadersReserved
