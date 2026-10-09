import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedSchedule

/-! Physical carved-header routing through the unchanged spectator bank. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedRouting
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersCarvedData
open CompactGadgetReservationHeadersRouting (bank placement active extra)
variable {t a : ℕ}

def program (f : Front) (t : ℕ) := Placement.placed
  (CompactGadgetReservationHeadersCarvedSchedule.program (a := a) f) (placement t)
def headerWords (s : Shape) (rows w : ℕ) (f : Front) : Fin 4 → List Bool :=
  fun i => RecursiveChildQuotientsConstant.bits
    (BinaryRadixRangePrepare.values (s.prefixRange rows f) (gap s w f) (suffix s w) w i)
theorem header_values (s : Shape) (rows w : ℕ) (f : Front) :
    ∀ i, Counter.value (headerWords s rows w f i) =
      BinaryRadixRangePrepare.values (s.prefixRange rows f) (gap s w f) (suffix s w) w i :=
  fun _ => RecursiveChildQuotientsConstant.bits_value _
theorem header_canonical (s : Shape) (rows w : ℕ) (f : Front) :
    ∀ i, GrowingCounterData.Canonical (headerWords s rows w f i) :=
  fun _ => RecursiveChildQuotientsConstant.bits_canonical _

theorem constructs (hs : Fin 7 → List Bool) (s : Shape) (n rows w : ℕ) (f : Front)
    (spectators : Tapes t a)
    (hv : ∀ i, Counter.value (hs i) = CompactGadgetReservationHeadersCarvedSchedule.originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hw : w ≤ s.H) :
    HoareTime (program (a := a) f t)
      (fun v => v = bank (CompactGadgetReservationHeadersCarvedSchedule.initial hs w) spectators)
      (fun v => v = bank (CompactGadgetReservationHeadersCarvedSchedule.finished hs s n rows w f) spectators)
      (CompactGadgetReservationHeadersOps.bound (CompactGadgetReservationHeadersCarvedSchedule.schedule f)
        (CompactGadgetReservationHeadersCarvedSchedule.initial hs w)) := by
  have hr := Placement.hoare_at
    (CompactGadgetReservationHeadersCarvedSchedule.constructs hs s n rows w f hv hc hK hd hG hw)
    (placement t) (bank (CompactGadgetReservationHeadersCarvedSchedule.initial hs w) spectators) (active _ _)
  refine hr.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,extra]
  simpa only [active,extra] using Placement.view (placement t)
    (bank (CompactGadgetReservationHeadersCarvedSchedule.finished hs s n rows w f) spectators)

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedRouting
