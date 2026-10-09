import IntegerMultBounds.Machine.CompactGadgetReservationHeadersEndpoint
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersRows

/-! Exact header constructor routing with a retained spectator bank between
its permanent header tapes and its shared fifteen private tapes. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersRouting
noncomputable section
variable {t a : ℕ}

def placement (t : ℕ) : Fin (40+t) ≃ Fin ((25+t)+15) where
  toFun := Fin.addCases (m := 40) (n := t)
    (Fin.addCases (m := 25) (n := 15) (fun i : Fin 25 => Fin.castAdd 15 (Fin.castAdd t i))
      (fun i : Fin 15 => Fin.natAdd (25+t) i))
    (fun i : Fin t => Fin.castAdd 15 (Fin.natAdd 25 i))
  invFun := Fin.addCases (m := 25+t) (n := 15)
    (Fin.addCases (m := 25) (n := t) (fun i : Fin 25 => Fin.castAdd t (Fin.castAdd 15 i))
      (fun i : Fin t => Fin.natAdd 40 i))
    (fun i : Fin 15 => Fin.castAdd t (Fin.natAdd 25 i))
  left_inv i := by
    induction i using Fin.addCases with
    | left i => induction i using (Fin.addCases (m := 25) (n := 15)) <;> simp only [Fin.addCases_left,Fin.addCases_right]
    | right i => simp only [Fin.addCases_left,Fin.addCases_right]
  right_inv i := by
    induction i using Fin.addCases with
    | left i => induction i using (Fin.addCases (m := 25) (n := t)) <;> simp only [Fin.addCases_left,Fin.addCases_right]
    | right i => simp only [Fin.addCases_left,Fin.addCases_right]

def bank (xs : CompactGadgetReservationHeadersWords.Words) (spectators : Tapes t a) :=
  CompactGadgetReservationHeadersCore.bank ((CompactGadgetReservationHeadersWords.common xs).append spectators)
def program (f : CompactGadgetReservationShape.Front) (t : ℕ) :=
  Placement.placed (CompactGadgetReservationHeadersSchedule.program (a := a) f) (placement t)

theorem active (xs : CompactGadgetReservationHeadersWords.Words) (spectators : Tapes t a) :
    Placement.active (placement t) (bank xs spectators) = CompactGadgetReservationHeadersWords.bank xs := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using (Fin.addCases (m := 25) (n := 15)) with
  | left i => simp only [placement,Equiv.coe_fn_mk,bank,CompactGadgetReservationHeadersCore.bank,
      CleanSubbank.bank,Tapes.append,Fin.addCases_left,]
  | right i => simp only [placement,Equiv.coe_fn_mk,bank,CompactGadgetReservationHeadersCore.bank,
      CleanSubbank.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right]

theorem extra (xs : CompactGadgetReservationHeadersWords.Words) (spectators : Tapes t a) :
    Placement.extra (placement t) (bank xs spectators) = spectators := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [placement,Equiv.coe_fn_mk,bank,CompactGadgetReservationHeadersCore.bank,
    CleanSubbank.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right]

theorem constructs (hs : Fin 7 → List Bool) (s : CompactGadgetReservationShape.Shape)
    (n rows : ℕ) (f : CompactGadgetReservationShape.Front) (spectators : Tapes t a)
    (hv : ∀ i, Counter.value (hs i) = CompactGadgetReservationHeadersSchedule.originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hn : n ≤ s.axes) :
    HoareTime (program (a := a) f t)
      (fun v => v = bank (CompactGadgetReservationHeadersSchedule.initial hs) spectators)
      (fun v => v = bank (CompactGadgetReservationHeadersSchedule.finished hs s n rows f) spectators)
      (CompactGadgetReservationHeadersOps.bound (CompactGadgetReservationHeadersSchedule.schedule f)
        (CompactGadgetReservationHeadersSchedule.initial hs)) := by
  have hr := Placement.hoare_at (CompactGadgetReservationHeadersSchedule.constructs hs s n rows f hv hc hK hd hG hn)
    (placement t) (bank (CompactGadgetReservationHeadersSchedule.initial hs) spectators) (active _ _)
  refine hr.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,extra]
  simpa only [active,extra] using Placement.view (placement t)
    (bank (CompactGadgetReservationHeadersSchedule.finished hs s n rows f) spectators)

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersRouting
