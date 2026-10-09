import IntegerMultBounds.Machine.CompactSpectatorLeafHeaders
import IntegerMultBounds.Machine.ButterflySpectatorSemantics

/-! The immutable scalar remains baseline q. Twice the physically generated
full global bit dimension is added only to the private precision reservation.
The source must already contain the explicitly enlarged signed fields; this
machine neither resizes nor renormalizes coefficients between arithmetic axes. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafGuardHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd)
open CompactSpectatorLeafHeaders (initial)
open ButterflyIndependentGuardHeaders (reservation)

def schedule : List Op := [cmd (.add 3 0 (by decide)),cmd (.add 3 0 (by decide))]

theorem eval_eq (s : Shape) (rows ell q rho ordinal count : ℕ) :
    execute schedule (initial s rows ell q rho ordinal count)=
      initial s rows ell (reservation s.bits q) rho ordinal count := by
  funext i
  fin_cases i <;> simp [schedule,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,Function.update,reservation]
  omega

theorem valid (s : Shape) (rows ell q rho ordinal count : ℕ) :
    validSchedule schedule (initial s rows ell q rho ordinal count) := by
  simp [schedule,validSchedule,ButterflyAxisHeadersArithmetic.valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,initial,Function.update]

theorem runs (s : Shape) (rows ell q rho ordinal count : ℕ) :
    HoareTime (compile (a:=2) schedule).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial s rows ell q rho ordinal count))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial s rows ell (reservation s.bits q) rho ordinal count))
      (scheduleCost schedule (initial s rows ell q rho ordinal count)) := by
  have hh := schedule_runs (a:=2) schedule (initial s rows ell q rho ordinal count) (valid s rows ell q rho ordinal count)
  rwa [eval_eq] at hh

theorem stored_width (s : Shape) (q : ℕ) : ButterflyGuard.width (reservation s.bits q) s.bits=q+4*s.bits+4 := by
  unfold ButterflyGuard.width ButterflyGuard.halfWidth reservation
  omega

/-- Readiness follows from actual signed field lengths, rather than changing
what the retained baseline precision descriptor means. -/
theorem readiness (s : Shape) (rows ell q : ℕ) (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ∀ i,(f i).1.length=q+4*s.bits+4 ∧ (f i).2.length=q+4*s.bits+4) :
    ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f := by
  intro i
  simpa only [stored_width] using hw i

theorem width_overhead (s : Shape) (q : ℕ) :
    ButterflyGuard.width (reservation s.bits q) s.bits≤2*ButterflyGuard.width q s.bits := by
  unfold ButterflyGuard.width ButterflyGuard.halfWidth reservation
  omega


/-- At the actual baseline precision6b, the two-pass stored field remains a
fixed multiple of the original multiplier precision scale. -/
theorem multiplier_width (s : Shape) (b : ℕ) (hb : 1≤b) (hD : s.bits≤b) :
    ButterflyGuard.width (reservation s.bits (6*b)) s.bits≤14*b := by
  rw [stored_width]
  omega

end
end IntegerMultBounds.Machine.CompactSpectatorLeafGuardHeaders
