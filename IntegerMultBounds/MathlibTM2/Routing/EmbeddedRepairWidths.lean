module

public import IntegerMultBounds.MathlibTM2.Routing.FieldPairClean
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthData
public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationData

/-! Row/key-mask generation for any injectively embedded repair bank.
Only the two raw field tapes change; all other inner and outer tapes survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {N A : ℕ} (e : Fin repairT → Fin N) (he : Function.Injective e)

def embeddedRepairWidthBank (rb wy : ℕ) (bank : Fin (N + 6) → List (Fin (A + 4))) :=
  fieldPairGenerated (e (repairSetupSource (.inr .row))) (e (repairSetupSource (.inr .keyMask))) rb wy bank

theorem embeddedRepairWidthBank_keep (rb wy : ℕ) (bank : Fin (N + 6) → List (Fin (A + 4)))
    (i : Fin N) (hr : i ≠ e (repairSetupSource (.inr .row)))
    (hm : i ≠ e (repairSetupSource (.inr .keyMask))) :
    embeddedRepairWidthBank e rb wy bank (fieldCore i) = bank (fieldCore i) := by
  simp [embeddedRepairWidthBank, fieldPairGenerated, fieldCore_injective.eq_iff, hr, hm]

include he in
theorem embeddedRepairWidthBank_raw (rb wy : ℕ) (bank : Fin (N + 6) → List (Fin (A + 4)))
    (i : Fin repairT) (hr : i ≠ repairSetupSource (.inr .row)) (hm : i ≠ repairSetupSource (.inr .keyMask)) :
    embeddedRepairWidthBank e rb wy bank (fieldCore (e i)) = bank (fieldCore (e i)) :=
  embeddedRepairWidthBank_keep e rb wy bank (e i) (he.ne hr) (he.ne hm)

include he in
theorem embeddedRepairWidthBank_project (rb wy : ℕ) (bank : Fin (N + 6) → List (Fin (A + 4))) :
    (fun i => embeddedRepairWidthBank e rb wy bank (fieldCore (e i))) =
      repairWidthBank rb wy (fun i => bank (fieldCore (e i))) := by
  funext i
  simp only [embeddedRepairWidthBank, fieldPairGenerated, repairWidthBank,
    Function.update_apply, fieldCore_injective.eq_iff, he.eq_iff]

include he in
theorem RepairPendingConfigurationData.embeddedWidths (p : Par) (X rb : ℕ)
    {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin (N + 6) → List (Fin (A + 4))}
    (data : RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => bank (fieldCore (e i)))) :
    RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => embeddedRepairWidthBank e rb p.wy bank (fieldCore (e i))) := by
  rw [embeddedRepairWidthBank_project e he]
  exact data.widthsGenerated p X rb

include he in
theorem embeddedRepairWidths_exec {Q : ℕ} {P U : Type}
    (body : P → Pr P (N + 6) Q A U) (Lr Lm rb wy : ℕ)
    (hr : rb < 2 ^ Lr) (hm : wy < 2 ^ Lm)
    (v : HS (N + 6) Q A U) (S : Stacks (N + 6) A)
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm wy)
    (hscratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R (fieldCore (e (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R (fieldCore (e (repairSetupSource (.inr .keyMask)))) = []) :
    ∃ (v' : HS (N + 6) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * wy + 11) + 2 * wy + 6) + 1 ∧
      Exec body (binaryFieldBatch (fieldPairJobs (e (repairSetupSource (.inr .row)))
        (e (repairSetupSource (.inr .keyMask))) Lr Lm rb wy)) (mk v S) steps
        (mk v' { S with R := embeddedRepairWidthBank e rb wy S.R }) :=
  fieldPair_exec body _ _ (he.ne (by simp [repairSetupSource])) Lr Lm rb wy hr hm v S
    hrowWidth hmaskWidth hscratch hrow hmask

end
end IntegerMultBounds.MathlibTM2.Routing
