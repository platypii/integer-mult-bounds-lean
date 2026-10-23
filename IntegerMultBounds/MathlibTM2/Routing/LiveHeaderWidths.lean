module

public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderInputFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationData
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthData
public import IntegerMultBounds.MathlibTM2.Routing.FieldPairClean

/-! Actual width generation inside the live header/descriptor bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev liveHeaderConfigurationT := repairLiveHeaderT + 6

def liveHeaderWidthJobs (Lr Lm rb wy : ℕ) : List (BinaryFieldJob liveHeaderConfigurationT) :=
  fieldPairJobs (repairLiveHeaderRaw (repairSetupSource (.inr .row)))
    (repairLiveHeaderRaw (repairSetupSource (.inr .keyMask))) Lr Lm rb wy

def liveHeaderWidthBank {A : ℕ} (rb wy : ℕ)
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) :=
  fieldPairGenerated (repairLiveHeaderRaw (repairSetupSource (.inr .row)))
    (repairLiveHeaderRaw (repairSetupSource (.inr .keyMask))) rb wy bank

theorem liveHeaderWidths_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P liveHeaderConfigurationT Q A U) (Lr Lm rb wy : ℕ)
    (hr : rb < 2 ^ Lr) (hm : wy < 2 ^ Lm)
    (v : HS liveHeaderConfigurationT Q A U) (S : Stacks liveHeaderConfigurationT A)
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm wy)
    (hscratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R (fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R (fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .keyMask)))) = []) :
    ∃ (v' : HS liveHeaderConfigurationT Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * wy + 11) + 2 * wy + 6) + 1 ∧
      Exec body (binaryFieldBatch (liveHeaderWidthJobs Lr Lm rb wy)) (mk v S) m
        (mk v' { S with R := liveHeaderWidthBank rb wy S.R }) := by
  exact fieldPair_exec body _ _ (repairLiveHeaderRaw_injective.ne (by simp [repairSetupSource]))
    Lr Lm rb wy hr hm v S hrowWidth hmaskWidth hscratch hrow hmask

end
end IntegerMultBounds.MathlibTM2.Routing
