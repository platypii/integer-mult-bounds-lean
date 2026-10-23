module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleFixedProgram
public import IntegerMultBounds.MathlibTM2.Routing.FieldPairFixedProgram
public import IntegerMultBounds.MathlibTM2.Routing.JointBankAllSourceProfilesRepair

/-! One generated/placed repair program for every geometry, row count, binary
width and requested source map. All numerical inputs remain metadata on tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K : ℕ} {P P' U : Type}
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "ep₀" => inactiveClassifierPlacementEmbed (t₀ := t₀)
local notation "slot₀" => inactiveClassifierPlacementSlot (t₀ := t₀)

def allSourcePlacedFixedProgram
    (keySrc raw activity : Fin repairT)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQplacement : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ TP₀) (ι : P → P') : Pr P' TP₀ Q (prime + K) U :=
  (.seq (binaryScheduleFixedChain slot₀ inactiveClassifierPlacementSlot_injective hd pay hhd hQplacement hT (reservoirExchangeOrder false))
        (.seq (embProg ep₀ ι (.seq (classifierPairProgram classifierBankReg
          (classifierBankRepeat inactiveClassifierTemporary inactiveClassifierPhase) classifierBankPad)
        (.seq (embProg classifierCore id (.seq (fieldPairFixedProgram (inactiveProfileHeaderRaw (repairSetupSource (.inr .row)))
          (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask))))
        (.seq (embProg (fieldCore (N := inactiveProfileHeaderT)) id (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq (liveCoordinateProfilesProgram keySrc raw activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw)))))
          (metadataClean [fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .row))),
            fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))]))))
          (metadataClean [classifierCore inactiveClassifierTemporary, classifierCore inactiveClassifierPhase])))) (binaryScheduleFixedChain slot₀ inactiveClassifierPlacementSlot_injective hd pay hhd hQplacement hT (reservoirExchangeOrder true))))

theorem allSourcePlacedProgram_eq {n R B : ℕ}
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQplacement : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ TP₀)
    (spec : Fin 3 → BlockExchangeSpec n) (hR : 0 < R) (hB : 0 < B)
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (keySrc raw activity : Fin repairT)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (Lr Lm nr nm : ℕ) (ι : P → P') :
    let calls := binaryScheduleCalls slot₀ inactiveClassifierPlacementSlot_injective hd pay hhd hpay hQplacement hT
      spec hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue
    ((.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg ep₀ ι (.seq (classifierPairProgram classifierBankReg
          (classifierBankRepeat inactiveClassifierTemporary inactiveClassifierPhase) classifierBankPad)
        (.seq (embProg classifierCore id (.seq (binaryFieldBatch (fieldPairJobs (inactiveProfileHeaderRaw (repairSetupSource (.inr .row)))
          (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask))) Lr Lm nr nm))
        (.seq (embProg (fieldCore (N := inactiveProfileHeaderT)) id (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq (liveCoordinateProfilesProgram keySrc raw activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw)))))
          (metadataClean [fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .row))),
            fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))]))))
          (metadataClean [classifierCore inactiveClassifierTemporary, classifierCore inactiveClassifierPhase])))) (binaryExchangeChain calls (reservoirExchangeOrder true)))) : Pr P' TP₀ Q (prime + K) U) =
      allSourcePlacedFixedProgram keySrc raw activity hQ hA hd pay hhd hQplacement hT ι := by
  simp only [binaryScheduleCalls_chain, fieldPairJobs_program, allSourcePlacedFixedProgram]

end
end IntegerMultBounds.MathlibTM2.Routing
