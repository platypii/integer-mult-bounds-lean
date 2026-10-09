import IntegerMultBounds.Machine.ActivePrefixStageWidthOriginal
import IntegerMultBounds.Machine.ActivePrefixStageSingletonDispatch
import IntegerMultBounds.Machine.ActivePrefixStageDispatchSelected

/-! Extend a leading-bank clean routine with a separate width flag. The new
flag is framed and all native private tapes remain physically blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimePlaced
noncomputable section
variable {k n q a B : ℕ}

def program (M : Program n q a) (hn : k≤n) :=
  Placement.placed M (CleanSubbank.placement (Fin.castLE hn) (Fin.castAdd 1) (Fin.castAdd_injective _ _))

theorem runs (M : Program n q a) (hn : k≤n) (v w : Tapes k a)
    (h : HoareTime M (fun x => x=SharedBankStageInput.raw v n)
      (fun x => x=SharedBankStageInput.raw w n) B) :
    HoareTime (program M hn)
      (fun x => x=CleanSubbank.bank (s:=n) (CleanSubbank.bank (s:=1) v))
      (fun x => x=CleanSubbank.bank (s:=n) (CleanSubbank.bank (s:=1) w)) B := by
  refine CleanSubbank.realizes M (Fin.castLE hn) (Fin.castAdd 1)
    (Fin.castLE_injective hn) (Fin.castAdd_injective _ _) _ _ _ _ B ?_ ?_ ?_ ?_ ?_ h
  · rw [SharedBankRawCompose.payload_raw _ (Fin.castLE hn) (fun _ => rfl),CleanSubbank.payload_bank]
  · rw [SharedBankRawCompose.payload_raw _ (Fin.castLE hn) (fun _ => rfl),CleanSubbank.payload_bank]
  · exact SharedBankRawCompose.strip_raw _ _ (fun _ => rfl)
  · exact SharedBankRawCompose.strip_raw _ _ (fun _ => rfl)
  · rw [CleanSubbank.strip_bank,CleanSubbank.strip_bank]

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimePlaced
