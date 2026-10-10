import IntegerMultBounds.Machine.NativeEndpointCharacterPrepare

/-! Copy the actual raw geometry and immutable ell/precision into private
endpoint-character storage. The caller, including every unrelated role and
controller tape, remains literally unchanged. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterCopy
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
variable {s : Shape} {t : ℕ}

def index (i : Fin 15) : Fin 28 :=
  ⟨if i.val<13 then i.val else i.val+4,by have := i.isLt; split_ifs <;> omega⟩
def destination (i : Fin 15) : Fin 67 := Fin.castAdd 24 (Fin.castAdd 15 (index i))
theorem destination_injective : Function.Injective destination := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [destination,index,Fin.val_castAdd] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def words (v : Stage s) (parentRows ell p : ℕ) (i : Fin 15) :=
  RecursiveChildQuotientsConstant.bits
    ((NativeEndpointCharacterPrepare.raw v parentRows ell p (index i)).getD 0)

theorem initial_eq (v : Stage s) (parentRows ell p : ℕ) :
    NativeEndpointCharacterPrepare.input v parentRows ell p=
      FixedHeaderSparseBankCopy.headerBank destination (words v parentRows ell p) := by
  apply FixedHeaderSparseBankCopy.headerBank_eq destination destination_injective (words v parentRows ell p)
  · intro i
    fin_cases i <;> constructor <;> rfl
  · intro j hj
    have hsmall : ¬j.val<13 := by
      intro h
      exact hj ⟨j.val,by omega⟩ (by apply Fin.ext; simp [destination,index,h])
    have h17 : j.val≠17 := by
      intro h
      exact hj (13 : Fin 15) (Fin.ext (by simpa [destination,index] using h.symm))
    have h18 : j.val≠18 := by
      intro h
      exact hj (14 : Fin 15) (Fin.ext (by simpa [destination,index] using h.symm))
    induction j using Fin.addCases (m:=43) (n:=24) with
    | left j =>
      induction j using Fin.addCases (m:=28) (n:=15) with
      | left j =>
        have hr : NativeEndpointCharacterPrepare.raw v parentRows ell p j=none := by
          have hn : ¬j.val<13 := by simpa only [Fin.val_castAdd] using hsmall
          have hn17 : j.val≠17 := by simpa only [Fin.val_castAdd] using h17
          have hn18 : j.val≠18 := by simpa only [Fin.val_castAdd] using h18
          fin_cases j <;> simp_all [NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw]
        simp only [NativeEndpointCharacterPrepare.input,ActiveRepairRankHeadersCommands.bank,
          CleanSubbank.bank,Tapes.append,Fin.addCases_left,ActiveRepairRankHeadersCommands.caller,hr]
        trivial
      | right j => simp [NativeEndpointCharacterPrepare.input,ActiveRepairRankHeadersCommands.bank,
        CleanSubbank.bank,Tapes.append,SharedBank.empty,FixedHeaderBankCopy.empty]
    | right j => simp [NativeEndpointCharacterPrepare.input,ActiveRepairRankHeadersCommands.bank,
        CleanSubbank.bank,Tapes.append,SharedBank.empty,FixedHeaderBankCopy.empty]

def program (focus : Fin 15 → Fin t) := FixedHeaderSparseBankCopy.program (a:=2)
  (by omega : 0<t+15) focus destination destination_injective (by decide : 15≤67)

theorem runs (focus : Fin 15 → Fin t) (caller : Tapes t 2) (v : Stage s)
    (parentRows ell p : ℕ)
    (hs : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary (words v parentRows ell p i))
    (hh : ∀ i,caller.head (focus i)=1) :
    HoareTime (program focus) (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=caller.append (NativeEndpointCharacterPrepare.input v parentRows ell p))
      (FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 15) (words v parentRows ell p)) := by
  have h := FixedHeaderSparseBankCopy.constructs (by omega : 0<t+15) focus destination
    destination_injective (by decide : 15≤67) caller (words v parentRows ell p) hs hh
  rwa [←initial_eq] at h

end
end IntegerMultBounds.Machine.NativeEndpointCharacterCopy
