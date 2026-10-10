import IntegerMultBounds.Machine.AllAxisPhaseOriginalScalar

/-! Binary endpoint-character scratch preparation from retained physical
original geometry and immutable polynomial precision. Every caller tape is
framed; all copied and computed descriptors are physically erased. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageHeadersData (Order)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s : Shape} {t : ℕ}

abbrev destination := AllAxisPhaseOriginalScalar.destination
abbrev destination_injective := AllAxisPhaseOriginalScalar.destination_injective

def words (v : Stage s) (rows ell : ℕ) (i : Fin 14) : List Bool :=
  Fin.addCases (fun i : Fin 13 => bits (ActivePrefixStageHeadersData.originalValues v rows i))
    (fun _ : Fin 1 => bits ell) i

def tail (ell : ℕ) : Tapes 24 2 :=
  setTape (FixedHeaderBankCopy.empty 24) 22 (RadixZeroFill.encodedBinary (bits ell)) 1

def initial (v : Stage s) (rows ell : ℕ) : Tapes 67 2 :=
  (ActiveRepairRankHeadersCommands.bank (ActivePrefixStageHeadersData.initial v rows)).append (tail ell)
def ready (order : Order) (v : Stage s) (rows ell : ℕ) : Tapes 67 2 :=
  (ActiveRepairRankHeadersCommands.bank (ActivePrefixStageHeadersData.finished order v rows)).append (tail ell)

theorem initial_eq (v : Stage s) (rows ell : ℕ) :
    initial v rows ell=FixedHeaderSparseBankCopy.headerBank destination (words v rows ell) := by
  apply FixedHeaderSparseBankCopy.headerBank_eq destination destination_injective (words v rows ell)
  · intro i
    induction i using Fin.addCases (m:=13) (n:=1) with
    | left i =>
      simp [initial,tail,destination,AllAxisPhaseOriginalScalar.destination,
        AllAxisPhaseOriginalPorts.destination,words,Tapes.append,
        ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
        ActiveRepairRankHeadersCommands.caller,ActivePrefixStageHeadersData.initial,i.isLt]
    | right i =>
      simp only [destination,AllAxisPhaseOriginalScalar.destination,words,Fin.addCases_right]
      rw [show (65 : Fin 67)=Fin.natAdd 43 (22 : Fin 24) from rfl]
      change (tail ell).head 22=1 ∧ (tail ell).tape 22=RadixZeroFill.encodedBinary (bits ell)
      simp [tail,setTape]
  · intro j hj
    have h13 : 13≤j.val := by
      by_contra h
      have hlt : j.val<13 := by omega
      exact hj (Fin.castAdd 1 ⟨j.val,hlt⟩) (by simp only [destination,AllAxisPhaseOriginalScalar.destination,Fin.addCases_left,AllAxisPhaseOriginalPorts.destination]; rfl)
    have h65 : j≠(65 : Fin 67) := by
      intro h
      exact hj (Fin.natAdd 13 (0 : Fin 1)) (by change (65 : Fin 67)=j; exact h.symm)
    induction j using Fin.addCases (m:=43) (n:=24) with
    | left j =>
      induction j using Fin.addCases (m:=28) (n:=15) with
      | left j =>
        have hn : ¬j.val<13 := by simp only [Fin.val_castAdd] at h13; omega
        simp [initial,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
          ActiveRepairRankHeadersCommands.caller,ActivePrefixStageHeadersData.initial,Tapes.append,hn]
      | right j => simp [initial,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,SharedBank.empty]
    | right j =>
      have hn : j≠(22 : Fin 24) := by
        intro h; subst j; exact h65 rfl
      simp [initial,tail,Tapes.append,setTape,hn,FixedHeaderBankCopy.empty]

def copy (focus : Fin 14 → Fin t) := FixedHeaderSparseBankCopy.program (a:=2)
  (by omega : 0<t+14) focus destination destination_injective (by decide : 14≤67)
def erase := FixedHeaderSparseBankCopy.cleanup (a:=2)
  (by omega : 0<t+14) destination destination_injective (by decide : 14≤67)

theorem copy_runs (focus : Fin 14 → Fin t) (caller : Tapes t 2)
    (v : Stage s) (rows ell : ℕ)
    (hs : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary (words v rows ell i))
    (hh : ∀ i,caller.head (focus i)=1) :
    HoareTime (copy focus)
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=caller.append (initial v rows ell))
      (FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (words v rows ell)) := by
  have h := FixedHeaderSparseBankCopy.constructs (by omega : 0<t+14) focus destination
    destination_injective (by decide : 14≤67) caller (words v rows ell) hs hh
  rwa [←initial_eq] at h

theorem erase_runs (caller : Tapes t 2) (v : Stage s) (rows ell : ℕ) :
    HoareTime (erase (t:=t)) (fun z => z=caller.append (initial v rows ell))
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (FixedHeaderBankCopy.cleanupCost (t:=t) (words v rows ell)) := by
  have h := FixedHeaderSparseBankCopy.cleans (by omega : 0<t+14) destination
    destination_injective (by decide : 14≤67) caller (words v rows ell)
  rwa [←initial_eq] at h

end
end IntegerMultBounds.Machine.NativeEndpointCharacterHeaders
