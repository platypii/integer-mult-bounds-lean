import IntegerMultBounds.Machine.CompactNativeConjugatedPhase
import IntegerMultBounds.Machine.FixedHeaderSparseBankCopy

/-! The full native conjugated caller has only original13 and immutable ell
metadata after its shared native source is removed. This is the actual sparse
bank constructed and erased by the fixed descriptor copier. -/
namespace IntegerMultBounds.Machine.CompactNativeConjugatedHeaderBank
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageNativeRows (Rows)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {B : ℕ}

abbrev tapes := AllAxisPhaseOriginalScalar.outer+67
def source : Fin tapes := ⟨65,by have := ActivePrefixStageNativeCore.public_le; unfold tapes AllAxisPhaseOriginalScalar.outer AllAxisPhaseOriginalPorts.tapes ActivePrefixStageNativePairSchedule.count; omega⟩
def destination (i : Fin 14) : Fin tapes := Fin.castAdd 67 (AllAxisPhaseOriginalScalar.focus i)
theorem destination_injective : Function.Injective destination := by
  intro i j h
  induction i using Fin.addCases (m:=13) (n:=1) with
  | left i =>
    induction j using Fin.addCases (m:=13) (n:=1) with
    | left j =>
      apply congrArg (Fin.castAdd 1); apply Fin.ext
      have hv := congrArg Fin.val h
      simpa [destination,AllAxisPhaseOriginalScalar.focus,AllAxisPhaseOriginalPorts.focus] using hv
    | right j =>
      have hv := congrArg Fin.val h
      have hp := ActivePrefixStageNativeCore.public_le
      simp [destination,AllAxisPhaseOriginalScalar.focus,AllAxisPhaseOriginalPorts.focus] at hv
      have hi := i.isLt
      unfold AllAxisPhaseOriginalPorts.tapes ActivePrefixStageNativePairSchedule.count at hv
      omega
  | right i =>
    induction j using Fin.addCases (m:=13) (n:=1) with
    | left j =>
      have hv := congrArg Fin.val h
      have hp := ActivePrefixStageNativeCore.public_le
      simp [destination,AllAxisPhaseOriginalScalar.focus,AllAxisPhaseOriginalPorts.focus] at hv
      have hj := j.isLt
      unfold AllAxisPhaseOriginalPorts.tapes ActivePrefixStageNativePairSchedule.count at hv
      omega
    | right j => exact congrArg (Fin.natAdd 13) (Subsingleton.elim i j)

theorem source_ne (i : Fin 14) : destination i≠source := by
  intro h
  have hv := congrArg Fin.val h
  induction i using Fin.addCases (m:=13) (n:=1) with
  | left i => simp [destination,source,AllAxisPhaseOriginalScalar.focus,AllAxisPhaseOriginalPorts.focus] at hv; have := i.isLt; omega
  | right i =>
    have hp := ActivePrefixStageNativeCore.public_le
    simp [destination,source,AllAxisPhaseOriginalScalar.focus] at hv
    unfold AllAxisPhaseOriginalPorts.tapes ActivePrefixStageNativePairSchedule.count at hv
    omega

def initial (d : Inputs s) (ell : ℕ) : Tapes tapes prime :=
  FixedHeaderSparseBankCopy.headerBank destination (AllAxisPhaseOriginalScalar.words d ell)

theorem bank_without_source (d : Inputs s) (xs : Rows d B) (ell : ℕ) :
    setTape (CompactNativeConjugatedPhase.bank d ell xs) source (fun _ => blank) 0=initial d ell := by
  change _=FixedHeaderSparseBankCopy.headerBank destination (AllAxisPhaseOriginalScalar.words d ell)
  apply FixedHeaderSparseBankCopy.headerBank_eq destination destination_injective
  · intro i
    simp only [setTape,Function.update_of_ne (source_ne i)]
    simp only [destination,CompactNativeConjugatedPhase.bank,Tapes.append,Fin.addCases_left]
    exact ⟨(AllAxisPhaseOriginalScalar.source_headers d xs ell i).2,
      (AllAxisPhaseOriginalScalar.source_headers d xs ell i).1⟩
  · intro j hj
    by_cases hs : j=source
    · subst j; simp [setTape]
    have h13 : ¬j.val<13 := by
      intro h
      exact hj (Fin.castAdd 1 ⟨j.val,h⟩) (Fin.ext (by simp only [destination,AllAxisPhaseOriginalScalar.focus,Fin.addCases_left,AllAxisPhaseOriginalPorts.focus,Fin.val_castAdd]))
    have hell : j.val≠AllAxisPhaseOriginalPorts.tapes := by
      intro h
      exact hj (Fin.natAdd 13 (0 : Fin 1)) (Fin.ext (by simp only [destination,AllAxisPhaseOriginalScalar.focus,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Nat.add_zero]; exact h.symm))
    have h65 : j.val≠65 := by intro h; exact hs (Fin.ext h)
    simp only [setTape,Function.update_of_ne hs]
    induction j using Fin.addCases (m:=AllAxisPhaseOriginalScalar.outer) (n:=67) with
    | right j => simp [CompactNativeConjugatedPhase.bank,Tapes.append,FixedHeaderBankCopy.empty]
    | left j =>
      induction j using Fin.addCases (m:=AllAxisPhaseOriginalPorts.tapes) (n:=1) with
      | right j => have := j.isLt; simp only [Fin.val_castAdd,Fin.val_natAdd] at hell; omega
      | left j =>
        induction j using Fin.addCases (m:=ActivePrefixStageNative.tapes) (n:=1) with
        | right j => simp [CompactNativeConjugatedPhase.bank,AllAxisPhaseOriginalScalar.caller,ActivePrefixStageNativePairRun.bank,Tapes.append,SharedBank.empty]
        | left j =>
          simp only [CompactNativeConjugatedPhase.bank,AllAxisPhaseOriginalScalar.caller,
            ActivePrefixStageNativePairRun.bank,Tapes.append,Fin.addCases_left,ActivePrefixStageNativeRows.bank]
          by_cases h66 : j.val<66
          · have hlt : j.val<65 := by simp only [Fin.val_castAdd] at h65; omega
            have hn : ¬j.val<13 := by simpa only [Fin.val_castAdd] using h13
            simp only [SharedBankStageInput.raw,dite_eq_left h66]
            have he : (⟨j.val,h66⟩ : Fin 66)=Fin.castAdd 1 ⟨j.val,hlt⟩ := Fin.ext rfl
            simp only [he,ActivePrefixStageNativeRows.core,Tapes.append,Fin.addCases_left]
            by_cases h28 : j.val<28
            · simp [ActivePrefixStageHeadersRouting.caller,ActivePrefixStageHeadersPlaced.lift,
                ActivePrefixStageHeadersData.initial,h28,hn]
            · simp [ActivePrefixStageHeadersRouting.caller,ActivePrefixStageHeadersPlaced.lift,h28]
          · simp only [SharedBankStageInput.raw,dite_eq_right h66,and_self]

theorem bank_source (d : Inputs s) (xs : Rows d B) (ell : ℕ) :
    (CompactNativeConjugatedPhase.bank d ell xs).tape source=
      SymbolTriplePlaced.native ActivePrefixStageNative.ha (ActivePrefixStageNativeRows.flat xs) ∧
    (CompactNativeConjugatedPhase.bank d ell xs).head source=0 := by
  let i : Fin ActivePrefixStageNative.tapes := ⟨65,by have := ActivePrefixStageNativeCore.public_le; omega⟩
  have he : source=Fin.castAdd 67 (Fin.castAdd 1 (Fin.castAdd 1 i)) := Fin.ext rfl
  simp only [he,CompactNativeConjugatedPhase.bank,AllAxisPhaseOriginalScalar.caller,
    ActivePrefixStageNativePairRun.bank,Tapes.append,Fin.addCases_left,ActivePrefixStageNativeRows.bank,
    SharedBankStageInput.raw]
  have h66 : i.val<66 := by dsimp [i]; omega
  simp only [dite_eq_left h66]
  have hi : (⟨i.val,h66⟩ : Fin 66)=Fin.natAdd 65 (0 : Fin 1) := Fin.ext rfl
  simp only [hi,ActivePrefixStageNativeRows.core,Tapes.append,Fin.addCases_right]
  trivial

/-- Removing the native source leaves the same metadata for every row word. -/
theorem metadata_independent (d : Inputs s) (xs : Rows d B) (ys : Rows d B) (ell : ℕ) :
    setTape (CompactNativeConjugatedPhase.bank d ell xs) source (fun _ => blank) 0=
      setTape (CompactNativeConjugatedPhase.bank d ell ys) source (fun _ => blank) 0 := by
  rw [bank_without_source,bank_without_source]

theorem room {t : ℕ} : 0<t+14 := by omega
theorem header_room : 14≤tapes := by
  have := ActivePrefixStageNativeCore.public_le
  unfold tapes AllAxisPhaseOriginalScalar.outer AllAxisPhaseOriginalPorts.tapes ActivePrefixStageNativePairSchedule.count
  omega

def setup {t : ℕ} (focus : Fin 14 → Fin t) :=
  FixedHeaderSparseBankCopy.program (a:=prime) room focus destination destination_injective header_room
def cleanup (t : ℕ) :=
  FixedHeaderSparseBankCopy.cleanup (a:=prime) (room (t:=t)) destination destination_injective header_room

theorem setup_runs {t : ℕ} (focus : Fin 14 → Fin t) (v : Tapes t prime)
    (d : Inputs s) (ell : ℕ)
    (hf : ∀ i,v.tape (focus i)=RadixZeroFill.encodedBinary (AllAxisPhaseOriginalScalar.words d ell i))
    (hh : ∀ i,v.head (focus i)=1) :
    HoareTime (setup focus) (fun z => z=v.append (FixedHeaderBankCopy.empty tapes))
      (fun z => z=v.append (initial d ell))
      (FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (AllAxisPhaseOriginalScalar.words d ell)) :=
  FixedHeaderSparseBankCopy.constructs room focus destination destination_injective header_room v _ hf hh

theorem cleanup_runs {t : ℕ} (v : Tapes t prime) (d : Inputs s) (ell : ℕ) :
    HoareTime (cleanup t) (fun z => z=v.append (initial d ell))
      (fun z => z=v.append (FixedHeaderBankCopy.empty tapes))
      (FixedHeaderBankCopy.cleanupCost (t:=t) (AllAxisPhaseOriginalScalar.words d ell)) :=
  FixedHeaderSparseBankCopy.cleans room destination destination_injective header_room v _

end
end IntegerMultBounds.Machine.CompactNativeConjugatedHeaderBank
