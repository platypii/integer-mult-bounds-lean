import IntegerMultBounds.Machine.ArbitraryWidthPaddedPieceShared
import IntegerMultBounds.Machine.ArbitraryWidthElementaryShared
import IntegerMultBounds.Machine.FixedHeaderSparseBankCopy

/-! Literal blank-ready recursive banks and their six retained headers. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersCore
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50NodeSegments (payloadCount)
open ArbitrarySliceCall (rootCount commonCount headerSlot)

abbrev blankTape : ℤ → Fin (prime+4) := fun _ => blank
abbrev emptyOne := SharedBank.empty 1 prime
abbrev emptyTwo := SharedBank.empty 2 prime

def rootPrivate (hs : Fin 6 → List Bool) :=
  ArbitrarySliceCall.rootBank (Shared50RecursiveCallSemantics.childRoles blankTape)
    hs blankTape 0 emptyOne emptyOne emptyTwo

theorem blank_roles : Shared50RecursiveCallSemantics.childRoles blankTape =
    SharedBank.empty payloadCount prime :=
  SharedPlacementAlphabet.setTape_self _ _

def commonPrivate (hs : Fin 6 → List Bool) :=
  (SharedBank.empty payloadCount prime).append
    (((SharedBank.empty 1 prime).append (RecursiveShiftRoleBank.headers hs)).append
      (SharedBank.empty 7 prime))

theorem rootPrivate_eq (hs : Fin 6 → List Bool) :
    rootPrivate hs = SharedBankStageInput.raw (commonPrivate hs) rootCount := by
  unfold rootPrivate ArbitrarySliceCall.rootBank
  rw [blank_roles]
  unfold Shared50RecursiveBank.bank RecursiveCallBank.bank RecursiveShiftRoleBank.common commonPrivate
  congr 3
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem header_injective : Function.Injective headerSlot := by
  intro i j he
  have hv := congrArg Fin.val he
  change payloadCount+(1+i.val) = payloadCount+(1+j.val) at hv
  exact Fin.ext (by omega)

theorem root_target (hs : Fin 6 → List Bool) (i : Fin 6) :
    (rootPrivate hs).head (headerSlot i) = 1 ∧
    (rootPrivate hs).tape (headerSlot i) = RadixZeroFill.encodedBinary (hs i) :=
  ArbitraryWidthPieceSetup.root_header _ hs blankTape 0 emptyOne emptyOne emptyTwo i

theorem common_blank (hs : Fin 6 → List Bool) (j : Fin commonCount)
    (hn : ∀ i : Fin 6, (RecursiveCallBank.headerSlot i : Fin commonCount) ≠ j) :
    (commonPrivate hs).head j = 0 ∧ (commonPrivate hs).tape j = blankTape := by
  induction j using Fin.addCases with
  | left j => simp only [commonPrivate,Tapes.append,Fin.addCases_left,SharedBank.empty]; exact ⟨trivial,trivial⟩
  | right j =>
    induction j using Fin.addCases with
    | right j => simp only [commonPrivate,Tapes.append,Fin.addCases_right,SharedBank.empty]; exact ⟨trivial,trivial⟩
    | left j =>
      change Fin (1+6) at j
      induction j using Fin.addCases with
      | left j => simp only [commonPrivate,Tapes.append,Fin.addCases_right,Fin.addCases_left,SharedBank.empty]; exact ⟨trivial,trivial⟩
      | right j => exact False.elim (hn j rfl)

theorem root_blank (hs : Fin 6 → List Bool) (j : Fin rootCount)
    (hn : ∀ i : Fin 6, headerSlot i ≠ j) :
    (rootPrivate hs).head j = 0 ∧ (rootPrivate hs).tape j = blankTape := by
  rw [rootPrivate_eq]
  by_cases hj : j.val < commonCount
  · have hn' : ∀ i : Fin 6, (RecursiveCallBank.headerSlot i : Fin commonCount) ≠ ⟨j.val,hj⟩ := by
      intro i he
      apply hn i
      apply Fin.ext
      have hv := congrArg Fin.val he
      change payloadCount+(1+i.val) = j.val at hv ⊢
      exact hv
    have h := common_blank hs ⟨j.val,hj⟩ hn'
    simpa only [SharedBankStageInput.raw,dite_eq_left hj] using h
  · simp only [SharedBankStageInput.raw,hj,dite_false]
    exact ⟨trivial,trivial⟩

theorem root_sparse (hs : Fin 6 → List Bool) :
    rootPrivate hs = FixedHeaderSparseBankCopy.headerBank headerSlot hs :=
  FixedHeaderSparseBankCopy.headerBank_eq headerSlot header_injective hs (rootPrivate hs)
    (root_target hs) (root_blank hs)

end
end IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersCore
