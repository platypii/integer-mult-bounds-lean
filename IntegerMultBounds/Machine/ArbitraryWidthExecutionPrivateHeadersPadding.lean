import IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersCore
import IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersAppend
import IntegerMultBounds.Machine.RadixHighBlockJoinSetup

/-! The physical pad/dispatch/crop private bank is exactly ten sparse headers. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersPadding
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ArbitrarySliceCall (rootCount headerSlot)
open ArbitraryWidthConsumePlacement (T)
open ArbitraryWidthExecutionPrivateHeadersCore
open ArbitraryWidthExecutionPrivateHeadersAppend
open FixedHeaderSparseBankCopy (headerBank)

private theorem empty_append {l r a : ℕ} :
    (SharedBank.empty l a).append (SharedBank.empty r a) = SharedBank.empty (l+r) a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
    simp [SharedBank.empty]

def pieceSlots : Fin 6 → Fin T := rightSlots (leftSlots (leftSlots (r := 12) headerSlot))

theorem piece_injective : Function.Injective pieceSlots :=
  right_injective _ (left_injective _ (left_injective headerSlot header_injective))

theorem piece_sparse (hs : Fin 6 → List Bool) :
    ArbitraryWidthPaddedPiecePlacement.privateBank hs blankTape 0 emptyOne emptyOne emptyTwo emptyOne =
      headerBank pieceSlots hs := by
  change (SharedBank.empty 14 prime).append
    (((rootPrivate hs).append ((SharedBank.empty 11 prime).append emptyOne)).append
      (SharedBank.empty 6 prime)) = _
  rw [empty_append,root_sparse,append_empty headerSlot header_injective,
    append_empty _ (left_injective headerSlot header_injective)]
  exact ArbitraryWidthExecutionPrivateHeadersAppend.empty_append _
    (left_injective _ (left_injective headerSlot header_injective)) hs

def rowSlots (i : Fin 4) : Fin 12 := ⟨i.val+2,by omega⟩

theorem row_injective : Function.Injective rowSlots := by
  intro i j he
  have hv := congrArg Fin.val he
  exact Fin.ext (by dsimp only [rowSlots] at hv; omega)

theorem row_sparse (hs : Fin 4 → List Bool) :
    ArbitraryWidthPaddedPiecePadding.bank blankTape blankTape hs = headerBank rowSlots hs := by
  apply FixedHeaderSparseBankCopy.headerBank_eq _ row_injective
  · intro i
    fin_cases i
    all_goals constructor
    all_goals first | rfl | exact (RadixHighBlockJoinSetup.encoded_binary _).symm
  · intro j hj
    have h0 := hj 0
    have h1 := hj 1
    have h2 := hj 2
    have h3 := hj 3
    fin_cases j <;> first | exact False.elim (h0 rfl) | exact False.elim (h1 rfl) |
      exact False.elim (h2 rfl) | exact False.elim (h3 rfl) | exact ⟨rfl,rfl⟩

def paddedSlots : Fin (4+6) → Fin ArbitraryWidthPaddedPieceRun.tapeCount := slots rowSlots pieceSlots
def paddedWords (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool) :
    Fin (4+6) → List Bool := Fin.addCases paddingHeaders rootHeaders

theorem padded_injective : Function.Injective paddedSlots :=
  slots_injective rowSlots pieceSlots row_injective piece_injective

/-- Four row descriptors and six low-root descriptors are the complete set
of marked input tapes; source, padded payload, controls and stacks are blank. -/
theorem padded_sparse (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool) :
    ArbitraryWidthPaddedPieceShared.privateBank paddingHeaders rootHeaders blankTape 0
      emptyOne emptyOne emptyTwo emptyOne = headerBank paddedSlots (paddedWords paddingHeaders rootHeaders) := by
  change (ArbitraryWidthPaddedPiecePadding.bank blankTape blankTape paddingHeaders).append
    (ArbitraryWidthPaddedPiecePlacement.privateBank rootHeaders blankTape 0 emptyOne emptyOne emptyTwo emptyOne) = _
  rw [row_sparse,piece_sparse]
  exact append rowSlots pieceSlots row_injective piece_injective paddingHeaders rootHeaders

end
end IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersPadding
