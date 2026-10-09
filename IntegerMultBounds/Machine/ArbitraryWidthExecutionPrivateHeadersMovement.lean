import IntegerMultBounds.Machine.ArbitraryWidthHighMovementPlacement
import IntegerMultBounds.Machine.FixedHeaderSparseBankCopy

/-! Literal five-header sparse bank for the physical join/separate engine.
Its outer clock is a marked canonical zero, not a blank tape. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersMovement
noncomputable section
variable {q a : ℕ}
open RadixHighBlockJoinBank (count)
open FixedHeaderSparseBankCopy (headerBank)

def movementSlots : Fin 5 → Fin (RadixHighBlockJoinSetup.total q) :=
  ![Fin.castAdd 2 RadixHighBlockJoinBank.spectatorSlot,
    RadixHighBlockJoinSetup.originalPrefixSlot,RadixHighBlockJoinSetup.originalSuffixSlot,
    Fin.natAdd (count q) 0,Fin.natAdd (count q) 1]

def movementWords (ss op oe rs : List Bool) : Fin 5 → List Bool := ![ss,op,oe,[],rs]

theorem movement_injective : Function.Injective (movementSlots (q := q)) := by
  intro i j he
  have hv := congrArg Fin.val he
  fin_cases i <;> fin_cases j
  all_goals simp [movementSlots,RadixHighBlockJoinSetup.originalPrefixSlot,
    RadixHighBlockJoinSetup.originalSuffixSlot,RadixHighBlockJoinBank.spectatorSlot,
    RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
    RadixHighBlockJoinBank.count_eq] at hv
  all_goals rfl

theorem movement_target (ss op oe rs : List Bool) (i : Fin 5) :
    (ArbitraryWidthHighMovementPlacement.privateBank (q := q) (a := a) ss op oe rs).head (movementSlots i) = 1 ∧
    (ArbitraryWidthHighMovementPlacement.privateBank (q := q) (a := a) ss op oe rs).tape (movementSlots i) =
      RadixZeroFill.encodedBinary (movementWords ss op oe rs i) := by
  let b := RadixHighBlockJoinSetup.bank (q := q) (a := a) (fun _ => blank) ss op oe none none none
    (RadixHighBlockJoinInitialize.controls CountedLoopReuseAlphabet.empty 1 rs)
  fin_cases i
  · change b.head (Fin.castAdd 2 RadixHighBlockJoinBank.spectatorSlot) = 1 ∧
      b.tape (Fin.castAdd 2 RadixHighBlockJoinBank.spectatorSlot) = RadixZeroFill.encodedBinary ss
    dsimp only [b]
    rw [RadixHighBlockJoinSetup.read_head,RadixHighBlockJoinSetup.read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.spectatorSlot,RadixHighBlockJoinSetup.optionHead,
      RadixHighBlockJoinSetup.optionTape,RadixHighBlockJoinSetup.encoded_binary]
    split_ifs <;> first | omega | exact ⟨rfl,rfl⟩
  · change b.head (Fin.castAdd 2 RadixHighBlockJoinBank.originalPrefixSlot) = 1 ∧
      b.tape (Fin.castAdd 2 RadixHighBlockJoinBank.originalPrefixSlot) = RadixZeroFill.encodedBinary op
    dsimp only [b]
    rw [RadixHighBlockJoinSetup.read_head,RadixHighBlockJoinSetup.read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinSetup.optionHead,
      RadixHighBlockJoinSetup.optionTape,RadixHighBlockJoinSetup.encoded_binary]
    split_ifs <;> first | omega | exact ⟨rfl,rfl⟩
  · change b.head (Fin.castAdd 2 RadixHighBlockJoinBank.originalSuffixSlot) = 1 ∧
      b.tape (Fin.castAdd 2 RadixHighBlockJoinBank.originalSuffixSlot) = RadixZeroFill.encodedBinary oe
    dsimp only [b]
    rw [RadixHighBlockJoinSetup.read_head,RadixHighBlockJoinSetup.read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.originalSuffixSlot,RadixHighBlockJoinSetup.optionHead,
      RadixHighBlockJoinSetup.optionTape,RadixHighBlockJoinSetup.encoded_binary]
    split_ifs <;> first | omega | exact ⟨rfl,rfl⟩
  · change b.head (Fin.natAdd (count q) 0) = 1 ∧
      b.tape (Fin.natAdd (count q) 0) = RadixZeroFill.encodedBinary []
    simp only [b,RadixHighBlockJoinSetup.bank,Tapes.append,Fin.addCases_right]
    exact ⟨rfl,(RadixHighBlockJoinSetup.encoded_binary []).symm⟩
  · change b.head (Fin.natAdd (count q) 1) = 1 ∧
      b.tape (Fin.natAdd (count q) 1) = RadixZeroFill.encodedBinary rs
    simp only [b,RadixHighBlockJoinSetup.bank,Tapes.append,Fin.addCases_right]
    exact ⟨rfl,(RadixHighBlockJoinSetup.encoded_binary rs).symm⟩

theorem movement_blank (ss op oe rs : List Bool) (j : Fin (RadixHighBlockJoinSetup.total q))
    (hn : ∀ i : Fin 5, movementSlots i ≠ j) :
    (ArbitraryWidthHighMovementPlacement.privateBank (q := q) (a := a) ss op oe rs).head j = 0 ∧
    (ArbitraryWidthHighMovementPlacement.privateBank (q := q) (a := a) ss op oe rs).tape j = fun _ => blank := by
  induction j using Fin.addCases with
  | left j =>
    have h0 : j.val ≠ 2*q+14 := by intro he; apply hn 0; exact Fin.ext he.symm
    have h1 : j.val ≠ 2*q+32 := by intro he; apply hn 1; exact Fin.ext he.symm
    have h2 : j.val ≠ 2*q+33 := by intro he; apply hn 2; exact Fin.ext he.symm
    unfold ArbitraryWidthHighMovementPlacement.privateBank ArbitraryWidthHighMovementPlacement.bank
      RadixHighBlockJoinInitialize.input
    rw [RadixHighBlockJoinSetup.read_head,RadixHighBlockJoinSetup.read_tape]
    simp only [h0,h1,h2,or_self,ite_false,RadixHighBlockJoinSetup.optionHead,RadixHighBlockJoinSetup.optionTape]
    constructor <;> split_ifs <;> rfl
  | right j =>
    fin_cases j
    · exact False.elim (hn 3 rfl)
    · exact False.elim (hn 4 rfl)

/-- All five marked headers must be initialized and erased physically.
Index3 is canonical zero for the retained outer clock: its separator and
head-one position are explicitly included in this exact sparse bank. -/
theorem movement_sparse (ss op oe rs : List Bool) :
    ArbitraryWidthHighMovementPlacement.privateBank (q := q) (a := a) ss op oe rs =
      headerBank movementSlots (movementWords ss op oe rs) :=
  FixedHeaderSparseBankCopy.headerBank_eq movementSlots movement_injective _ _
    (movement_target ss op oe rs) (movement_blank ss op oe rs)

end
end IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersMovement
