import IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersCore
import IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersAppend

/-! Sparse initialized header banks for high exchange and elementary fallback. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersRoot
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ArbitrarySliceCall (rootCount headerSlot)
open ArbitraryWidthExecutionPrivateHeadersCore
open ArbitraryWidthExecutionPrivateHeadersAppend
open FixedHeaderSparseBankCopy (headerBank)

def rhoSlot : Fin 1 → Fin 16 := fun _ => 14

theorem rho_injective : Function.Injective rhoSlot := fun i j _ => Subsingleton.elim i j

theorem exchange_tail (rs : List Bool) :
    ArbitraryWidthHighExchangeControls.input (a := prime) rs = headerBank rhoSlot (fun _ => rs) := by
  apply FixedHeaderSparseBankCopy.headerBank_eq _ rho_injective
  · intro i
    constructor
    · rfl
    · exact BinaryDescriptorStackRoundtrip.descriptor_encoded rs
  · intro j hj
    have hn : j ≠ 14 := fun he => hj 0 he.symm
    fin_cases j <;> first | exact False.elim (hn rfl) | exact ⟨rfl,rfl⟩

def exchangeSlots : Fin (6+1) → Fin ArbitraryWidthHighExchange.tapeCount := slots headerSlot rhoSlot
def exchangeWords (hs : Fin 6 → List Bool) (rs : List Bool) : Fin (6+1) → List Bool :=
  Fin.addCases hs (fun _ => rs)

theorem exchange_injective : Function.Injective exchangeSlots :=
  slots_injective headerSlot rhoSlot header_injective rho_injective

/-- Exactly the six original root descriptors and retained rho are marked;
all remaining heads/cells are genuinely blank-ready. -/
theorem exchange_sparse (hs : Fin 6 → List Bool) (rs : List Bool) :
    ArbitraryWidthHighExchangeShared.privateBank hs rs blankTape 0 emptyOne emptyOne emptyTwo =
      headerBank exchangeSlots (exchangeWords hs rs) := by
  change (rootPrivate hs).append (ArbitraryWidthHighExchangeControls.input rs) = _
  rw [root_sparse,exchange_tail]
  exact append headerSlot rhoSlot header_injective rho_injective hs (fun _ => rs)

def elementarySlots : Fin 6 → Fin ArbitraryWidthElementary.tapeCount := leftSlots headerSlot

theorem elementary_injective : Function.Injective elementarySlots := left_injective headerSlot header_injective

/-- The bounded fallback has only the original six headers; its future
count slot starts blank rather than with a free initialized zero marker. -/
theorem elementary_sparse (hs : Fin 6 → List Bool) :
    ArbitraryWidthElementaryShared.privateBank hs blankTape 0 emptyOne emptyOne emptyTwo =
      headerBank elementarySlots hs := by
  change (rootPrivate hs).append (SharedBank.empty 16 prime) = _
  rw [root_sparse]
  exact append_empty headerSlot header_injective hs

end
end IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersRoot
