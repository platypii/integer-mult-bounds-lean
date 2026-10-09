import IntegerMultBounds.Machine.ArbitraryWidthHighExecutionInitialize

/-! Reverse physical erasure of all three high-execution private header banks. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighExecutionInitializeCleanup
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open ArbitraryWidthHighRun (paddingCount)
open ArbitraryWidthExecutionPrivateHeadersRoot
open ArbitraryWidthExecutionPrivateHeadersPadding
open ArbitraryWidthExecutionPrivateHeadersMovement
open ArbitraryWidthHighExecutionInitialize
variable {t : ℕ}

def exchangeCleanup := FixedHeaderSparseBankCopy.cleanup (a := prime) (by omega : 0 < t+7)
  exchangeSlots exchange_injective exchange_room

def movementCleanup := FixedHeaderSparseBankCopy.cleanup (a := prime) (by omega : 0 < (t+exchangeCount)+5)
  (movementSlots (q := prime)) movement_injective movement_room

def paddingCleanup := FixedHeaderSparseBankCopy.cleanup (a := prime)
  (by omega : 0 < ((t+exchangeCount)+movementCount)+10) paddedSlots padded_injective padding_room

def program := seq (seq (paddingCleanup (t := t)) (extend movementCleanup paddingCount))
  (extend (extend exchangeCleanup movementCount) paddingCount)

/-- Erase padding headers first, then movement headers including its retained
clock marker, then exchange headers. This accepts the post-execution caller
bank unchanged, and restores every private tape/head to genuinely blank/zero. -/
theorem cleans (caller : Tapes t prime) (hs : Fin 6 → List Bool) (rs ss op oe : List Bool)
    (ph : Fin 4 → List Bool) (rh : Fin 6 → List Bool) (V : ℕ) (hV : 0 < V)
    (be : Bounded (exchangeWords hs rs) V) (bm : Bounded (movementWords ss op oe rs) V)
    (bp : Bounded (paddedWords ph rh) V) :
    HoareTime (program (t := t))
      (fun w => w = output caller hs rs ss op oe ph rh)
      (fun w => w = ArbitraryWidthHighExecutionInitialize.input caller) (200*V) := by
  have h1 := FixedHeaderSparseBankCopy.cleans_linear (by omega : 0 < ((t+exchangeCount)+movementCount)+10)
    paddedSlots padded_injective padding_room
    ((caller.append (exchangePrivate hs rs)).append (movementPrivate ss op oe rs))
    (paddedWords ph rh) V hV bp.canonical bp.value
  rw [← padded_sparse] at h1
  have h2 := FixedHeaderSparseBankCopy.cleans_linear (by omega : 0 < (t+exchangeCount)+5)
    (movementSlots (q := prime)) movement_injective movement_room
    (caller.append (exchangePrivate hs rs)) (movementWords ss op oe rs) V hV bm.canonical bm.value
  rw [← movement_sparse] at h2
  have h2' := hoare_extend_eq h2 (SharedBank.empty paddingCount prime)
  have h3 := FixedHeaderSparseBankCopy.cleans_linear (by omega : 0 < t+7)
    exchangeSlots exchange_injective exchange_room caller (exchangeWords hs rs) V hV be.canonical be.value
  rw [← exchange_sparse] at h3
  have h3' := hoare_extend_eq (hoare_extend_eq h3 (SharedBank.empty movementCount prime))
    (SharedBank.empty paddingCount prime)
  exact ((h1.seq h2').seq h3').consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ArbitraryWidthHighExecutionInitializeCleanup
