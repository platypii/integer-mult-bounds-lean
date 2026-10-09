import IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersRoot
import IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersPadding
import IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersMovement
import IntegerMultBounds.Machine.ArbitraryWidthHighRun

/-! Physical installation of all high-branch private execution headers from
retained caller tapes, including the movement engine's canonical-zero clock. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighExecutionInitialize
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open ArbitraryWidthHighRun (paddingCount)
open ArbitraryWidthExecutionPrivateHeadersCore
open ArbitraryWidthExecutionPrivateHeadersRoot
open ArbitraryWidthExecutionPrivateHeadersPadding
open ArbitraryWidthExecutionPrivateHeadersMovement
variable {t n : ℕ}

/-- Source slots need not be distinct: one retained word may initialize
several different private headers. -/
structure Sources (caller : Tapes t prime) (focus : Fin n → Fin t) (words : Fin n → List Bool) : Prop where
  tape : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (words i)
  head : ∀ i, caller.head (focus i) = 1

structure Bounded (words : Fin n → List Bool) (V : ℕ) : Prop where
  canonical : ∀ i, GrowingCounterData.Canonical (words i)
  value : ∀ i, Counter.value (words i) ≤ V

theorem exchange_room : 7 ≤ exchangeCount := by
  have h := Fintype.card_le_of_injective exchangeSlots exchange_injective
  simpa only [Fintype.card_fin] using h

theorem movement_room : 5 ≤ movementCount := by
  have h := Fintype.card_le_of_injective (movementSlots (q := prime)) movement_injective
  simpa only [Fintype.card_fin] using h

theorem padding_room : 10 ≤ paddingCount := by
  have h := Fintype.card_le_of_injective paddedSlots padded_injective
  simpa only [Fintype.card_fin] using h

def exchangePrivate (hs : Fin 6 → List Bool) (rs : List Bool) :=
  ArbitraryWidthHighExchangeShared.privateBank hs rs blankTape 0 emptyOne emptyOne emptyTwo

def movementPrivate (ss op oe rs : List Bool) :=
  ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs

def paddingPrivate (ph : Fin 4 → List Bool) (rh : Fin 6 → List Bool) :=
  ArbitraryWidthPaddedPieceShared.privateBank ph rh blankTape 0 emptyOne emptyOne emptyTwo emptyOne

def input (caller : Tapes t prime) :=
  ((caller.append (SharedBank.empty exchangeCount prime)).append
    (SharedBank.empty movementCount prime)).append (SharedBank.empty paddingCount prime)

def output (caller : Tapes t prime) (hs : Fin 6 → List Bool) (rs ss op oe : List Bool)
    (ph : Fin 4 → List Bool) (rh : Fin 6 → List Bool) :=
  ((caller.append (exchangePrivate hs rs)).append (movementPrivate ss op oe rs)).append
    (paddingPrivate ph rh)

def exchangeCopy (focus : Fin 7 → Fin t) :=
  FixedHeaderSparseBankCopy.program (a := prime) (by omega : 0 < t+7) focus
    exchangeSlots exchange_injective exchange_room

def movementFocus (focus : Fin 5 → Fin t) : Fin 5 → Fin (t+exchangeCount) :=
  fun i => Fin.castAdd exchangeCount (focus i)
def movementCopy (focus : Fin 5 → Fin t) :=
  FixedHeaderSparseBankCopy.program (a := prime) (by omega : 0 < (t+exchangeCount)+5)
    (movementFocus focus) (movementSlots (q := prime)) movement_injective movement_room

def paddingFocus (focus : Fin 10 → Fin t) : Fin 10 → Fin ((t+exchangeCount)+movementCount) :=
  fun i => Fin.castAdd movementCount (Fin.castAdd exchangeCount (focus i))
def paddingCopy (focus : Fin 10 → Fin t) :=
  FixedHeaderSparseBankCopy.program (a := prime) (by omega : 0 < ((t+exchangeCount)+movementCount)+10)
    (paddingFocus focus) paddedSlots padded_injective padding_room

def program (exchange : Fin 7 → Fin t) (movement : Fin 5 → Fin t) (padding : Fin 10 → Fin t) :=
  seq (seq (extend (extend (exchangeCopy exchange) movementCount) paddingCount)
    (extend (movementCopy movement) paddingCount)) (paddingCopy padding)

/-- Three actual fixed-family copy machines preserve every caller tape/head.
All private banks start wholly blank; all 22 marked words are physically
copied, including the empty word's separator for the movement clock. -/
theorem constructs (caller : Tapes t prime)
    (exchange : Fin 7 → Fin t) (movement : Fin 5 → Fin t) (padding : Fin 10 → Fin t)
    (hs : Fin 6 → List Bool) (rs ss op oe : List Bool)
    (ph : Fin 4 → List Bool) (rh : Fin 6 → List Bool) (V : ℕ) (hV : 0 < V)
    (he : Sources caller exchange (exchangeWords hs rs))
    (hm : Sources caller movement (movementWords ss op oe rs))
    (hp : Sources caller padding (paddedWords ph rh))
    (be : Bounded (exchangeWords hs rs) V) (bm : Bounded (movementWords ss op oe rs) V)
    (bp : Bounded (paddedWords ph rh) V) :
    HoareTime (program exchange movement padding)
      (fun w => w = input caller) (fun w => w = output caller hs rs ss op oe ph rh) (222*V) := by
  have h1 := FixedHeaderSparseBankCopy.constructs_linear (by omega : 0 < t+7) exchange
    exchangeSlots exchange_injective exchange_room caller (exchangeWords hs rs)
    he.tape he.head V hV be.canonical be.value
  rw [← exchange_sparse] at h1
  have h1' := hoare_extend_eq (hoare_extend_eq h1 (SharedBank.empty movementCount prime))
    (SharedBank.empty paddingCount prime)
  have h2 := FixedHeaderSparseBankCopy.constructs_linear (by omega : 0 < (t+exchangeCount)+5)
    (movementFocus movement) (movementSlots (q := prime)) movement_injective movement_room
    (caller.append (exchangePrivate hs rs)) (movementWords ss op oe rs)
    (by intro i; simpa only [movementFocus,Tapes.append,Fin.addCases_left] using hm.tape i)
    (by intro i; simpa only [movementFocus,Tapes.append,Fin.addCases_left] using hm.head i)
    V hV bm.canonical bm.value
  rw [← movement_sparse] at h2
  have h2' := hoare_extend_eq h2 (SharedBank.empty paddingCount prime)
  have h3 := FixedHeaderSparseBankCopy.constructs_linear (by omega : 0 < ((t+exchangeCount)+movementCount)+10)
    (paddingFocus padding) paddedSlots padded_injective padding_room
    ((caller.append (exchangePrivate hs rs)).append (movementPrivate ss op oe rs)) (paddedWords ph rh)
    (by intro i; simpa only [paddingFocus,Tapes.append,Fin.addCases_left] using hp.tape i)
    (by intro i; simpa only [paddingFocus,Tapes.append,Fin.addCases_left] using hp.head i)
    V hV bp.canonical bp.value
  rw [← padded_sparse] at h3
  exact ((h1'.seq h2').seq h3).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ArbitraryWidthHighExecutionInitialize
