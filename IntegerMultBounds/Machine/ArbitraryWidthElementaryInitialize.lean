import IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersRoot

/-! The elementary fallback's complete blank private bank is initialized by
copying its six retained source headers, then cleared by the actual eraser. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthElementaryInitialize
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ArbitraryWidthExecutionPrivateHeadersCore (blankTape emptyOne emptyTwo)
open ArbitraryWidthExecutionPrivateHeadersRoot (elementarySlots elementary_injective elementary_sparse)
variable {t : ℕ}

private theorem six_le : 6 ≤ ArbitraryWidthElementary.tapeCount := by
  change 6 ≤ ArbitrarySliceCall.rootCount+16
  omega

def privateBank (hs : Fin 6 → List Bool) :=
  ArbitraryWidthElementaryShared.privateBank hs blankTape 0 emptyOne emptyOne emptyTwo

def program (focus : Fin 6 → Fin t) := FixedHeaderSparseBankCopy.program (a := prime)
  (by omega : 0 < t+6) focus elementarySlots elementary_injective six_le

def cleanup := FixedHeaderSparseBankCopy.cleanup (a := prime)
  (by omega : 0 < t+6) elementarySlots elementary_injective six_le

theorem constructs (focus : Fin 6 → Fin t) (caller : Tapes t prime)
    (hs : Fin 6 → List Bool) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hv : ∀ i, Counter.value (hs i) ≤ V)
    (ht : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (focus i) = 1) :
    HoareTime (program focus)
      (fun w => w = caller.append (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount))
      (fun w => w = caller.append (privateBank hs)) (60*V) := by
  have h := FixedHeaderSparseBankCopy.constructs_linear (a := prime)
    (by omega : 0 < t+6) focus elementarySlots elementary_injective six_le caller hs ht hh V hV hc hv
  simpa only [program,privateBank,elementary_sparse] using h

theorem cleans (caller : Tapes t prime) (hs : Fin 6 → List Bool) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hv : ∀ i, Counter.value (hs i) ≤ V) :
    HoareTime (cleanup (t := t))
      (fun w => w = caller.append (privateBank hs))
      (fun w => w = caller.append (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount))
      (54*V) := by
  have h := FixedHeaderSparseBankCopy.cleans_linear (a := prime)
    (by omega : 0 < t+6) elementarySlots elementary_injective six_le caller hs V hV hc hv
  simpa only [cleanup,privateBank,elementary_sparse] using h

end
end IntegerMultBounds.Machine.ArbitraryWidthElementaryInitialize
