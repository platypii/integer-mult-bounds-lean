module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalRun
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighCommonDispatchWithin

/-! Sole-original-header positive-width execution: physically prepare common
metadata, choose and run the actual branch, then erase every private bank. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalRunWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighRun (paddingCount)
variable {t : ℕ}

open ArbitraryWidthOriginalRun (input program cost extend_banks_hoare)

def coefficient (cutoff : ℕ) : ℕ := max
  (ArbitraryWidthHighCommonPrepare.setupCoefficient prime cutoff+ArbitraryWidthHighCommonDispatchWithin.coefficient cutoff)
  (2*ArbitraryWidthHighCommonPrepare.cleanupCoefficient prime cutoff)

/-- Empty private banks preserve arbitrary caller head equality structurally. -/
theorem input_head_congr {v w : Tapes t prime} (h : v.head = w.head) :
    (input v).head = (input w).head := by
  have hcommon := Tapes.append_head_congr _ _ ArbitraryWidthHighPrepareShared.privateInput
    ArbitraryWidthHighPrepareShared.privateInput
    (Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 16) (FixedHeaderBankCopy.empty 16) h rfl) rfl
  have hbranch := Tapes.append_head_congr _ _ ArbitraryWidthZeroHeaderShared.empty
    ArbitraryWidthZeroHeaderShared.empty
    (Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 12) (FixedHeaderBankCopy.empty 12)
      (Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty 17) (FixedHeaderBankCopy.empty 17) hcommon rfl) rfl) rfl
  have hexecution := Tapes.append_head_congr _ _ (SharedBank.empty paddingCount prime)
    (SharedBank.empty paddingCount prime)
    (Tapes.append_head_congr _ _ (SharedBank.empty movementCount prime) (SharedBank.empty movementCount prime)
      (Tapes.append_head_congr _ _ (SharedBank.empty exchangeCount prime) (SharedBank.empty exchangeCount prime)
        hbranch rfl) rfl) rfl
  exact Tapes.append_head_congr _ _ (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount)
    (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount) hexecution rfl


theorem runs_within (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ ArbitraryWidthHighPrepare.highDepth prime n ∧
      ArbitraryWidthHighPrepare.highDepth prime n < n) (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive) (he : 0 < d.width)
    (hv : RecursiveDimensionBank.Headers d hs)
    (ht : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (headers i) = 1)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient cutoff*volume prime d : ℕ) ≤ (input caller).head j ∧
      (input caller).head j+(coefficient cutoff*volume prime d : ℕ) ≤ hi) :
    HoareWithin (program headers source) (fun z => z = input caller)
      (fun z => z = input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) (cost d hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hs' := extend_banks_hoare (ArbitraryWidthHighCommonPrepare.constructs headers caller prime d hs
    Shared50ModularControl.prime_prime.two_le hp he hv ht hh)
  have hsBound := ArbitraryWidthHighCommonPrepare.setup_budget prime cutoff d
    Shared50ModularControl.prime_prime.two_le hp (fun n hn => (hcut n hn).2.le)
  have hcBound := ArbitraryWidthHighCommonPrepare.cleanup_budget prime cutoff d
    Shared50ModularControl.prime_prime.two_le hp (fun n hn => (hcut n hn).2.le)
  have hreserve := Nat.mul_le_mul_right (volume prime d)
    (show ArbitraryWidthHighCommonPrepare.setupCoefficient prime cutoff+
      ArbitraryWidthHighCommonDispatchWithin.coefficient cutoff ≤ coefficient cutoff from le_max_left _ _)
  rw [Nat.add_mul] at hreserve
  have hcleanup := Nat.mul_le_mul_right (volume prime d)
    (show 2*ArbitraryWidthHighCommonPrepare.cleanupCoefficient prime cutoff ≤ coefficient cutoff from le_max_right _ _)
  rw [Nat.mul_assoc] at hcleanup
  have hws := HoareWithin.of_time_heads hs' lo hi (by
    rintro w rfl j
    have hm := hmargin j
    change lo+_ ≤ (input caller).head j ∧ (input caller).head j+_ ≤ hi
    omega)
  have hprepared : ∀ j, lo+(ArbitraryWidthHighCommonDispatchWithin.coefficient cutoff*volume prime d : ℕ) ≤
      (ArbitraryWidthHighCommonDispatch.bank caller d hs).head j ∧
      (ArbitraryWidthHighCommonDispatch.bank caller d hs).head j+
        (ArbitraryWidthHighCommonDispatchWithin.coefficient cutoff*volume prime d : ℕ) ≤ hi := by
    intro j
    have ht := hs'.head_change j
    change (input caller).head j-(ArbitraryWidthHighCommonPrepare.setupCost prime d : ℕ) ≤
      (ArbitraryWidthHighCommonDispatch.bank caller d hs).head j ∧
      (ArbitraryWidthHighCommonDispatch.bank caller d hs).head j ≤
        (input caller).head j+(ArbitraryWidthHighCommonPrepare.setupCost prime d : ℕ) at ht
    have hm := hmargin j
    omega
  have hb := ArbitraryWidthHighCommonDispatchWithin.runs_within cutoff hcut caller source d hs hp hv x hf hhead lo hi hprepared
  have hn : headers 3 ≠ source := by
    intro h
    have hh3 := hh 3
    rw [h,hhead] at hh3
    omega
  let changed := setTape caller source (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0
  have hc := extend_banks_hoare (ArbitraryWidthHighCommonPrepare.cleans headers changed prime d hs
    Shared50ModularControl.prime_prime.two_le hp hv
    (by simpa only [changed,setTape,Function.update_of_ne hn] using ht 3)
    (by simpa only [changed,setTape,Function.update_of_ne hn] using hh 3))
  have hcallerHeads : changed.head = caller.head := by
    funext j
    by_cases hj : j = source
    · subst j; simp only [changed,setTape,Function.update_self,hhead]
    · simp only [changed,setTape,Function.update_of_ne hj]
  have hheads := input_head_congr hcallerHeads
  have hwc := HoareWithin.of_time_post_heads hc lo hi (by
    rintro w rfl j
    change lo+_ ≤ (input changed).head j ∧ (input changed).head j+_ ≤ hi
    rw [hheads]
    have hm := hmargin j
    omega)
  exact ((hws.seq hb).seq hwc).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; rfl) (fun _ h => h)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalRunWithin
