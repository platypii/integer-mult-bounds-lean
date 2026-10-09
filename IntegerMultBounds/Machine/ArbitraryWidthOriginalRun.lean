import IntegerMultBounds.Machine.ArbitraryWidthHighCommonDispatchCost

/-! Sole-original-header positive-width execution: physically prepare common
metadata, choose and run the actual branch, then erase every private bank. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthOriginalRun
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open ArbitraryWidthHighRun (paddingCount)
variable {t : ℕ}

def input (caller : Tapes t prime) :=
  (ArbitraryWidthHighPreparedRun.input (ArbitraryWidthHighCommonPrepare.input caller)).append
    (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount)

def extendBanks {states : ℕ} (M : Program ((t+16)+19) states prime) :=
  extend (extend (extend (extend (extend (extend (extend M 17) 12) 1)
    exchangeCount) movementCount) paddingCount) ArbitraryWidthElementary.tapeCount

def program (headers : Fin 6 → Fin t) (source : Fin t) :=
  seq (seq (extendBanks (ArbitraryWidthHighCommonPrepare.program headers prime))
    (ArbitraryWidthHighCommonDispatch.program source))
    (extendBanks (ArbitraryWidthHighCommonPrepare.cleanup headers))

def cost (d : Descriptor) (hs : Fin 6 → List Bool) :=
  ArbitraryWidthHighCommonPrepare.setupCost prime d+1+
    ArbitraryWidthHighCommonDispatch.cost d hs+1+ArbitraryWidthHighCommonPrepare.cleanupCost prime d

private theorem extend_banks_hoare {states budget : ℕ} {M : Program ((t+16)+19) states prime}
    {v w : Tapes ((t+16)+19) prime}
    (h : HoareTime M (fun z => z = v) (fun z => z = w) budget) :
    HoareTime (extendBanks M)
      (fun z => z = (ArbitraryWidthHighPreparedRun.input v).append
        (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount))
      (fun z => z = (ArbitraryWidthHighPreparedRun.input w).append
        (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount)) budget :=
  hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (hoare_extend_eq (hoare_extend_eq h (FixedHeaderBankCopy.empty 17)) (FixedHeaderBankCopy.empty 12))
    ArbitraryWidthZeroHeaderShared.empty) (SharedBank.empty exchangeCount prime))
    (SharedBank.empty movementCount prime)) (SharedBank.empty paddingCount prime))
    (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount)

theorem runs (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive) (he : 0 < d.width)
    (hv : RecursiveDimensionBank.Headers d hs)
    (ht : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (headers i) = 1)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) :
    HoareTime (program headers source) (fun z => z = input caller)
      (fun z => z = input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) (cost d hs) := by
  have hs' := extend_banks_hoare (ArbitraryWidthHighCommonPrepare.constructs headers caller prime d hs
    Shared50ModularControl.prime_prime.two_le hp he hv ht hh)
  have hb := ArbitraryWidthHighCommonDispatch.runs caller source d hs hp hv x hf hhead
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
  exact ((hs'.seq hb).seq hc).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; rfl)

def coefficient (cutoff : ℕ) : ℝ := ArbitraryWidthHighCommonDispatchCost.coefficient cutoff+
  ((ArbitraryWidthHighCommonPrepare.setupCoefficient prime cutoff+
    ArbitraryWidthHighCommonPrepare.cleanupCoefficient prime cutoff+2 : ℕ) : ℝ)

theorem coefficient_positive (cutoff : ℕ) : 0 < coefficient cutoff := by
  have h := ArbitraryWidthHighCommonDispatchCost.coefficient_positive cutoff
  unfold coefficient
  positivity

theorem cost_bound (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ ArbitraryWidthHighPrepare.highDepth prime n ∧
      ArbitraryWidthHighPrepare.highDepth prime n < n)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs) (he : 0 < d.width) :
    (cost d hs : ℝ) ≤ coefficient cutoff*(volume prime d : ℝ)*(d.width : ℝ)^Parameters.tau := by
  have hb := ArbitraryWidthHighCommonDispatchCost.bound cutoff hcut d hs hp hv he
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le d hp
  have hs := ArbitraryWidthHighCommonPrepare.setup_budget prime cutoff d
    Shared50ModularControl.prime_prime.two_le hp (fun n hn => (hcut n hn).2.le)
  have hc := ArbitraryWidthHighCommonPrepare.cleanup_budget prime cutoff d
    Shared50ModularControl.prime_prime.two_le hp (fun n hn => (hcut n hn).2.le)
  have ho : ArbitraryWidthHighCommonPrepare.setupCost prime d+
      ArbitraryWidthHighCommonPrepare.cleanupCost prime d+2 ≤
      (ArbitraryWidthHighCommonPrepare.setupCoefficient prime cutoff+
        ArbitraryWidthHighCommonPrepare.cleanupCoefficient prime cutoff+2)*volume prime d := by
    calc
      _ ≤ ArbitraryWidthHighCommonPrepare.setupCoefficient prime cutoff*volume prime d+
          ArbitraryWidthHighCommonPrepare.cleanupCoefficient prime cutoff*volume prime d+2*volume prime d :=
        Nat.add_le_add (Nat.add_le_add hs hc) (by omega)
      _ = _ := by simp only [Nat.add_mul]
  have hor : (ArbitraryWidthHighCommonPrepare.setupCost prime d : ℝ)+
      (ArbitraryWidthHighCommonPrepare.cleanupCost prime d : ℝ)+2 ≤
      ((ArbitraryWidthHighCommonPrepare.setupCoefficient prime cutoff+
        ArbitraryWidthHighCommonPrepare.cleanupCoefficient prime cutoff+2 : ℕ) : ℝ)*(volume prime d : ℝ) := by
    exact_mod_cast ho
  have hpower : 1 ≤ (d.width : ℝ)^Parameters.tau := Real.one_le_rpow (by exact_mod_cast he)
    Shared50RecursiveBudgetBound.exponent_range.1.le
  have hlin := mul_le_mul_of_nonneg_left hpower
    (show 0 ≤ ((ArbitraryWidthHighCommonPrepare.setupCoefficient prime cutoff+
      ArbitraryWidthHighCommonPrepare.cleanupCoefficient prime cutoff+2 : ℕ) : ℝ)*(volume prime d : ℝ) by exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  unfold cost coefficient
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hor hlin ⊢
  nlinarith only [hb,hor,hlin]

theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (d : Descriptor) (hs : Fin 6 → List Bool),
    d.Positive → RecursiveDimensionBank.Headers d hs → 0 < d.width →
    (cost d hs : ℝ) ≤ C*(volume prime d : ℝ)*(d.width : ℝ)^Parameters.tau := by
  obtain ⟨cutoff,hcut⟩ := ArbitraryWidthHighGuard.bounded_fallback prime Shared50ModularControl.prime_prime.two_le
  exact ⟨coefficient cutoff,coefficient_positive cutoff,fun d hs hp hv he => cost_bound cutoff hcut d hs hp hv he⟩

end
end IntegerMultBounds.Machine.ArbitraryWidthOriginalRun
