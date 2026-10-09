import IntegerMultBounds.Machine.ArbitraryWidthElementaryInitialize

/-! Actual fallback from blank private work, including all header copies. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthElementaryInitializedRun
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthExecutionPrivateHeadersCore (blankTape emptyOne emptyTwo)
open ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

theorem blank_ready : Shared50RecursiveCallReady.Ready blankTape 0 emptyOne emptyOne emptyTwo := by
  refine ⟨?_,?_,rfl,?_,?_⟩
  all_goals intro z hz; rfl

def program (headers : Fin 6 → Fin t) (source : Fin t) :=
  seq (seq (ArbitraryWidthElementaryInitialize.program headers)
    (ArbitraryWidthElementaryShared.program source))
    (ArbitraryWidthElementaryInitialize.cleanup (t := t))

theorem realizes_hoare (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
    (v : Descriptor) (hs : Fin 6 → List Bool) (hp : v.Positive)
    (hv : RecursiveDimensionBank.Headers v hs)
    (ht : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (headers i) = 1)
    (x : Fin (volume prime v) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) :
    HoareTime (program headers source)
      (fun w => w = caller.append (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount))
      (fun w => w = (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
        (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount))
      (60*volume prime v+ArbitraryWidthElementary.coefficient*(v.width+1)*volume prime v+
        54*volume prime v+2) := by
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hb (i : Fin 6) : Counter.value (hs i) ≤ volume prime v :=
    (hv.1 i).trans_le (RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le v hp i)
  have hi := ArbitraryWidthElementaryInitialize.constructs headers caller hs (volume prime v) hV hv.2 hb ht hh
  have hm := ArbitraryWidthElementaryShared.realizes_hoare caller source v hs hp hv blankTape 0
    emptyOne emptyOne emptyTwo blank_ready x hf hhead
  have he := ArbitraryWidthElementaryInitialize.cleans
    (setTape caller source (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0)
    hs (volume prime v) hV hv.2 hb
  have h := (hi.seq hm).seq he
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem bounded_hoare (cutoff : ℕ) (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
    (v : Descriptor) (hs : Fin 6 → List Bool) (hp : v.Positive)
    (hv : RecursiveDimensionBank.Headers v hs) (hw : v.width ≤ cutoff)
    (ht : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (headers i) = 1)
    (x : Fin (volume prime v) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) :
    HoareTime (program headers source)
      (fun w => w = caller.append (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount))
      (fun w => w = (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
        (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount))
      ((ArbitraryWidthElementary.coefficient*(cutoff+1)+116)*volume prime v) := by
  have h := realizes_hoare caller headers source v hs hp hv ht hh x hf hhead
  apply h.consequence (fun _ h => h) (fun _ h => h)
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hm := Nat.mul_le_mul_right (volume prime v)
    (Nat.mul_le_mul_left ArbitraryWidthElementary.coefficient (Nat.add_le_add_right hw 1))
  nlinarith

theorem bounded_budget (cutoff e V : ℕ) (τ : ℝ) (he : 0 < e) (hτ : 0 < τ) :
    (((ArbitraryWidthElementary.coefficient*(cutoff+1)+116)*V : ℕ) : ℝ) ≤
      ((ArbitraryWidthElementary.coefficient*(cutoff+1)+116 : ℕ) : ℝ)*(V : ℝ)*(e : ℝ)^τ := by
  have hp : 1 ≤ (e : ℝ)^τ := Real.one_le_rpow (by exact_mod_cast he) hτ.le
  have h := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ ((ArbitraryWidthElementary.coefficient*(cutoff+1)+116 : ℕ) : ℝ)*(V : ℝ) by exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  simpa only [Nat.cast_mul,mul_one] using h

end
end IntegerMultBounds.Machine.ArbitraryWidthElementaryInitializedRun
