module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalTotalRun
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalRunWithin
public import IntegerMultBounds.Machine.HoareWithinBranch

/-! One fixed original-descriptor machine covers zero and positive widths.
The actual canonical-width read selects the concrete proved branch; all
private metadata and execution banks start and finish blank. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalTotalRunWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

open ArbitraryWidthOriginalTotalRun (input program cost zeroCoefficient)

def coefficient (cutoff : ℕ) : ℕ := max (ArbitraryWidthOriginalRunWithin.coefficient cutoff) zeroCoefficient

theorem runs_within (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ ArbitraryWidthHighPrepare.highDepth prime n ∧
      ArbitraryWidthHighPrepare.highDepth prime n < n) (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs)
    (ht : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (headers i) = 1)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient cutoff*volume prime d : ℕ) ≤ (input caller).head j ∧
      (input caller).head j+(coefficient cutoff*volume prime d : ℕ) ≤ hi) :
    HoareWithin (program headers source) (fun w => w = input caller)
      (fun w => w = input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) (cost d hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hz : ArbitraryWidthOriginalZeroBranch.test headers (input caller).reads = true ↔ d.width = 0 := by
    rw [ArbitraryWidthOriginalZeroBranch.test_true_iff caller headers (hs 3) (hv.2 3) (ht 3) (hh 3),hv.1 3]
    rfl
  have hpositiveReserve := Nat.mul_le_mul_right (volume prime d)
    (show ArbitraryWidthOriginalRunWithin.coefficient cutoff ≤ coefficient cutoff from le_max_left _ _)
  have hzeroReserve := Nat.mul_le_mul_right (volume prime d)
    (show zeroCoefficient ≤ coefficient cutoff from le_max_right _ _)
  by_cases hw : d.width = 0
  · have hzero := ArbitraryWidthOriginalZeroBranch.zero_hoare caller headers source d hs hp hw hv ht hh x hf hhead
    have hzeroWithin := HoareWithin.of_time_heads hzero lo hi (by
      rintro w rfl j
      have hm := hmargin j
      change lo+(zeroCoefficient*volume prime d : ℕ) ≤ (input caller).head j ∧
        (input caller).head j+(zeroCoefficient*volume prime d : ℕ) ≤ hi
      omega)
    have hyes : HoareWithin (ArbitraryWidthOriginalZeroBranch.zeroProgram headers source)
        (fun w => w = input caller ∧ ArbitraryWidthOriginalZeroBranch.test headers w.reads = true)
        (fun w => w = input (setTape caller source
          (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0))
        (zeroCoefficient*volume prime d) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) :=
      hzeroWithin.consequence (fun _ h => h.1) (fun _ h => h) le_rfl (fun _ h => h)
    have hno : HoareWithin (ArbitraryWidthOriginalRun.program headers source)
        (fun w => w = input caller ∧ ArbitraryWidthOriginalZeroBranch.test headers w.reads = false)
        (fun w => w = input (setTape caller source
          (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) 0 (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
      rintro w ⟨rfl,h⟩
      have htrue := hz.mpr hw
      rw [h] at htrue
      exact Bool.noConfusion htrue
    have h := HoareWithin.branch (ArbitraryWidthOriginalZeroBranch.test headers) hyes hno
    simpa only [program,ArbitraryWidthOriginalZeroBranch.program,cost,hw,ite_true,Nat.max_zero] using h
  · have he : 0 < d.width := Nat.pos_of_ne_zero hw
    have hpositive := ArbitraryWidthOriginalRunWithin.runs_within cutoff hcut caller headers source d hs hp he hv ht hh x hf hhead
      lo hi (by
        intro j
        have hm := hmargin j
        change lo+_ ≤ (input caller).head j ∧ (input caller).head j+_ ≤ hi
        omega)
    have hyes : HoareWithin (ArbitraryWidthOriginalZeroBranch.zeroProgram headers source)
        (fun w => w = input caller ∧ ArbitraryWidthOriginalZeroBranch.test headers w.reads = true)
        (fun w => w = input (setTape caller source
          (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) 0 (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
      rintro w ⟨rfl,h⟩
      exact (hw (hz.mp h)).elim
    have hno : HoareWithin (ArbitraryWidthOriginalRun.program headers source)
        (fun w => w = input caller ∧ ArbitraryWidthOriginalZeroBranch.test headers w.reads = false)
        (fun w => w = input (setTape caller source
          (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0))
        (ArbitraryWidthOriginalRun.cost d hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) :=
      hpositive.consequence (fun _ h => h.1) (fun _ h => h) le_rfl (fun _ h => h)
    have h := HoareWithin.branch (ArbitraryWidthOriginalZeroBranch.test headers) hyes hno
    simpa only [program,ArbitraryWidthOriginalZeroBranch.program,cost,hw,ite_false,Nat.zero_max] using h

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalTotalRunWithin
