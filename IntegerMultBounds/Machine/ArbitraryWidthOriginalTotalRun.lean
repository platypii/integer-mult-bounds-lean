import IntegerMultBounds.Machine.ArbitraryWidthOriginalRun
import IntegerMultBounds.Machine.ArbitraryWidthOriginalZeroBranch

/-! One fixed original-descriptor machine covers zero and positive widths.
The actual canonical-width read selects the concrete proved branch; all
private metadata and execution banks start and finish blank. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthOriginalTotalRun
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

abbrev input := @ArbitraryWidthOriginalZeroBranch.input

def program (headers : Fin 6 → Fin t) (source : Fin t) :=
  ArbitraryWidthOriginalZeroBranch.program headers source (ArbitraryWidthOriginalRun.program headers source)

def zeroCoefficient := ArbitraryWidthElementary.coefficient+116
def cost (d : Descriptor) (hs : Fin 6 → List Bool) :=
  (if d.width = 0 then zeroCoefficient*volume prime d else ArbitraryWidthOriginalRun.cost d hs)+1

theorem runs (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs)
    (ht : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (headers i) = 1)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) :
    HoareTime (program headers source) (fun w => w = input caller)
      (fun w => w = input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) (cost d hs) := by
  have hz : ArbitraryWidthOriginalZeroBranch.test headers (input caller).reads = true ↔ d.width = 0 := by
    rw [ArbitraryWidthOriginalZeroBranch.test_true_iff caller headers (hs 3) (hv.2 3) (ht 3) (hh 3),hv.1 3]
    rfl
  by_cases hw : d.width = 0
  · have hzero := ArbitraryWidthOriginalZeroBranch.zero_hoare caller headers source d hs hp hw hv ht hh x hf hhead
    have hyes : HoareTime (ArbitraryWidthOriginalZeroBranch.zeroProgram headers source)
        (fun w => w = input caller ∧ ArbitraryWidthOriginalZeroBranch.test headers w.reads = true)
        (fun w => w = input (setTape caller source
          (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0))
        (zeroCoefficient*volume prime d) :=
      hzero.consequence (fun _ h => h.1) (fun _ h => h) le_rfl
    have hno : HoareTime (ArbitraryWidthOriginalRun.program headers source)
        (fun w => w = input caller ∧ ArbitraryWidthOriginalZeroBranch.test headers w.reads = false)
        (fun w => w = input (setTape caller source
          (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) 0 := by
      rintro w ⟨rfl,h⟩
      have htrue := hz.mpr hw
      rw [h] at htrue
      contradiction
    have h := branch_hoare (ArbitraryWidthOriginalZeroBranch.test headers) hyes hno
    simpa only [program,ArbitraryWidthOriginalZeroBranch.program,cost,hw,ite_true,Nat.max_zero] using h
  · have he : 0 < d.width := Nat.pos_of_ne_zero hw
    have hpositive := ArbitraryWidthOriginalRun.runs caller headers source d hs hp he hv ht hh x hf hhead
    have hyes : HoareTime (ArbitraryWidthOriginalZeroBranch.zeroProgram headers source)
        (fun w => w = input caller ∧ ArbitraryWidthOriginalZeroBranch.test headers w.reads = true)
        (fun w => w = input (setTape caller source
          (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) 0 := by
      rintro w ⟨rfl,h⟩
      exact (hw (hz.mp h)).elim
    have hno : HoareTime (ArbitraryWidthOriginalRun.program headers source)
        (fun w => w = input caller ∧ ArbitraryWidthOriginalZeroBranch.test headers w.reads = false)
        (fun w => w = input (setTape caller source
          (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0))
        (ArbitraryWidthOriginalRun.cost d hs) :=
      hpositive.consequence (fun _ h => h.1) (fun _ h => h) le_rfl
    have h := branch_hoare (ArbitraryWidthOriginalZeroBranch.test headers) hyes hno
    simpa only [program,ArbitraryWidthOriginalZeroBranch.program,cost,hw,ite_false,Nat.zero_max] using h

theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (d : Descriptor) (hs : Fin 6 → List Bool),
    d.Positive → RecursiveDimensionBank.Headers d hs →
    (cost d hs : ℝ) ≤ C*(volume prime d : ℝ)*((max 1 d.width : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := ArbitraryWidthOriginalRun.uniform_bound
  have hK : 0 ≤ (zeroCoefficient : ℝ) := Nat.cast_nonneg _
  refine ⟨C+(zeroCoefficient : ℝ)+1,by linarith,?_⟩
  intro d hs hp hv
  have hVnat := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le d hp
  have hV : 1 ≤ (volume prime d : ℝ) := by exact_mod_cast hVnat
  by_cases hw : d.width = 0
  · unfold cost
    rw [ite_eq_left hw,hw]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.max_zero,Real.one_rpow]
    nlinarith
  · have he : 0 < d.width := Nat.pos_of_ne_zero hw
    have hmax : max 1 d.width = d.width := max_eq_right he
    have hpow : 1 ≤ (d.width : ℝ)^Parameters.tau := Real.one_le_rpow (by exact_mod_cast he)
      Shared50RecursiveBudgetBound.exponent_range.1.le
    have hb := hbound d hs hp hv he
    have hVpow : 1 ≤ (volume prime d : ℝ)*(d.width : ℝ)^Parameters.tau := by nlinarith
    have hKpow : 0 ≤ (zeroCoefficient : ℝ)*((volume prime d : ℝ)*(d.width : ℝ)^Parameters.tau) :=
      mul_nonneg hK (by linarith)
    unfold cost
    rw [ite_eq_right hw,hmax]
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith only [hb,hVpow,hKpow]

end
end IntegerMultBounds.Machine.ArbitraryWidthOriginalTotalRun
