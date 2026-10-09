import IntegerMultBounds.Machine.ArbitraryWidthPieceCost
import IntegerMultBounds.Machine.ArbitraryWidthHighPrepare
import IntegerMultBounds.Machine.ArbitraryWidthHighLayout

/-! The actual high-row rounding increases payload volume by at most two.
The complete physical low-width dispatcher therefore retains its certified
exponent when paid against the original unpadded full-width array. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighPaddedBudget
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighPrepare (highDepth rounded rows)

def descriptor (P e G B : ℕ) : Descriptor :=
  ⟨P,rounded prime e,1,e-highDepth prime e,G,B⟩

/-- The physically selected depth supplies the complete recursive dispatch
width/divisibility premises without any externally chosen depth. -/
theorem width_fit (P e G B : ℕ) :
    (descriptor P e G B).width < 125000^(ArbitraryWidthHighPrepare.depth e+1) := by
  have he := FixedBasePowerUntilBound.dominates 125000 e (by decide : 2 ≤ 125000)
  change e ≤ 125000^(ArbitraryWidthHighPrepare.depth e) at he
  have hp : 0 < 125000^(ArbitraryWidthHighPrepare.depth e) := pow_pos (by decide) _
  change e-highDepth prime e < _
  rw [pow_succ]
  have hsub := Nat.sub_le e (highDepth prime e)
  nlinarith

theorem rows_divisible (P e G B : ℕ) :
    Shared50TapeGlobal.roleCount^(ArbitraryWidthHighPrepare.depth e) ∣
      (descriptor P e G B).rows :=
  ArbitraryWidthHighPrepare.rounded_divisible prime e

theorem positive (P e G B : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    (descriptor P e G B).Positive := by
  have hr := ArbitraryWidthHighPrepare.rows_le_rounded prime e Shared50ModularControl.prime_prime.two_le
  have hp := ArbitraryWidthHighPrepare.rows_positive prime e Shared50ModularControl.prime_prime.two_le
  exact ⟨hP,lt_of_lt_of_le hp hr,(by change 0 < 1; decide),hG,hB⟩

theorem volume_le (P e G B : ℕ) (hr : highDepth prime e ≤ e) :
    volume prime (descriptor P e G B) ≤
      2*volume prime (ArbitraryWidthHighLayout.originalDescriptor P e G B) := by
  have hR := RoundedRowDescriptor.rounded_lt_twice (rows prime e) (ArbitraryWidthHighPrepare.divisor e)
    (ArbitraryWidthHighPrepare.rows_positive prime e Shared50ModularControl.prime_prime.two_le)
    (ArbitraryWidthHighPrepare.divisor_le_rows prime e Shared50ModularControl.prime_prime.two_le)
  change rounded prime e < 2*rows prime e at hR
  have hrows : rows prime e = prime^(highDepth prime e)*prime^(highDepth prime e) := by
    simp only [rows,mul_pow]
  have hs := ArbitraryWidthHighLayout.split_power prime e (highDepth prime e) hr
  have h := Nat.mul_le_mul_left (P*G*B*prime^(e-highDepth prime e)*prime^(e-highDepth prime e)) hR.le
  rw [hrows] at h
  simp only [volume,descriptor,ArbitraryWidthHighLayout.originalDescriptor,mul_one]
  rw [hs]
  nlinarith only [h]

/-- The actual physical dispatcher on the generated padded shape requires
no independently supplied recursion depth, width envelope or row divisor. -/
theorem dispatches (P e G B : ℕ) (hs : Fin 6 → List Bool)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : RecursiveDimensionBank.Headers (descriptor P e G B) hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime (descriptor P e G B)) → ZMod 2) :
    HoareTime ArbitraryWidthPieceRun.program
      (fun z => z = ArbitraryWidthPieceSetup.input
        (ArbitraryWidthPieceSetup.bare (ArbitrarySliceCall.rootBank (ArbitrarySliceCall.data x)
          hs f p node scalar st) frame))
      (fun z => z = ArbitraryWidthPieceSetup.input
        (ArbitraryWidthPieceSetup.bare (ArbitrarySliceCall.rootBank
          (ArbitrarySliceCall.data (Shared50RecursiveNodeRows.transpose (one_dvd _) x))
          hs f p node scalar st) frame)) (ArbitraryWidthPieceRun.cost (descriptor P e G B) hs) := by
  exact ArbitraryWidthPieceRun.runs (descriptor P e G B) hs (ArbitraryWidthHighPrepare.depth e)
    (positive P e G B hP hG hB) hv (width_fit P e G B) (rows_divisible P e G B)
    f p node scalar st ready frame hfree x

/-- This is the runtime of the actual complete low dispatcher, including its
sole-header initialization and all private cleanup, rather than a cost oracle. -/
theorem piece_cost (P e G B : ℕ) (hs : Fin 6 → List Bool)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hr : highDepth prime e < e)
    (hv : RecursiveDimensionBank.Headers (descriptor P e G B) hs) :
    (ArbitraryWidthPieceRun.cost (descriptor P e G B) hs : ℝ) ≤
      (2*ArbitraryWidthPieceCost.coefficient)*
        (volume prime (ArbitraryWidthHighLayout.originalDescriptor P e G B) : ℝ)*
        (e : ℝ)^Parameters.tau := by
  have hp := positive P e G B hP hG hB
  have hw : 0 < (descriptor P e G B).width := by change 0 < e-highDepth prime e; omega
  have h := ArbitraryWidthPieceCost.cost_tau (descriptor P e G B) hs hp hv hw
  have hV : (volume prime (descriptor P e G B) : ℝ) ≤
      2*(volume prime (ArbitraryWidthHighLayout.originalDescriptor P e G B) : ℝ) := by
    exact_mod_cast volume_le P e G B hr.le
  have he : ((descriptor P e G B).width : ℝ)^Parameters.tau ≤ (e : ℝ)^Parameters.tau :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show (descriptor P e G B).width ≤ e from Nat.sub_le _ _))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have h1 := mul_le_mul_of_nonneg_left hV ArbitraryWidthPieceCost.coefficient_positive.le
  have h2 := mul_le_mul h1 he (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (mul_nonneg ArbitraryWidthPieceCost.coefficient_positive.le (by positivity))
  exact h.trans (by convert h2 using 1; ring)

end
end IntegerMultBounds.Machine.ArbitraryWidthHighPaddedBudget
