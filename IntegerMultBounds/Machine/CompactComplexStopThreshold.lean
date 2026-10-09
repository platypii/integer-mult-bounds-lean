import IntegerMultBounds.Machine.FixedBasePowerUntilRange
import IntegerMultBounds.Networks.ComplexRecursiveCallSchema

/-! The complex recursion stop threshold is generated once from the original
global dimension. Growing a fixed-base power only up to that dimension avoids
computing an unbounded thousandth power at every recursive node. -/
namespace IntegerMultBounds.Machine.CompactComplexStopThreshold
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {q : ℕ}

def base : ℕ := (25^3)^1000

theorem base_ge_two : 2 ≤ base := by
  exact (show 2 ≤ (25:ℕ)^3 by norm_num).trans
    (le_self_pow (by norm_num : 1 ≤ (25:ℕ)^3) (by decide : (1000:ℕ)≠0))

def threshold (D : ℕ) := Nat.clog base D

/-- This comparison uses only the generated stopping exponent. The leaf case
is explicit, so exponent-zero nodes never become positive-width stages. -/
theorem stopped_iff (D e : ℕ) :
    Networks.ComplexRecursiveCallSchema.stopped D e = true ↔
      e=0 ∨ e<threshold D := by
  rw [Networks.ComplexRecursiveCallSchema.stopped_iff]
  have hpow : ((25^3)^e)^1000 = base^e := by
    change ((25^3)^e)^1000 = ((25^3)^1000)^e
    calc
      ((25^3)^e)^1000 = (25^3)^(e*1000) := (pow_mul _ _ _).symm
      _ = (25^3)^(1000*e) := congrArg (fun k : ℕ => (25^3)^k) (Nat.mul_comm e 1000)
      _ = ((25^3)^1000)^e := pow_mul _ _ _
  rw [hpow]
  exact or_congr Iff.rfl (Nat.lt_clog_iff_pow_lt (by have := base_ge_two; omega)).symm

def output (_B r : ℕ) (ds : List Bool) : Tapes 9 q :=
  setTape (FixedBasePowerUntil.input ds) (7 : Fin 9)
    (BinaryDescriptorStack.descriptor (FixedBasePowerUntil.counter r)) 1

def program (B : ℕ) := seq (FixedBasePowerUntil.program (q := q) B)
  (BinaryDescriptorCleanupList.oneProgram (5 : Fin 9))

private theorem cleanup (B r : ℕ) (ds : List Bool) :
    HoareTime (BinaryDescriptorCleanupList.oneProgram (a := q) (5 : Fin 9))
      (fun v => v=FixedBasePowerUntil.output B r ds)
      (fun v => v=output B r ds) (2*(FixedBasePowerStep.bits B r).length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (5 : Fin 9)
    (FixedBasePowerUntil.output (q := q) B r ds) (FixedBasePowerStep.bits B r)
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- A fixed nine-tape machine retains only the original threshold word and the
new least exponent; every other tape is blank and reset. The fixed constant is
large, but independent of both the input and the recursive node. -/
theorem constructs (B D : ℕ) (hB : 2 ≤ B) (hD : 0 < D) (ds : List Bool)
    (hd : Counter.value ds=D) (hc : GrowingCounterData.Canonical ds) :
    HoareTime (program (q := q) B)
      (fun v => v=FixedBasePowerUntil.input ds)
      (fun v => v=output B (Nat.clog B D) ds)
      ((FixedBasePowerUntil.constant B*B+2*B+7)*D) := by
  have h0 := FixedBasePowerUntilRange.constructs_threshold_linear (q := q) B D hB hD ds hd hc
  have h1 := cleanup (q := q) B (Nat.clog B D) ds
  have hw := GrowingCounterData.canonical_width (FixedBasePowerStep.bits B (Nat.clog B D))
    (FixedBasePowerStep.bits_canonical B (Nat.clog B D))
  rw [FixedBasePowerStep.bits_value] at hw
  have hl := Nat.log2_le_self (B^(Nat.clog B D))
  have hp := FixedBasePowerUntilRange.final_power_lt B D hB hD
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h)
    (by nlinarith)

/-- Actual manuscript base, with no externally supplied stopping exponent. -/
theorem constructs_actual (D : ℕ) (hD : 0<D) (ds : List Bool)
    (hd : Counter.value ds=D) (hc : GrowingCounterData.Canonical ds) :
    HoareTime (program (q := q) base)
      (fun v => v=FixedBasePowerUntil.input ds)
      (fun v => v=output base (threshold D) ds)
      ((FixedBasePowerUntil.constant base*base+2*base+7)*D) :=
  constructs base D base_ge_two hD ds hd hc

end
end IntegerMultBounds.Machine.CompactComplexStopThreshold
