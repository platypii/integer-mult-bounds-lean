import IntegerMultBounds.Machine.FixedBasePowerUntil
import IntegerMultBounds.Machine.ArbitraryWidthHighRows

/-! The actual least-power selector costs linearly in its input threshold.
Its runtime exponent is exactly the manuscript
parameter for selecting recursive depth or paired high-digit rows. -/
namespace IntegerMultBounds.Machine.FixedBasePowerUntilRange
variable {q : ℕ}

theorem final_power_lt (B D : ℕ) (hB : 2 ≤ B) (hD : 0 < D) :
    B^(Nat.clog B D) < B*D := by
  by_cases hr : Nat.clog B D = 0
  · rw [hr,pow_zero]
    nlinarith
  · have hp : B^(Nat.clog B D-1) < D :=
      (Nat.lt_clog_iff_pow_lt (by omega)).mp (by omega)
    have he : Nat.clog B D = (Nat.clog B D-1)+1 := by omega
    rw [he,pow_succ]
    have hm := Nat.mul_lt_mul_of_pos_right hp (show 0 < B by omega)
    simpa only [Nat.mul_comm] using hm

theorem constructs_threshold_linear (B D : ℕ) (hB : 2 ≤ B) (hD : 0 < D)
    (ds : List Bool) (hd : Counter.value ds = D) (cd : GrowingCounterData.Canonical ds) :
    HoareTime (FixedBasePowerUntil.program (q := q) B)
      (fun v => v = FixedBasePowerUntil.input ds)
      (fun v => v = FixedBasePowerUntil.output B (Nat.clog B D) ds)
      ((FixedBasePowerUntil.constant B*B)*D) := by
  apply (FixedBasePowerUntil.constructs_linear B D hB ds hd cd).consequence
    (fun _ h => h) (fun _ h => h)
  have hm := Nat.mul_le_mul_left (FixedBasePowerUntil.constant B)
    (final_power_lt B D hB hD).le
  simpa only [FixedBasePowerUntilBound.rho,Nat.mul_assoc] using hm

theorem paired_exponent (radix D : ℕ) :
    Nat.clog (radix*radix) D = ArbitraryWidthHighRows.rho radix D := rfl

theorem paired_value (radix D : ℕ) :
    (radix*radix)^(Nat.clog (radix*radix) D) = ArbitraryWidthHighRows.rowCount radix D :=
  (ArbitraryWidthHighRows.square_power radix (ArbitraryWidthHighRows.rho radix D)).symm

end IntegerMultBounds.Machine.FixedBasePowerUntilRange
