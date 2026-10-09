import IntegerMultBounds.Machine.FixedBasePowerDescriptor

/-! Bounds paying repeated scans while a fixed-base power grows to a runtime
threshold. The exponent is the genuine least stopping exponent. -/
namespace IntegerMultBounds.Machine.FixedBasePowerUntilBound

def rho (B D : ℕ) := Nat.clog B D

theorem dominates (B D : ℕ) (hB : 2 ≤ B) : D ≤ B ^ rho B D :=
  (Nat.clog_le_iff_le_pow (by omega)).mp le_rfl

theorem before (B D i : ℕ) (hB : 2 ≤ B) (hi : i < rho B D) : B ^ i < D :=
  (Nat.lt_clog_iff_pow_lt (by omega)).mp hi

theorem square_le_power (B n : ℕ) (hB : 2 ≤ B) : (n+1)^2 ≤ 8*B^n := by
  suffices hh : (n+1)^2 ≤ 8*2^n by
    exact hh.trans (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hB n))
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases hn : n < 2
    · interval_cases n <;> norm_num
    · rw [pow_succ 2 n]
      have hp : (n+2)^2 ≤ 2*(n+1)^2 := by nlinarith
      nlinarith

theorem descriptor_width (B D r : ℕ) (_hB : 2 ≤ B) (hD : D ≤ B^r)
    (ds : List Bool) (hv : Counter.value ds = D) (hc : GrowingCounterData.Canonical ds) :
    ds.length ≤ B*r+1 := by
  have hb : B ≤ 2^B := by
    have := FixedBasePowerDescriptor.depth_le_power 2 B (by omega)
    omega
  have hd : D ≤ 2^(B*r) := by
    calc D ≤ B^r := hD
         _ ≤ (2^B)^r := Nat.pow_le_pow_left hb r
         _ = 2^(B*r) := (pow_mul 2 B r).symm
  have hl := Nat.log_mono_right (b := 2) hd
  rw [Nat.log_pow (by omega)] at hl
  have hw := GrowingCounterData.canonical_width ds hc
  rw [hv,Nat.log2_eq_log_two] at hw
  omega

/-- Even scanning the retained threshold on every loop iteration fits the
final power. This includes one initial comparison. -/
theorem repeated_scan (B D r : ℕ) (hB : 2 ≤ B) (hD : D ≤ B^r)
    (ds : List Bool) (hv : Counter.value ds = D) (hc : GrowingCounterData.Canonical ds) :
    (r+1)*ds.length ≤ 8*(B+1)*B^r := by
  have hw := descriptor_width B D r hB hD ds hv hc
  have hs := square_le_power B r hB
  have hm := Nat.mul_le_mul_left (r+1) hw
  have hp := Nat.mul_le_mul_left (B+1) hs
  nlinarith

end IntegerMultBounds.Machine.FixedBasePowerUntilBound
