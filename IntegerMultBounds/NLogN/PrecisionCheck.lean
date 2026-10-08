import IntegerMultBounds.NLogN.MainParams
import IntegerMultBounds.NLogN.MainStep

/-! The precision condition of the recursive step, discharged from the paper's
parameter choices (step (3) of the proof of Proposition 5.4). With chunk size
`b`, precision `6b`, grid length `S ≤ T < n ≤ 2^b`, and transform errors
bounded by `2^(γ+5) T log₂ T`, the condition `2^(2b) S² (εI + 2εF + 2) < 2^(p-1)`
of `main_step` holds because `γ + 11 < b`; and `2 ⌈n/b⌉ ≤ S + 1` holds when
`T < 2S`. The error bound itself and the existence of a suitable `S` are
hypotheses here. -/

namespace IntegerMultBounds.NLogN

/-- `log₂ T ≤ b`, as `T < n ≤ 2^b`. -/
theorem log_transformSize_le {n : ℕ} (hn : 2 ≤ n) (hb : 8 ≤ chunkSize n) :
    Nat.log 2 (transformSize n) ≤ chunkSize n := by
  have hT : transformSize n < 2 ^ chunkSize n :=
    lt_of_lt_of_le (transformSize_lt hn hb) (n_le_two_pow_chunk n)
  exact (Nat.log_lt_of_lt_pow (by unfold transformSize; exact (pow_pos (by norm_num) _).ne') hT).le

/-- The precision condition in natural numbers: `2^(2b) S (S (3ε + 2)) 2 < 2^(6b)`. -/
theorem precision_ok_nat {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) (S : ℕ)
    (hS : S ≤ transformSize n) (ε : ℕ)
    (hε : ε ≤ 2 ^ (gammaParam d n + 5) * transformSize n * Nat.log 2 (transformSize n)) :
    2 ^ (2 * chunkSize n) * S * (S * (3 * ε + 2)) * 2 < 2 ^ precision n := by
  have hb := chunkSize_ge_4096 hd hn
  have hγ := gammaParam_add_lt hd hn
  have hn2 : 2 ≤ n :=
    le_trans (by calc 2 = 2 ^ 1 := by norm_num
                  _ ≤ 2 ^ (d ^ 12) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow _ _ (by omega))) hn
  have hL := log_transformSize_le hn2 (by omega)
  have hTb := (transformSize_bounds hn2).2
  have hT : transformSize n < 2 ^ chunkSize n :=
    lt_of_lt_of_le (transformSize_lt hn2 (by omega)) (n_le_two_pow_chunk n)
  set b := chunkSize n with hb'
  set T := transformSize n with hT'
  set γ := gammaParam d n with hγ'
  have hTL : T * Nat.log 2 T < 2 ^ (b + 3) := by
    calc T * Nat.log 2 T ≤ T * b := Nat.mul_le_mul_left _ hL
      _ < 8 * n := hTb
      _ ≤ 8 * 2 ^ b := Nat.mul_le_mul_left _ (n_le_two_pow_chunk n)
      _ = 2 ^ (b + 3) := by rw [pow_add]; ring
  have hε' : ε ≤ 2 ^ (γ + b + 8) := by
    calc ε ≤ 2 ^ (γ + 5) * T * Nat.log 2 T := hε
      _ = 2 ^ (γ + 5) * (T * Nat.log 2 T) := by ring
      _ ≤ 2 ^ (γ + 5) * 2 ^ (b + 3) := Nat.mul_le_mul_left _ hTL.le
      _ = 2 ^ (γ + b + 8) := by rw [← pow_add]; congr 1; ring
  have h3 : 3 * ε + 2 ≤ 2 ^ (γ + b + 10) := by
    have hP1 : 1 < 2 ^ (γ + b + 8) := Nat.one_lt_two_pow (by omega)
    have hP2 : 2 ^ (γ + b + 10) = 4 * 2 ^ (γ + b + 8) := by
      rw [show γ + b + 10 = (γ + b + 8) + 2 by ring, pow_add]; ring
    rw [hP2]
    set P := 2 ^ (γ + b + 8) with hP
    omega
  have hS' : S ≤ 2 ^ b := le_trans hS hT.le
  calc 2 ^ (2 * b) * S * (S * (3 * ε + 2)) * 2
      ≤ 2 ^ (2 * b) * 2 ^ b * (2 ^ b * 2 ^ (γ + b + 10)) * 2 :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ hS') (Nat.mul_le_mul hS' h3))
    _ = 2 ^ (5 * b + γ + 11) := by
        rw [show 5 * b + γ + 11 = 2 * b + b + (b + (γ + b + 10)) + 1 by ring]
        simp only [pow_add, pow_one]
    _ < 2 ^ (6 * b) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    _ = 2 ^ precision n := by rw [precision]

/-- The precision condition of `main_step`, in the real form it expects, under
Proposition 5.2's error bound `εF, εI ≤ 2^(γ+5) T log₂ T`. -/
theorem precision_ok {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) (S : ℕ)
    (hS : S ≤ transformSize n) {εF εI : ℝ}
    (hεF : εF ≤ 2 ^ (gammaParam d n + 5) * transformSize n * Nat.log 2 (transformSize n))
    (hεI : εI ≤ 2 ^ (gammaParam d n + 5) * transformSize n * Nat.log 2 (transformSize n)) :
    (2 : ℝ) ^ (2 * chunkSize n) * S * (S * (εI + (2 * εF + 2))) < 2 ^ precision n / 2 := by
  set E : ℕ := 2 ^ (gammaParam d n + 5) * transformSize n * Nat.log 2 (transformSize n)
    with hE
  have hnat := precision_ok_nat hd hn S hS E le_rfl
  set X : ℕ := 2 ^ (2 * chunkSize n) * S * (S * (3 * E + 2)) with hX
  have hEr : (2 : ℝ) ^ (gammaParam d n + 5) * transformSize n * Nat.log 2 (transformSize n)
      = (E : ℝ) := by rw [hE]; push_cast; ring
  rw [hEr] at hεF hεI
  have h1 : εI + (2 * εF + 2) ≤ 3 * (E : ℝ) + 2 := by linarith
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have h2 : (2 : ℝ) ^ (2 * chunkSize n) * S * (S * (εI + (2 * εF + 2))) ≤ (X : ℝ) := by
    rw [hX]; push_cast
    gcongr
  have h3 : (X : ℝ) * 2 < 2 ^ precision n := by exact_mod_cast hnat
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The digit-count condition of `main_step`: with `b = ⌈log₂ n⌉` chunks of
`n` bits and `T < 2S`, the two digit lists together have at most `S + 1` entries. -/
theorem digits_fit {n : ℕ} (hn : 2 ≤ n) {x y : List Bool} (hx : x.length = n)
    (hy : y.length = n) (S : ℕ) (hS : transformSize n < 2 * S) :
    (digitsOf (chunkSize n) x).length + (digitsOf (chunkSize n) y).length ≤ S + 1 := by
  have hb : 1 ≤ chunkSize n := Nat.clog_pos (by norm_num) (by omega)
  have h4 := (transformSize_bounds hn).1
  have hxl := digitsOf_length_le_div hb x
  have hyl := digitsOf_length_le_div hb y
  rw [hx] at hxl
  rw [hy] at hyl
  set b := chunkSize n with hb'
  set T := transformSize n with hT'
  set q := (n + b - 1) / b with hq
  have hqb : q * b ≤ n + b - 1 := Nat.div_mul_le_self _ _
  -- `4 (q − 1) b < 4 n ≤ T b`, hence `4 (q − 1) < T`.
  have hlt : 4 * (q - 1) * b < T * b := by
    rw [mul_assoc, Nat.sub_mul, one_mul]
    set m := q * b with hm
    set Tb := T * b with hTb
    omega
  have hqT : 4 * (q - 1) < T := Nat.lt_of_mul_lt_mul_right hlt
  omega

end IntegerMultBounds.NLogN
