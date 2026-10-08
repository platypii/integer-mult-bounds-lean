import IntegerMultBounds.NLogN.Multiplier

/-! An a priori bit cost for the plain FFT multiplier of `Multiplier.lean` on
small inputs. For `q`-bit integers the chunk size is `⌈log₂ q⌉`, the transform
length is at most `8 q / log₂ q + 8`, and the precision is at most
`3 log₂ q + 13` bits. Proved: with these parameters, zero error oracles, and
the root `e^(2πi/2^m)`, the multiplier returns the exact product; and the
operation count, in an operation-count model where every fixed-point word
product costs `2 p²` bit operations and every word addition `2 p` (schoolbook
word arithmetic), is at most `10^6 q (log₂ q)²` for every `q ≥ 2`. This is the
fixed-constant bound used for the `O(log n)`-bit products inside the weight
evaluations of the main algorithm. Tape steps are not modelled. -/

namespace IntegerMultBounds.NLogN

open Real

/-- Chunk size for `q`-bit inputs. -/
def smallK (q : ℕ) : ℕ := Nat.clog 2 q

/-- Number of chunks per input. -/
def smallN (q : ℕ) : ℕ := (q + smallK q - 1) / smallK q

/-- Padded input length, a multiple of the chunk size. -/
def smallLen (q : ℕ) : ℕ := smallK q * smallN q

/-- Number of output digits, `k * L = 2 n`. -/
def smallL (q : ℕ) : ℕ := 2 * smallN q

/-- Transform exponent. -/
def smallM (q : ℕ) : ℕ := Nat.clog 2 (2 * smallL q)

/-- Precision in bits. -/
def smallP (q : ℕ) : ℕ := 2 * smallM q + 4 + smallK q

theorem smallK_pos {q : ℕ} (hq : 2 ≤ q) : 1 ≤ smallK q :=
  Nat.clog_pos (by norm_num) (by omega)

theorem log_le_smallK (q : ℕ) : Nat.log 2 q ≤ smallK q := Nat.log_le_clog 2 q

theorem smallK_le (q : ℕ) : smallK q ≤ Nat.log 2 q + 1 := by
  unfold smallK
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  exact (Nat.lt_pow_succ_log_self (by norm_num) q).le

theorem smallN_pos {q : ℕ} (hq : 2 ≤ q) : 1 ≤ smallN q := by
  have hk := smallK_pos hq
  unfold smallN
  rw [Nat.le_div_iff_mul_le (by omega)]
  omega

theorem smallN_le {q : ℕ} (hq : 2 ≤ q) : smallN q ≤ q / smallK q + 1 := by
  have hk := smallK_pos hq
  unfold smallN
  have h := Nat.div_lt_iff_lt_mul (x := q + smallK q - 1) (y := q / smallK q + 2) (k := smallK q)
    (by omega)
  have hdm := Nat.div_add_mod q (smallK q)
  have hml := Nat.mod_lt q (show 0 < smallK q by omega)
  have : (q + smallK q - 1) / smallK q < q / smallK q + 2 := by
    rw [h, Nat.add_mul, mul_comm]
    generalize smallK q * (q / smallK q) = A at *
    omega
  omega

theorem le_smallLen {q : ℕ} (hq : 2 ≤ q) : q ≤ smallLen q := by
  have hk := smallK_pos hq
  unfold smallLen smallN
  have hdm := Nat.div_add_mod (q + smallK q - 1) (smallK q)
  have hml := Nat.mod_lt (q + smallK q - 1) (show 0 < smallK q by omega)
  generalize smallK q * ((q + smallK q - 1) / smallK q) = A at *
  omega

theorem smallLen_lt {q : ℕ} (hq : 2 ≤ q) : smallLen q < q + smallK q := by
  have hk := smallK_pos hq
  unfold smallLen smallN
  have hdm := Nat.div_add_mod (q + smallK q - 1) (smallK q)
  generalize smallK q * ((q + smallK q - 1) / smallK q) = A at *
  omega

theorem smallL_pos {q : ℕ} (hq : 2 ≤ q) : 1 ≤ smallL q := by
  unfold smallL; have := smallN_pos hq; omega

theorem smallM_pos {q : ℕ} (hq : 2 ≤ q) : 1 ≤ smallM q := by
  have := smallL_pos hq
  exact Nat.clog_pos (by norm_num) (by unfold smallL at *; omega)

theorem two_pow_smallM_le {q : ℕ} (hq : 2 ≤ q) :
    2 ^ smallM q ≤ 8 * (q / smallK q) + 8 := by
  have h1 : 2 ^ smallM q ≤ 4 * smallL q := pow_clog_le (smallL_pos hq)
  have h2 := smallN_le hq
  unfold smallL at h1
  omega

theorem smallL_le {q : ℕ} (hq : 2 ≤ q) : 2 * smallL q ≤ 8 * q := by
  have h := smallN_le hq
  have h' : q / smallK q ≤ q := Nat.div_le_self q _
  unfold smallL; omega

theorem smallM_le {q : ℕ} (hq : 2 ≤ q) : smallM q ≤ Nat.log 2 q + 4 := by
  unfold smallM
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  have h1 := smallL_le hq
  have h2 : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  calc 2 * smallL q ≤ 8 * q := h1
    _ ≤ 8 * 2 ^ (Nat.log 2 q + 1) := by omega
    _ = 2 ^ (Nat.log 2 q + 4) := by ring

theorem smallP_le {q : ℕ} (hq : 2 ≤ q) : smallP q ≤ 3 * Nat.log 2 q + 13 := by
  have := smallM_le hq
  have := smallK_le q
  unfold smallP; omega

theorem smallP_le' {q : ℕ} (hq : 2 ≤ q) : smallP q ≤ 16 * Nat.log 2 q := by
  have := smallP_le hq
  have hl : 1 ≤ Nat.log 2 q := Nat.log_pos (by norm_num) hq
  omega

/-- Leading zero bits do not change the value. -/
theorem binaryValue_replicate_false_append (c : ℕ) (x : List Bool) :
    Machine.binaryValue (List.replicate c false ++ x) = Machine.binaryValue x := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [List.replicate_succ, List.cons_append]
    simp [Machine.binaryValue, ih]

/-- The padded input. -/
def smallPad (q : ℕ) (x : List Bool) : List Bool :=
  List.replicate (smallLen q - q) false ++ x

theorem smallPad_length {q : ℕ} (hq : 2 ≤ q) {x : List Bool} (hx : x.length = q) :
    (smallPad q x).length = smallLen q := by
  have := le_smallLen hq
  simp [smallPad, hx]; omega

/-- The root of unity used by the small multiplier. -/
noncomputable def smallRoot (q : ℕ) : ℂ :=
  Complex.exp (2 * π * Complex.I / ((2 ^ smallM q : ℕ) : ℂ))

theorem smallRoot_primitive (q : ℕ) : IsPrimitiveRoot (smallRoot q) (2 ^ smallM q) :=
  Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ (by norm_num))

/-- The exact product via the plain FFT multiplier with zero error oracles. -/
noncomputable def smallMul (q : ℕ) (x y : List Bool) : List Bool :=
  mulFixed (smallK q) (smallL q) (smallM q) (smallRoot q) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ => 0) (smallPad q x) (smallPad q y)

theorem smallMul_correct {q : ℕ} (hq : 2 ≤ q) {x y : List Bool} (hx : x.length = q)
    (hy : y.length = q) :
    Machine.binaryValue (smallMul q x y) = Machine.binaryValue x * Machine.binaryValue y ∧
      (smallMul q x y).length = 2 * smallLen q := by
  have hk := smallK_pos hq
  have hx' := smallPad_length hq hx
  have hy' := smallPad_length hq hy
  have hL : smallK q * smallL q = 2 * smallLen q := by unfold smallL smallLen; ring
  have h := mulFixed_correct (p := smallP q) (by omega) (smallRoot_primitive q)
    (e₁ := fun _ _ => 0) (e₂ := fun _ _ => 0) (e₃ := fun _ _ => 0) (r := fun _ => 0)
    (fun i j => by simp) (fun i j => by simp)
    (fun i j => by simp) (fun j => by simp)
    (le_refl _) hx' hy' hL (mulFixed_params (by omega) hx' hy' hL)
  unfold smallMul
  refine ⟨?_, h.2⟩
  rw [h.1]
  simp [smallPad, binaryValue_replicate_false_append]

theorem smallMul_exists {q : ℕ} (hq : 2 ≤ q) {x y : List Bool} (hx : x.length = q)
    (hy : y.length = q) :
    ∃ out : List Bool, Machine.binaryValue out = Machine.binaryValue x * Machine.binaryValue y ∧
      out.length = 2 * (smallK q * smallN q) :=
  ⟨smallMul q x y, smallMul_correct hq hx hy⟩

/-- Bit operations of the small multiplier: each of the `mulFixedOps m` fixed-point
complex operations is at most four real word products (`2 p²` bit operations each)
and four word additions (`2 p` each), plus `8 q p` for chunking, rounding, and
carry propagation. -/
def smallMulBits (q : ℕ) : ℕ :=
  mulFixedOps (smallM q) * (8 * smallP q ^ 2 + 8 * smallP q) + 8 * q * smallP q

theorem mulFixedOps_smallM_le {q : ℕ} (hq : 2 ≤ q) : mulFixedOps (smallM q) ≤ 448 * q := by
  have hl : 1 ≤ Nat.log 2 q := Nat.log_pos (by norm_num) hq
  have hlq : Nat.log 2 q ≤ q := Nat.log_le_self 2 q
  have h1 := mulFixedOps_le (smallM_pos hq)
  have h2 := two_pow_smallM_le hq
  have h3 := smallM_le hq
  have hkl := log_le_smallK q
  have hdiv : q / smallK q ≤ q / Nat.log 2 q := Nat.div_le_div_left hkl (by omega)
  have hA : Nat.log 2 q * (q / Nat.log 2 q) ≤ q := Nat.mul_div_le q _
  have hB : q / Nat.log 2 q ≤ q := Nat.div_le_self q _
  generalize hd : q / Nat.log 2 q = d at *
  generalize hℓ : Nat.log 2 q = ℓ at *
  calc mulFixedOps (smallM q) ≤ 7 * smallM q * 2 ^ smallM q := h1
    _ ≤ 7 * (ℓ + 4) * (8 * d + 8) := by
        apply Nat.mul_le_mul
        · omega
        · omega
    _ = 56 * (ℓ * d) + 56 * (4 * d) + 56 * (ℓ + 4) := by ring
    _ ≤ 56 * q + 56 * (4 * q) + 56 * (3 * q) := by
        have : ℓ + 4 ≤ 3 * q := by omega
        have : 4 * d ≤ 4 * q := by omega
        omega
    _ = 448 * q := by ring

theorem smallMulBits_le {q : ℕ} (hq : 2 ≤ q) :
    smallMulBits q ≤ 10 ^ 6 * q * Nat.log 2 q ^ 2 := by
  have hl : 1 ≤ Nat.log 2 q := Nat.log_pos (by norm_num) hq
  have h1 := mulFixedOps_smallM_le hq
  have h2 := smallP_le' hq
  unfold smallMulBits
  generalize hℓ : Nat.log 2 q = ℓ at *
  generalize smallP q = p at *
  generalize mulFixedOps (smallM q) = ops at *
  have hp2 : 8 * p ^ 2 + 8 * p ≤ 2176 * ℓ ^ 2 := by nlinarith
  have hp' : p ≤ 16 * ℓ ^ 2 := by nlinarith
  have hqp : 8 * q * p ≤ 128 * q * ℓ ^ 2 := by
    calc 8 * q * p ≤ 8 * q * (16 * ℓ ^ 2) := Nat.mul_le_mul_left _ hp'
      _ = 128 * q * ℓ ^ 2 := by ring
  calc ops * (8 * p ^ 2 + 8 * p) + 8 * q * p
      ≤ 448 * q * (2176 * ℓ ^ 2) + 128 * q * ℓ ^ 2 := by
        have := Nat.mul_le_mul h1 hp2
        omega
    _ ≤ 10 ^ 6 * q * ℓ ^ 2 := by nlinarith

theorem smallMulBits_le_cube {q : ℕ} (hq : 2 ≤ q) :
    smallMulBits q ≤ 10 ^ 6 * q * Nat.log 2 q ^ 3 := by
  have hl : 1 ≤ Nat.log 2 q := Nat.log_pos (by norm_num) hq
  have := smallMulBits_le hq
  calc smallMulBits q ≤ 10 ^ 6 * q * Nat.log 2 q ^ 2 := this
    _ ≤ 10 ^ 6 * q * Nat.log 2 q ^ 3 := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega) (by norm_num)

/-- The hypothesis shape used by the joint cost recurrence. -/
theorem exists_small_multiplier_cost :
    ∃ K₁ : ℕ, ∀ q, 2 ≤ q → smallMulBits q ≤ K₁ * q * Nat.log 2 q ^ 3 :=
  ⟨10 ^ 6, fun _ hq => smallMulBits_le_cube hq⟩

end IntegerMultBounds.NLogN
