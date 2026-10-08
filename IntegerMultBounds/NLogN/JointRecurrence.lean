import IntegerMultBounds.NLogN.ResamplingOps

/-! The cost recurrence closed with an a priori cost for the small products.

`step_cost_nlogn` in `ResamplingOps` bounds a cost `M` by one full recursive
step whose resampling part evaluates `Mcost p = M p` on the small argument
`p = 6 ⌈log₂ n⌉`, so its per-row hypothesis still mentions `M`. Here the step is
split into two cost functions: `Mbig`, used for the delegated products of
size `3rp` (the recursion), and `Msmall`, used for the `p`-bit products inside
the resampling weights, for which any fixed algorithm with a polylogarithmic
overhead suffices (for instance the plain FFT multiplier of `Multiplier`,
whose word operations give `q (log₂ q)³`).

Proved: with weight evaluations costing at most `K₀ q (log₂ q)⁴` and small
products at most `K₁ q (log₂ q)³`, the per-row resampling cost is at most
`30 (K₀ + K₁ + 2) b²` once `b ≥ 2^624`, which holds for
`n ≥ 2^(2^624)` (a larger threshold than the paper's `2^(1729^12)`, because the
paper's `O(·)` hides the constants; the literal is never unfolded, see the
threshold section); hence any cost bounded above that
threshold by one full step plus a linear overhead, and below it by the a priori
`K₁ n (log₂ n)³`, is `O(n log n)`. No hypothesis mentions `M` on the
resampling side.

Not modelled: the bit cost of the weight evaluations (`Ecost`), tape steps,
and data rearrangement. -/

namespace IntegerMultBounds.NLogN

/-! ### The step with two cost functions -/

/-- One recursive step with the delegated products costed by `Mbig` and the
small products inside the resampling weights by `Msmall`. -/
def stepOps₂ {d k : ℕ} (r p : ℕ) (e : Fin k → ℕ) (s t : Fin d → ℕ) (mA mE nJ : ℕ)
    (Ecost Msmall Mbig : ℕ → ℕ) : ℕ :=
  3 * pipelineOps r p e Mbig + resampPart s t mA mE p nJ Ecost Msmall

/-- One full recursive step at `d = 1729`: `(12 T / r) Mbig(3rp) + O(n log n)`,
with the per-row condition on `Msmall` only. -/
theorem stepOps₂_params_le {n : ℕ} (hn : 2 ^ (1729 ^ 12) ≤ n) (s t : Fin 1729 → ℕ)
    (ht : ∀ i, 0 < t i) (hst : ∀ i, s i ≤ t i) (hT : ∏ j, t j = transformSize n)
    (Ecost Msmall Mbig : ℕ → ℕ) (K : ℕ)
    (hrow : alphaParam 1729 n * (Nat.sqrt (precision n) + 1) *
      termOps (precision n) Ecost Msmall ≤ K * chunkSize n ^ 2) :
    stepOps₂ (rootSize 1729 n) (precision n) (modelExponents 1729 n) s t
        (paperWindowA (precision n) (alphaParam 1729 n))
        (paperWindowE (precision n) (alphaParam 1729 n)) (paperIter (alphaParam 1729 n))
        Ecost Msmall Mbig ≤
      (12 * transformSize n / rootSize 1729 n) * Mbig (3 * rootSize 1729 n * precision n) +
        (2880 + 4320 * K * 1729) * n * Nat.log 2 n := by
  have hd : 2 ≤ 1729 := by norm_num
  have hpipe := main_ops_le' hd hn (modelExponents 1729 n) (modelExponents_prod hd hn) Mbig
  have hres := resampPart_nlogn hd hn s t ht hst hT Ecost Msmall K hrow
  clear hn hrow
  unfold stepOps₂
  have : (2880 + 4320 * K * 1729) * n * Nat.log 2 n =
      2880 * n * Nat.log 2 n + 4320 * K * 1729 * n * Nat.log 2 n := by ring
  rw [this]
  omega

/-! ### Elementary growth lemmas -/

theorem sq_le_two_pow_of_four_le {m : ℕ} (hm : 4 ≤ m) : m ^ 2 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h : 2 * m + 1 ≤ m ^ 2 := by nlinarith
    calc (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
      _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add ih (le_trans h ih)
      _ = 2 ^ (m + 1) := by ring

theorem lin_le_two_pow_of_le {q : ℕ} (hq : 26 ≤ q) : 24 * q + 27 ≤ 2 ^ q := by
  have h1 : 24 * q + 27 ≤ q ^ 2 := by nlinarith
  exact le_trans h1 (sq_le_two_pow_of_four_le (by omega))

/-- `(m + 4)^8 ≤ 2^(m/3)` for `m ≥ 624`. -/
theorem add_four_pow_eight_le {m : ℕ} (hm : 624 ≤ m) : (m + 4) ^ 8 ≤ 2 ^ (m / 3) := by
  set q := m / 3 with hq
  set r := q / 8 with hr
  have hq1 : 3 * q ≤ m := by omega
  have hq2 : m ≤ 3 * q + 2 := by omega
  have hr1 : 8 * r ≤ q := by omega
  have hr2 : q ≤ 8 * r + 7 := by omega
  have hr26 : 26 ≤ r := by omega
  have h1 : m + 4 ≤ 24 * r + 27 := by omega
  have h2 : m + 4 ≤ 2 ^ r := le_trans h1 (lin_le_two_pow_of_le hr26)
  calc (m + 4) ^ 8 ≤ (2 ^ r) ^ 8 := Nat.pow_le_pow_left h2 8
    _ = 2 ^ (8 * r) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hr1

/-- `log₂ (6 b) ≤ log₂ b + 3`. -/
theorem log_six_mul_le {b : ℕ} (hb : b ≠ 0) : Nat.log 2 (6 * b) ≤ Nat.log 2 b + 3 := by
  have h8 : Nat.log 2 (b * 2 * 2 * 2) = Nat.log 2 b + 3 := by
    rw [Nat.log_mul_base (by norm_num) (by positivity),
      Nat.log_mul_base (by norm_num) (by positivity),
      Nat.log_mul_base (by norm_num) hb]
  calc Nat.log 2 (6 * b) ≤ Nat.log 2 (b * 2 * 2 * 2) :=
        Nat.log_mono_right (by omega)
    _ = Nat.log 2 b + 3 := h8

theorem le_log_of_two_pow_le {E b : ℕ} (hb : b ≠ 0) (h : 2 ^ E ≤ b) : E ≤ Nat.log 2 b :=
  (Nat.le_log_iff_pow_le (by norm_num) hb).mpr h

/-- A lower bound on the chunk size from a lower bound on `n`. -/
theorem chunkSize_ge_of_pow_le {k n : ℕ} (hn : 2 ^ k ≤ n) : k ≤ chunkSize n := by
  unfold chunkSize
  rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · have : k - 1 < Nat.clog 2 n := by
      rw [Nat.lt_clog_iff_pow_lt (by norm_num)]
      calc 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
        _ ≤ n := hn
    omega

/-! ### The per-row condition from polylogarithmic small costs -/

/-- If the per-term cost is at most `p K' L⁴` with `L = log₂ p + 1`, then the
per-row resampling cost `α (√p + 1) c` is at most `30 K' b²` as soon as `b`
has a cube root `c` with `864 L⁸ ≤ 900 c` and `b ≥ 2^46`. -/
theorem row_cost_of_polylog {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n)
    (hb : 2 ^ 46 ≤ chunkSize n) (Ecost Msmall : ℕ → ℕ) (K' c : ℕ)
    (hterm : termOps (precision n) Ecost Msmall ≤
      precision n * K' * (Nat.log 2 (precision n) + 1) ^ 4)
    (hc : c ^ 3 ≤ chunkSize n)
    (hL : 864 * (Nat.log 2 (precision n) + 1) ^ 8 ≤ 900 * c) :
    alphaParam d n * (Nat.sqrt (precision n) + 1) * termOps (precision n) Ecost Msmall ≤
      30 * K' * chunkSize n ^ 2 := by
  have hα3 := alphaParam_cube_le hd hn hb
  have hp : precision n = 6 * chunkSize n := rfl
  set a := alphaParam d n
  set b := chunkSize n
  set p := precision n
  set L := Nat.log 2 p + 1
  have hac : a ^ 2 * c ≤ b := by
    have : (a ^ 2 * c) ^ 3 ≤ b ^ 3 := by
      calc (a ^ 2 * c) ^ 3 = (a ^ 3) ^ 2 * c ^ 3 := by ring
        _ ≤ b ^ 2 * b := Nat.mul_le_mul (Nat.pow_le_pow_left hα3 2) hc
        _ = b ^ 3 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
  have hsq : (Nat.sqrt p + 1) ^ 2 ≤ 4 * p := by
    have h1 : Nat.sqrt p ^ 2 ≤ p := Nat.sqrt_le' p
    have h2 : Nat.sqrt p ≤ p := Nat.sqrt_le_self p
    have hp1 : 1 ≤ p := by rw [hp]; omega
    nlinarith
  have hmain : (6 * (a * (Nat.sqrt p + 1) * (K' * L ^ 4))) ^ 2 ≤ (30 * K' * b) ^ 2 := by
    have h864 : 864 * (a ^ 2 * (K' ^ 2 * L ^ 8)) ≤ 900 * K' ^ 2 * (a ^ 2 * c) := by
      calc 864 * (a ^ 2 * (K' ^ 2 * L ^ 8)) = a ^ 2 * K' ^ 2 * (864 * L ^ 8) := by ring
        _ ≤ a ^ 2 * K' ^ 2 * (900 * c) := Nat.mul_le_mul_left _ hL
        _ = 900 * K' ^ 2 * (a ^ 2 * c) := by ring
    calc (6 * (a * (Nat.sqrt p + 1) * (K' * L ^ 4))) ^ 2
        = 36 * a ^ 2 * (Nat.sqrt p + 1) ^ 2 * (K' ^ 2 * L ^ 8) := by ring
      _ ≤ 36 * a ^ 2 * (4 * p) * (K' ^ 2 * L ^ 8) := by gcongr
      _ = b * (864 * (a ^ 2 * (K' ^ 2 * L ^ 8))) := by rw [hp]; ring
      _ ≤ b * (900 * K' ^ 2 * (a ^ 2 * c)) := Nat.mul_le_mul_left _ h864
      _ ≤ b * (900 * K' ^ 2 * b) := by gcongr
      _ = (30 * K' * b) ^ 2 := by ring
  have hroot : 6 * (a * (Nat.sqrt p + 1) * (K' * L ^ 4)) ≤ 30 * K' * b :=
    (Nat.pow_le_pow_iff_left (by norm_num)).mp hmain
  calc a * (Nat.sqrt p + 1) * termOps p Ecost Msmall
      ≤ a * (Nat.sqrt p + 1) * (p * K' * L ^ 4) := Nat.mul_le_mul_left _ hterm
    _ = (6 * (a * (Nat.sqrt p + 1) * (K' * L ^ 4))) * b := by rw [hp]; ring
    _ ≤ (30 * K' * b) * b := Nat.mul_le_mul_right _ hroot
    _ = 30 * K' * b ^ 2 := by ring

/-- The per-term cost from polylogarithmic weight and small-product costs. -/
theorem termOps_le_polylog {p : ℕ} (Ecost Msmall : ℕ → ℕ) (K₀ K₁ : ℕ)
    (hE : Ecost p ≤ K₀ * p * (Nat.log 2 p) ^ 4)
    (hM : Msmall p ≤ K₁ * p * (Nat.log 2 p) ^ 3) :
    termOps p Ecost Msmall ≤ p * (K₀ + K₁ + 2) * (Nat.log 2 p + 1) ^ 4 := by
  set L := Nat.log 2 p + 1
  have hL1 : 1 ≤ L := by omega
  have h4 : (Nat.log 2 p) ^ 4 ≤ L ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h3 : (Nat.log 2 p) ^ 3 ≤ L ^ 4 :=
    le_trans (Nat.pow_le_pow_left (by omega) 3) (Nat.pow_le_pow_right hL1 (by norm_num))
  have hone : 1 ≤ L ^ 4 := Nat.one_le_pow _ _ hL1
  unfold termOps
  calc Ecost p + Msmall p + 2 * p
      ≤ K₀ * p * L ^ 4 + K₁ * p * L ^ 4 + 2 * p * L ^ 4 := by
        have hE' : Ecost p ≤ K₀ * p * L ^ 4 := le_trans hE (Nat.mul_le_mul_left _ h4)
        have hM' : Msmall p ≤ K₁ * p * L ^ 4 := le_trans hM (Nat.mul_le_mul_left _ h3)
        have h2 : 2 * p ≤ 2 * p * L ^ 4 := Nat.le_mul_of_pos_right _ (by omega)
        omega
    _ = p * (K₀ + K₁ + 2) * L ^ 4 := by ring

/-- Above `b ≥ 2^624`, polylogarithmic weight and small-product costs give the
per-row condition with constant `30 (K₀ + K₁ + 2)`. -/
theorem row_threshold {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n)
    (hb : 2 ^ 624 ≤ chunkSize n) (Ecost Msmall : ℕ → ℕ) (K₀ K₁ : ℕ)
    (hE : Ecost (precision n) ≤ K₀ * precision n * (Nat.log 2 (precision n)) ^ 4)
    (hM : Msmall (precision n) ≤ K₁ * precision n * (Nat.log 2 (precision n)) ^ 3) :
    alphaParam d n * (Nat.sqrt (precision n) + 1) * termOps (precision n) Ecost Msmall ≤
      30 * (K₀ + K₁ + 2) * chunkSize n ^ 2 := by
  have hb46 : 2 ^ 46 ≤ chunkSize n :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hb
  have hterm := termOps_le_polylog Ecost Msmall K₀ K₁ hE hM
  set b := chunkSize n
  have hb0 : b ≠ 0 := by positivity
  set m := Nat.log 2 b with hm
  have hm624 : 624 ≤ m := le_log_of_two_pow_le hb0 hb
  clear hb
  have hp : precision n = 6 * b := rfl
  have hLm : Nat.log 2 (precision n) + 1 ≤ m + 4 := by
    rw [hp]
    have := log_six_mul_le hb0
    omega
  refine row_cost_of_polylog hd hn hb46 Ecost Msmall (K₀ + K₁ + 2) (2 ^ (m / 3)) hterm ?_ ?_
  · calc (2 ^ (m / 3)) ^ 3 = 2 ^ (3 * (m / 3)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le m 3)
      _ ≤ b := Nat.pow_log_le_self 2 hb0
  · calc 864 * (Nat.log 2 (precision n) + 1) ^ 8 ≤ 864 * (m + 4) ^ 8 := by gcongr
      _ ≤ 864 * 2 ^ (m / 3) := Nat.mul_le_mul_left _ (add_four_pow_eight_le hm624)
      _ ≤ 900 * 2 ^ (m / 3) := Nat.mul_le_mul_right _ (by norm_num)

/-! ### The threshold

The threshold `2^(2^624)` is written out literally everywhere: the kernel
folds `Nat.pow` on literal arguments during lazy delta reduction and refuses
exponents beyond 32 bits, so every helper is stated with a variable exponent
and only instantiated, never unfolded. -/

theorem pow_twelve_le_two_pow_joint {x k e : ℕ} (hx : x ≤ 2 ^ k) (hke : k * 12 ≤ e) :
    x ^ 12 ≤ 2 ^ e :=
  calc x ^ 12 ≤ (2 ^ k) ^ 12 := Nat.pow_le_pow_left hx 12
    _ = 2 ^ (k * 12) := by rw [← pow_mul]
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hke

theorem paper_exp_le : 1729 ^ 12 ≤ 2 ^ 624 :=
  pow_twelve_le_two_pow_joint (x := 1729) (k := 11) (e := 624) (by norm_num) (by norm_num)

theorem two_pow_le_two_pow {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by norm_num) h

theorem two_le_two_pow_two_pow (k : ℕ) : 2 ≤ 2 ^ (2 ^ k) :=
  Nat.le_self_pow (by positivity) 2

theorem natLog_lt_of_lt_two_pow {E n : ℕ} (hn2 : 2 ≤ n) (hn : n < 2 ^ E) :
    Nat.log 2 n < E :=
  (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr hn

/-- The a priori bound `K₁ n (log₂ n)³` below `2^E` is `B n log n`. -/
theorem base_of_polylog (M : ℕ → ℕ) (K₁ E : ℕ)
    (hbase : ∀ n, 2 ≤ n → n < 2 ^ E → M n ≤ K₁ * n * (Nat.log 2 n) ^ 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, 2 ≤ n → n < 2 ^ E → (M n : ℝ) ≤ B * n * Real.log n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K₁ * (E : ℝ) ^ 2 / Real.log 2, by positivity, fun n hn2 hn => ?_⟩
  have hlog := natLog_lt_of_lt_two_pow hn2 hn
  have h3 : (Nat.log 2 n) ^ 3 ≤ E ^ 2 * Nat.log 2 n := by
    have h2 : (Nat.log 2 n) ^ 2 ≤ E ^ 2 := Nat.pow_le_pow_left hlog.le 2
    calc (Nat.log 2 n) ^ 3 = (Nat.log 2 n) ^ 2 * Nat.log 2 n := by ring
      _ ≤ E ^ 2 * Nat.log 2 n := Nat.mul_le_mul_right _ h2
  have hM : M n ≤ K₁ * E ^ 2 * n * Nat.log 2 n := by
    calc M n ≤ K₁ * n * (Nat.log 2 n) ^ 3 := hbase n hn2 hn
      _ ≤ K₁ * n * (E ^ 2 * Nat.log 2 n) := Nat.mul_le_mul_left _ h3
      _ = K₁ * E ^ 2 * n * Nat.log 2 n := by ring
  have hM' : (M n : ℝ) ≤ K₁ * (E : ℝ) ^ 2 * n * (Nat.log 2 n : ℝ) := by
    exact_mod_cast hM
  have hL : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hl2]; exact natLog_mul_log_two_le (by omega)
  have hnn : (0 : ℝ) ≤ K₁ * (E : ℝ) ^ 2 * n := by positivity
  calc (M n : ℝ) ≤ K₁ * (E : ℝ) ^ 2 * n * (Nat.log 2 n : ℝ) := hM'
    _ ≤ K₁ * (E : ℝ) ^ 2 * n * (Real.log n / Real.log 2) :=
        mul_le_mul_of_nonneg_left hL hnn
    _ = K₁ * (E : ℝ) ^ 2 / Real.log 2 * n * Real.log n := by ring

/-! ### The joint recurrence -/

/-- Any cost `M` that, above `2^(2^624)`, is at most one full recursive step
(three pipelines with the delegated products costed by `M`, plus the
resampling maps with the paper's windows, their weights costing at most
`K₀ q (log₂ q)⁴` and their small products at most `K₁ q (log₂ q)³`) plus a
linear overhead, and that is at most `K₁ n (log₂ n)³` below the threshold, is
`O(n log n)`. No hypothesis involves `M` on the resampling side. -/
theorem joint_cost_nlogn (M Msmall Ecost : ℕ → ℕ) (K₀ K₁ C : ℕ)
    (s t : ℕ → Fin 1729 → ℕ)
    (ht : ∀ n i, 0 < t n i) (hst : ∀ n i, s n i ≤ t n i)
    (hT : ∀ n, ∏ j, t n j = transformSize n)
    (hE : ∀ q, 2 ≤ q → Ecost q ≤ K₀ * q * (Nat.log 2 q) ^ 4)
    (hM₀ : ∀ q, 2 ≤ q → Msmall q ≤ K₁ * q * (Nat.log 2 q) ^ 3)
    (hM : ∀ n, 2 ^ (2 ^ 624) ≤ n →
      M n ≤ stepOps₂ (rootSize 1729 n) (precision n) (modelExponents 1729 n) (s n) (t n)
        (paperWindowA (precision n) (alphaParam 1729 n))
        (paperWindowE (precision n) (alphaParam 1729 n)) (paperIter (alphaParam 1729 n))
        Ecost Msmall M + C * n)
    (hbase : ∀ n, 2 ≤ n → n < 2 ^ (2 ^ 624) → M n ≤ K₁ * n * (Nat.log 2 n) ^ 3) :
    ∃ D : ℝ, ∀ n, 2 ≤ n → (M n : ℝ) ≤ D * n * Real.log n := by
  have hd : 2 ≤ 1729 := by norm_num
  have hge : 2 ^ (1729 ^ 12) ≤ 2 ^ (2 ^ 624) := two_pow_le_two_pow paper_exp_le
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 30 * (K₀ + K₁ + 2) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ((2880 + 4320 * K * 1729 + C : ℕ) : ℝ) / Real.log 2 :=
    ⟨_, rfl⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 ≤ A := by rw [hA]; exact div_nonneg (Nat.cast_nonneg _) hl2.le
  have hM0 : ∀ n, (0 : ℝ) ≤ (M n : ℝ) := fun n => Nat.cast_nonneg _
  have hparams : ∀ n, 2 ^ (2 ^ 624) ≤ n →
      (transformSize n : ℝ) * precision n ≤ 48 * n ∧
        2 ≤ 3 * rootSize 1729 n * precision n ∧ 3 * rootSize 1729 n * precision n < n ∧
        0 < rootSize 1729 n ∧
        Real.log (3 * (rootSize 1729 n : ℝ) * precision n) ≤
          (1 / (1729 : ℝ) + 1 / (2 * (1729 : ℝ) ^ 2)) * Real.log n :=
    fun n hn => recurrence_params (le_trans hge hn)
  have hbase' := base_of_polylog M K₁ (2 ^ 624) hbase
  have hrec : ∀ n, 2 ^ (2 ^ 624) ≤ n →
      (M n : ℝ) ≤ 12 * (transformSize n : ℝ) / rootSize 1729 n *
        (M (3 * rootSize 1729 n * precision n) : ℝ) + A * n * Real.log n := by
    intro n hn
    have hn' : 2 ^ (1729 ^ 12) ≤ n := le_trans hge hn
    have hb : 2 ^ 624 ≤ chunkSize n := chunkSize_ge_of_pow_le hn
    have hp2 : 2 ≤ precision n := le_trans (by norm_num) (precision_ge hd hn')
    have hrow := row_threshold hd hn' hb Ecost Msmall K₀ K₁ (hE _ hp2) (hM₀ _ hp2)
    rw [← hK] at hrow
    have h := le_trans (hM n hn)
      (Nat.add_le_add_right (stepOps₂_params_le hn' (s n) (t n) (ht n) (hst n) (hT n)
        Ecost Msmall M K hrow) _)
    have h2 := step_cost_rec_real hn' M (2880 + 4320 * K * 1729) C h
    rw [hA]
    push_cast at h2 ⊢
    exact h2
  exact main_bound (T := transformSize) (r := rootSize 1729) (p := precision)
    (n₀ := 2 ^ (2 ^ 624)) (M := fun n => (M n : ℝ)) hA0 (two_le_two_pow_two_pow 624) hM0
    hparams hrec hbase'

end IntegerMultBounds.NLogN
