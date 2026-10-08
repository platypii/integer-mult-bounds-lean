import IntegerMultBounds.NLogN.CostBound
import IntegerMultBounds.NLogN.ExplicitNumeric

/-! An operation-count model for the numerical resampling maps of Section 4 of
Harvey–van der Hoeven (Theorem 4.1's cost `O(d T p^{3/2+δ} α + T p log T)`),
mirroring the structure of the explicit maps in `ExplicitNumeric`, and the
resulting cost shape of one recursive step.

Three kinds of operations are counted: an evaluation of a Gaussian weight to
`p` bits (the paper's Lemma 2.13, cost `Ecost p`), a fixed-point product of
`p`-bit numbers (cost `Mcost p`), and an addition, rounding, or data move of a
`p`-bit word (cost `p`). `resampAOps` counts `resampANum`: `2 mA + 1` terms per
output row, each one weight, one product, and two word operations.
`offDiagOps` counts `offDiagNum` with `2 mE` terms per row; `jOps` counts
`nJ` Horner steps of the Neumann inverse, each one application of the
off-diagonal map plus a subtraction and a rounding per entry (the explicit
`resampJNumC` uses `nJ = p`; the paper's Lemma 4.12 uses
`nJ = ⌈p/(α²θ)⌉ ≤ α² + 1`, which the sharper tail bound `‖E‖ ≤ 2^{−α²θ}`
permits); `diagOps` counts `diagDNum`; `resampBOps` adds the permutations,
row selection, and scaling as data moves. The tensors apply each
one-dimensional map to at most `T / t_i` slices (`tensorZR`).

Proved: closed-form bounds `d T (2 mA + 1) c`, `d T (nJ (2 mE c + 2p) + c + 4p)`
with `c` the per-term cost, the resampling part of a step bounded by
`30 d T ((mA + 1) + (nJ + 1)(mE + 1)) c`; with the paper's windows
`mA = (√p + 1) α`, `mE = √p/(2α) + 1`, `nJ = α² + 1` this is
`270 d T α (√p + 1) c`, the paper's `d T p^{1/2} α · p^{1+δ}`; the growth
bound `α³ ≤ b` for `b ≥ 2^46`; and, whenever the per-row cost
`α (√p + 1) c` is at most `K b²` (the paper's `p^{3/2+δ} α = O(p²)`), the
resampling part of a step is at most `4320 K d n log₂ n`, so a cost bounded by
the full step plus a linear overhead is `O(n log n)`; that per-row condition
follows from `Ecost p + Mcost p ≤ K₀ p log₂ p` once `b` exceeds an explicit
threshold.

Not modelled: tape steps, data rearrangement, and the bit cost of the weight
evaluations themselves (the parameter `Ecost`). -/

namespace IntegerMultBounds.NLogN

/-! ### One-dimensional counts -/

/-- Cost of one term of a truncated resampling sum: one weight evaluation, one
product, two word operations. -/
def termOps (p : ℕ) (Ecost Mcost : ℕ → ℕ) : ℕ := Ecost p + Mcost p + 2 * p

/-- `resampANum` on a length-`t` output: `2 mA + 1` terms per row. -/
def resampAOps (t mA p : ℕ) (Ecost Mcost : ℕ → ℕ) : ℕ :=
  t * (2 * mA + 1) * termOps p Ecost Mcost

/-- `offDiagNum` on a length-`s` vector: `2 mE` terms per row. -/
def offDiagOps (s mE p : ℕ) (Ecost Mcost : ℕ → ℕ) : ℕ :=
  s * (2 * mE) * termOps p Ecost Mcost

/-- `nJ` Horner steps of the Neumann inverse: one off-diagonal application
and one subtraction with rounding per entry. -/
def jOps (s mE p nJ : ℕ) (Ecost Mcost : ℕ → ℕ) : ℕ :=
  nJ * (offDiagOps s mE p Ecost Mcost + 2 * s * p)

/-- `diagDNum`: one weight, one product, two roundings per entry. -/
def diagOps (s p : ℕ) (Ecost Mcost : ℕ → ℕ) : ℕ := s * termOps p Ecost Mcost

/-- `resampBNumC`: the permutation `P_t`, the row selection, the inverse, the
diagonal, the inverse permutation and the scaling, the data moves on a
length-`t` vector. -/
def resampBOps (s t mE p nJ : ℕ) (Ecost Mcost : ℕ → ℕ) : ℕ :=
  jOps s mE p nJ Ecost Mcost + diagOps s p Ecost Mcost + 4 * t * p

/-! ### Tensors -/

/-- Coordinate `i` applies its one-dimensional map to `(∏ len) / len i`
slices. -/
def tensorOps {d : ℕ} (len : Fin d → ℕ) (opsAt : Fin d → ℕ) : ℕ :=
  ∑ i, (∏ j, len j) / len i * opsAt i

/-- Operations of `⊗ Ã_i` from the `s`-grid to the `t`-grid, counted with the
upper bound `T / t_i` on the number of slices of coordinate `i` (the mixed
shapes have at most that many since `s_j ≤ t_j`). -/
def resampAOpsD {d : ℕ} (t : Fin d → ℕ) (mA p : ℕ) (Ecost Mcost : ℕ → ℕ) : ℕ :=
  tensorOps t fun i => resampAOps (t i) mA p Ecost Mcost

/-- Operations of `⊗ B̃_i` from the `t`-grid to the `s`-grid, with the same
slice bound. -/
def resampBOpsD {d : ℕ} (s t : Fin d → ℕ) (mE p nJ : ℕ) (Ecost Mcost : ℕ → ℕ) : ℕ :=
  tensorOps t fun i => resampBOps (s i) (t i) mE p nJ Ecost Mcost

/-- The resampling part of one recursive step: three transforms of the prime
grid (Proposition 5.3), each one `Ã`, one `B̃`, one chirp/rounding pass on the
`t`-grid, and one `2^γ` scaling on the `s`-grid, plus the final rounding. -/
def resampPart {d : ℕ} (s t : Fin d → ℕ) (mA mE p nJ : ℕ) (Ecost Mcost : ℕ → ℕ) : ℕ :=
  3 * (resampAOpsD t mA p Ecost Mcost + resampBOpsD s t mE p nJ Ecost Mcost +
    (∏ i, t i) * termOps p Ecost Mcost + (∏ i, s i) * p) + (∏ i, s i) * (2 * p)

/-- One recursive step: three synthetic convolution pipelines on the
power-of-two grid plus the resampling part. -/
def stepOps {d k : ℕ} (r p : ℕ) (e : Fin k → ℕ) (s t : Fin d → ℕ) (mA mE nJ : ℕ)
    (Ecost Mcost : ℕ → ℕ) : ℕ :=
  3 * pipelineOps r p e Mcost + resampPart s t mA mE p nJ Ecost Mcost

/-! ### Closed-form bounds -/

theorem two_mul_le_termOps (p : ℕ) (Ecost Mcost : ℕ → ℕ) :
    2 * p ≤ termOps p Ecost Mcost := by
  unfold termOps; omega

theorem tensorOps_le {d : ℕ} (len : Fin d → ℕ) (opsAt : Fin d → ℕ) (c : ℕ)
    (hlen : ∀ i, 0 < len i) (hops : ∀ i, opsAt i ≤ len i * c) :
    tensorOps len opsAt ≤ d * (∏ j, len j) * c := by
  unfold tensorOps
  calc ∑ i, (∏ j, len j) / len i * opsAt i
      ≤ ∑ i : Fin d, (∏ j, len j) * c := by
        apply Finset.sum_le_sum
        intro i _
        obtain ⟨q, hq⟩ : len i ∣ ∏ j, len j := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
        rw [hq, Nat.mul_div_cancel_left _ (hlen i)]
        calc q * opsAt i ≤ q * (len i * c) := Nat.mul_le_mul_left _ (hops i)
          _ = len i * q * c := by ring
    _ = d * (∏ j, len j) * c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp [smul_eq_mul, mul_assoc]

theorem resampAOpsD_le {d : ℕ} (t : Fin d → ℕ) (mA p : ℕ) (Ecost Mcost : ℕ → ℕ)
    (ht : ∀ i, 0 < t i) :
    resampAOpsD t mA p Ecost Mcost ≤
      d * (∏ j, t j) * ((2 * mA + 1) * termOps p Ecost Mcost) := by
  apply tensorOps_le _ _ _ ht
  intro i
  unfold resampAOps
  rw [mul_assoc]

theorem resampBOpsD_le {d : ℕ} (s t : Fin d → ℕ) (mE p nJ : ℕ) (Ecost Mcost : ℕ → ℕ)
    (ht : ∀ i, 0 < t i) (hst : ∀ i, s i ≤ t i) :
    resampBOpsD s t mE p nJ Ecost Mcost ≤
      d * (∏ j, t j) *
        (nJ * (2 * mE * termOps p Ecost Mcost + 2 * p) + termOps p Ecost Mcost + 4 * p) := by
  apply tensorOps_le _ _ _ ht
  intro i
  unfold resampBOps jOps offDiagOps diagOps
  have h := hst i
  set c := termOps p Ecost Mcost
  calc nJ * (s i * (2 * mE) * c + 2 * s i * p) + s i * c + 4 * t i * p
      = s i * (nJ * (2 * mE * c + 2 * p) + c) + t i * (4 * p) := by ring
    _ ≤ t i * (nJ * (2 * mE * c + 2 * p) + c) + t i * (4 * p) :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _
    _ = t i * (nJ * (2 * mE * c + 2 * p) + c + 4 * p) := by ring

/-- The resampling part of a step is at most
`30 d T ((mA + 1) + (nJ + 1)(mE + 1)) · c`. -/
theorem resampPart_le {d : ℕ} (s t : Fin d → ℕ) (mA mE p nJ : ℕ) (Ecost Mcost : ℕ → ℕ)
    (hd : 1 ≤ d) (ht : ∀ i, 0 < t i) (hst : ∀ i, s i ≤ t i) :
    resampPart s t mA mE p nJ Ecost Mcost ≤
      30 * d * (∏ j, t j) * ((mA + 1) + (nJ + 1) * (mE + 1)) * termOps p Ecost Mcost := by
  have hA := resampAOpsD_le t mA p Ecost Mcost ht
  have hB := resampBOpsD_le s t mE p nJ Ecost Mcost ht hst
  have hS : ∏ i, s i ≤ ∏ i, t i := Finset.prod_le_prod fun i _ => hst i
  have hc := two_mul_le_termOps p Ecost Mcost
  unfold resampPart
  set c := termOps p Ecost Mcost
  set T := ∏ j, t j
  set S := ∏ j, s j
  have hdT : T ≤ d * T := Nat.le_mul_of_pos_left _ hd
  -- each of the six pieces against its share of the budget
  have h1 : 3 * (d * T * ((2 * mA + 1) * c)) ≤ 6 * (d * T) * (mA + 1) * c := by
    nlinarith [Nat.zero_le (d * T * c)]
  have h2 : 3 * (d * T * (nJ * (2 * mE * c + 2 * p) + c + 4 * p)) ≤
      6 * (d * T) * (nJ + 1) * (mE + 1) * c + 3 * (d * T) * c + 6 * (d * T) * c := by
    have : nJ * (2 * mE * c + 2 * p) ≤ nJ * (2 * mE * c + c) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4p : 4 * p ≤ 2 * c := by omega
    nlinarith [Nat.zero_le (d * T), Nat.zero_le (d * T * nJ * c),
      Nat.mul_le_mul_left (d * T) this, Nat.mul_le_mul_left (d * T) h4p]
  have h3 : 3 * (T * c) ≤ 3 * (d * T) * c := by nlinarith
  have h4 : 3 * (S * p) + S * (2 * p) ≤ 3 * (d * T) * c := by nlinarith
  calc 3 * (resampAOpsD t mA p Ecost Mcost + resampBOpsD s t mE p nJ Ecost Mcost +
        T * c + S * p) + S * (2 * p)
      ≤ 3 * (d * T * ((2 * mA + 1) * c)) +
          3 * (d * T * (nJ * (2 * mE * c + 2 * p) + c + 4 * p)) +
          3 * (T * c) + (3 * (S * p) + S * (2 * p)) := by
        nlinarith [hA, hB]
    _ ≤ 6 * (d * T) * (mA + 1) * c +
          (6 * (d * T) * (nJ + 1) * (mE + 1) * c + 3 * (d * T) * c + 6 * (d * T) * c) +
          3 * (d * T) * c + 3 * (d * T) * c := by
        omega
    _ ≤ 30 * d * T * ((mA + 1) + (nJ + 1) * (mE + 1)) * c := by
        nlinarith [Nat.zero_le (d * T * c), Nat.zero_le (d * T * (mA + 1) * c),
          Nat.zero_le (d * T * (nJ + 1) * (mE + 1) * c)]

theorem stepOps_le {d k : ℕ} (r p : ℕ) (e : Fin k → ℕ) (s t : Fin d → ℕ) (mA mE nJ : ℕ)
    (Ecost Mcost : ℕ → ℕ) (hd : 1 ≤ d) (ht : ∀ i, 0 < t i) (hst : ∀ i, s i ≤ t i) :
    stepOps r p e s t mA mE nJ Ecost Mcost ≤
      3 * pipelineOps r p e Mcost +
        30 * d * (∏ j, t j) * ((mA + 1) + (nJ + 1) * (mE + 1)) * termOps p Ecost Mcost :=
  Nat.add_le_add_left (resampPart_le s t mA mE p nJ Ecost Mcost hd ht hst) _

/-! ### The paper's windows -/

/-- Lemma 4.9's window `m = ⌈√p⌉ α`. -/
def paperWindowA (p α : ℕ) : ℕ := (Nat.sqrt p + 1) * α

/-- Lemma 4.11's window `m = ⌈√p / (2α)⌉`. -/
def paperWindowE (p α : ℕ) : ℕ := Nat.sqrt p / (2 * α) + 1

/-- Lemma 4.12's iteration count `n ≤ α² + 1`. -/
def paperIter (α : ℕ) : ℕ := α ^ 2 + 1

theorem paper_windows_sum_le (p α : ℕ) (hα : 1 ≤ α) (hαp : α ≤ Nat.sqrt p) :
    (paperWindowA p α + 1) + (paperIter α + 1) * (paperWindowE p α + 1) ≤
      9 * α * (Nat.sqrt p + 1) := by
  unfold paperWindowA paperIter paperWindowE
  set q := Nat.sqrt p / (2 * α)
  set m := Nat.sqrt p
  have hq : 2 * α * q ≤ m := Nat.mul_div_le m (2 * α)
  have hq' : α * (2 * α * q) ≤ α * m := Nat.mul_le_mul_left α hq
  have hα2 : α ^ 2 ≤ α * m := by nlinarith
  have hq2 : q ≤ m := by nlinarith
  nlinarith

/-- With the paper's windows the resampling part is `270 d T α (√p + 1) c`. -/
theorem resampPart_paper_le {d : ℕ} (s t : Fin d → ℕ) (p α : ℕ) (Ecost Mcost : ℕ → ℕ)
    (hd : 1 ≤ d) (ht : ∀ i, 0 < t i) (hst : ∀ i, s i ≤ t i) (hα : 1 ≤ α)
    (hαp : α ≤ Nat.sqrt p) :
    resampPart s t (paperWindowA p α) (paperWindowE p α) p (paperIter α) Ecost Mcost ≤
      270 * d * (∏ j, t j) * (α * (Nat.sqrt p + 1)) * termOps p Ecost Mcost := by
  calc resampPart s t (paperWindowA p α) (paperWindowE p α) p (paperIter α) Ecost Mcost
      ≤ 30 * d * (∏ j, t j) *
          ((paperWindowA p α + 1) + (paperIter α + 1) * (paperWindowE p α + 1)) *
          termOps p Ecost Mcost := resampPart_le s t _ _ p _ Ecost Mcost hd ht hst
    _ ≤ 30 * d * (∏ j, t j) * (9 * α * (Nat.sqrt p + 1)) * termOps p Ecost Mcost := by
        gcongr
        exact paper_windows_sum_le p α hα hαp
    _ = 270 * d * (∏ j, t j) * (α * (Nat.sqrt p + 1)) * termOps p Ecost Mcost := by ring

/-- The explicit numerics of `ExplicitNumeric` use `m = p` everywhere and `p`
Horner steps; their count is `60 d T (p + 1)² c`, quadratic in `p` and hence
not `O(n log n)`: the paper's windows are needed for the cost, the explicit
`m = p` only for the simplest correctness proof. -/
theorem resampPart_explicit_le {d : ℕ} (s t : Fin d → ℕ) (p : ℕ) (Ecost Mcost : ℕ → ℕ)
    (hd : 1 ≤ d) (ht : ∀ i, 0 < t i) (hst : ∀ i, s i ≤ t i) :
    resampPart s t p p p p Ecost Mcost ≤
      60 * d * (∏ j, t j) * (p + 1) ^ 2 * termOps p Ecost Mcost := by
  calc resampPart s t p p p p Ecost Mcost
      ≤ 30 * d * (∏ j, t j) * ((p + 1) + (p + 1) * (p + 1)) * termOps p Ecost Mcost :=
        resampPart_le s t p p p p Ecost Mcost hd ht hst
    _ ≤ 30 * d * (∏ j, t j) * (2 * (p + 1) ^ 2) * termOps p Ecost Mcost := by
        gcongr
        nlinarith
    _ = 60 * d * (∏ j, t j) * (p + 1) ^ 2 * termOps p Ecost Mcost := by ring

/-! ### Growth of `α` -/

/-- `α^24 ≤ 2^24 · 12^6 · b^7`, from `(α − 1)^4 < 12 d² b` and `d^12 ≤ b`. -/
theorem alphaParam_pow_24_le {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    alphaParam d n ^ 24 ≤ 2 ^ 24 * 12 ^ 6 * chunkSize n ^ 7 := by
  have hb := chunkSize_ge_4096 hd hn
  have hd12 := chunkSize_ge hn
  have hα := alphaParam_ge_two (d := d) (n := n) (by omega) (by omega)
  have hlt := alphaParam_pred_pow_lt (d := d) (n := n) (by positivity)
  set a := alphaParam d n
  set b := chunkSize n
  have h1 : a ≤ 2 * (a - 1) := by omega
  have h2 : a ^ 24 ≤ (2 * (a - 1)) ^ 24 := Nat.pow_le_pow_left h1 24
  have h3 : (2 * (a - 1)) ^ 24 = 2 ^ 24 * ((a - 1) ^ 4) ^ 6 := by ring
  have h4 : ((a - 1) ^ 4) ^ 6 ≤ (12 * d ^ 2 * b) ^ 6 := Nat.pow_le_pow_left hlt.le 6
  have h5 : (12 * d ^ 2 * b) ^ 6 = 12 ^ 6 * d ^ 12 * b ^ 6 := by ring
  have h6 : 12 ^ 6 * d ^ 12 * b ^ 6 ≤ 12 ^ 6 * b * b ^ 6 := by gcongr
  calc a ^ 24 ≤ 2 ^ 24 * ((a - 1) ^ 4) ^ 6 := by rw [← h3]; exact h2
    _ ≤ 2 ^ 24 * (12 ^ 6 * b * b ^ 6) := by rw [h5] at h4; gcongr; exact le_trans h4 h6
    _ = 2 ^ 24 * 12 ^ 6 * b ^ 7 := by ring

/-- `α³ ≤ b` once `b ≥ 2^46`. -/
theorem alphaParam_cube_le {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n)
    (hb : 2 ^ 46 ≤ chunkSize n) : alphaParam d n ^ 3 ≤ chunkSize n := by
  have h := alphaParam_pow_24_le hd hn
  set a := alphaParam d n
  set b := chunkSize n
  have hc : 2 ^ 24 * 12 ^ 6 ≤ 2 ^ 46 := by norm_num
  have h8 : (a ^ 3) ^ 8 ≤ b ^ 8 := by
    calc (a ^ 3) ^ 8 = a ^ 24 := by ring
      _ ≤ 2 ^ 24 * 12 ^ 6 * b ^ 7 := h
      _ ≤ 2 ^ 46 * b ^ 7 := Nat.mul_le_mul_right _ hc
      _ ≤ b * b ^ 7 := Nat.mul_le_mul_right _ hb
      _ = b ^ 8 := by ring
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h8

/-- `α ≤ √p` for the paper's parameters (so the window lemma applies). -/
theorem alphaParam_le_sqrt_precision {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    alphaParam d n ≤ Nat.sqrt (precision n) :=
  Nat.le_sqrt.mpr (by
    have := alphaParam_sq_lt_precision hd hn
    nlinarith)

/-! ### The per-row cost condition -/

/-- If weight evaluation and multiplication are quasilinear,
`Ecost p + Mcost p ≤ K₀ p log₂ p`, then the per-row resampling cost
`α (√p + 1) (Ecost p + Mcost p + 2p)` is at most `K b²` as soon as `b` has a
cube root `c` with `864 (K₀ log₂ p + 2)² ≤ K² c` and `b ≥ 2^46`. -/
theorem row_cost_of_quasilinear {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n)
    (hb : 2 ^ 46 ≤ chunkSize n) (Ecost Mcost : ℕ → ℕ) (K₀ K c : ℕ)
    (hE : Ecost (precision n) + Mcost (precision n) ≤
      K₀ * precision n * Nat.log 2 (precision n))
    (hc : c ^ 3 ≤ chunkSize n)
    (hL : 864 * (K₀ * Nat.log 2 (precision n) + 2) ^ 2 ≤ K ^ 2 * c) :
    alphaParam d n * (Nat.sqrt (precision n) + 1) * termOps (precision n) Ecost Mcost ≤
      K * chunkSize n ^ 2 := by
  have hα3 := alphaParam_cube_le hd hn hb
  have hp : precision n = 6 * chunkSize n := rfl
  set a := alphaParam d n
  set b := chunkSize n
  set p := precision n
  set L := K₀ * Nat.log 2 p + 2
  have hterm : termOps p Ecost Mcost ≤ p * L := by
    unfold termOps
    calc Ecost p + Mcost p + 2 * p ≤ K₀ * p * Nat.log 2 p + 2 * p := by omega
      _ = p * L := by ring
  -- `α² c ≤ b` from `α³ ≤ b` and `c³ ≤ b`
  have hac : a ^ 2 * c ≤ b := by
    have : (a ^ 2 * c) ^ 3 ≤ b ^ 3 := by
      calc (a ^ 2 * c) ^ 3 = (a ^ 3) ^ 2 * c ^ 3 := by ring
        _ ≤ b ^ 2 * b := Nat.mul_le_mul (Nat.pow_le_pow_left hα3 2) hc
        _ = b ^ 3 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
  -- `(√p + 1)² ≤ 4p`
  have hsq : (Nat.sqrt p + 1) ^ 2 ≤ 4 * p := by
    have h1 : Nat.sqrt p ^ 2 ≤ p := Nat.sqrt_le' p
    have h2 : Nat.sqrt p ≤ p := Nat.sqrt_le_self p
    have hp1 : 1 ≤ p := by rw [hp]; omega
    nlinarith
  -- `(6 α (√p + 1) L)² ≤ (K b)²`
  have hmain : (6 * (a * (Nat.sqrt p + 1) * L)) ^ 2 ≤ (K * b) ^ 2 := by
    have h864 : 864 * (a ^ 2 * L ^ 2) ≤ K ^ 2 * (a ^ 2 * c) := by
      calc 864 * (a ^ 2 * L ^ 2) = a ^ 2 * (864 * L ^ 2) := by ring
        _ ≤ a ^ 2 * (K ^ 2 * c) := Nat.mul_le_mul_left _ hL
        _ = K ^ 2 * (a ^ 2 * c) := by ring
    calc (6 * (a * (Nat.sqrt p + 1) * L)) ^ 2
        = 36 * a ^ 2 * (Nat.sqrt p + 1) ^ 2 * L ^ 2 := by ring
      _ ≤ 36 * a ^ 2 * (4 * p) * L ^ 2 := by gcongr
      _ = b * (864 * (a ^ 2 * L ^ 2)) := by rw [hp]; ring
      _ ≤ b * (K ^ 2 * (a ^ 2 * c)) := Nat.mul_le_mul_left _ h864
      _ ≤ b * (K ^ 2 * b) := by gcongr
      _ = (K * b) ^ 2 := by ring
  have hroot : 6 * (a * (Nat.sqrt p + 1) * L) ≤ K * b :=
    (Nat.pow_le_pow_iff_left (by norm_num)).mp hmain
  calc a * (Nat.sqrt p + 1) * termOps p Ecost Mcost
      ≤ a * (Nat.sqrt p + 1) * (p * L) := Nat.mul_le_mul_left _ hterm
    _ = (6 * (a * (Nat.sqrt p + 1) * L)) * b := by rw [hp]; ring
    _ ≤ (K * b) * b := Nat.mul_le_mul_right _ hroot
    _ = K * b ^ 2 := by ring

/-! ### The step with the Section 5 parameters -/

/-- With the paper's windows and parameters, the resampling part of a step is
at most `4320 K d n log₂ n` whenever the per-row cost `α (√p + 1) c` is at most
`K b²`. -/
theorem resampPart_nlogn {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) (s t : Fin d → ℕ)
    (ht : ∀ i, 0 < t i) (hst : ∀ i, s i ≤ t i) (hT : ∏ j, t j = transformSize n)
    (Ecost Mcost : ℕ → ℕ) (K : ℕ)
    (hrow : alphaParam d n * (Nat.sqrt (precision n) + 1) *
      termOps (precision n) Ecost Mcost ≤ K * chunkSize n ^ 2) :
    resampPart s t (paperWindowA (precision n) (alphaParam d n))
        (paperWindowE (precision n) (alphaParam d n)) (precision n) (paperIter (alphaParam d n))
        Ecost Mcost ≤
      4320 * K * d * n * Nat.log 2 n := by
  have hb := chunkSize_ge_4096 hd hn
  have hn2 : 2 ≤ n := le_trans (two_le_two_pow_pow (d := d) (by omega)) hn
  have hα1 : 1 ≤ alphaParam d n := le_trans (by norm_num) (alphaParam_ge_two (by omega) (by omega))
  have hαp := alphaParam_le_sqrt_precision hd hn
  have hTb : transformSize n * chunkSize n < 8 * n := (transformSize_bounds hn2).2
  have hlog : chunkSize n ≤ 2 * Nat.log 2 n := by
    have h1 := chunkSize_le_log_succ n
    have h2 : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) hn2
    omega
  have h := resampPart_paper_le s t (precision n) (alphaParam d n) Ecost Mcost (by omega) ht hst
    hα1 hαp
  rw [hT] at h
  calc _ ≤ 270 * d * transformSize n * (alphaParam d n * (Nat.sqrt (precision n) + 1)) *
        termOps (precision n) Ecost Mcost := h
    _ = 270 * d * transformSize n *
        (alphaParam d n * (Nat.sqrt (precision n) + 1) * termOps (precision n) Ecost Mcost) := by
        ring
    _ ≤ 270 * d * transformSize n * (K * chunkSize n ^ 2) := Nat.mul_le_mul_left _ hrow
    _ = 270 * K * d * (transformSize n * chunkSize n) * chunkSize n := by ring
    _ ≤ 270 * K * d * (8 * n) * chunkSize n := by gcongr
    _ ≤ 270 * K * d * (8 * n) * (2 * Nat.log 2 n) := by gcongr
    _ = 4320 * K * d * n * Nat.log 2 n := by ring

/-- One full recursive step at `d = 1729`: `(12 T / r) M(3rp) + O(n log n)`. -/
theorem stepOps_params_le {n : ℕ} (hn : 2 ^ (1729 ^ 12) ≤ n) (s t : Fin 1729 → ℕ)
    (ht : ∀ i, 0 < t i) (hst : ∀ i, s i ≤ t i) (hT : ∏ j, t j = transformSize n)
    (Ecost Mcost : ℕ → ℕ) (K : ℕ)
    (hrow : alphaParam 1729 n * (Nat.sqrt (precision n) + 1) *
      termOps (precision n) Ecost Mcost ≤ K * chunkSize n ^ 2) :
    stepOps (rootSize 1729 n) (precision n) (modelExponents 1729 n) s t
        (paperWindowA (precision n) (alphaParam 1729 n))
        (paperWindowE (precision n) (alphaParam 1729 n)) (paperIter (alphaParam 1729 n))
        Ecost Mcost ≤
      (12 * transformSize n / rootSize 1729 n) * Mcost (3 * rootSize 1729 n * precision n) +
        (2880 + 4320 * K * 1729) * n * Nat.log 2 n := by
  have hd : 2 ≤ 1729 := by norm_num
  have hpipe := main_ops_le' hd hn (modelExponents 1729 n) (modelExponents_prod hd hn) Mcost
  have hres := resampPart_nlogn hd hn s t ht hst hT Ecost Mcost K hrow
  clear hn hrow
  unfold stepOps
  have : (2880 + 4320 * K * 1729) * n * Nat.log 2 n =
      2880 * n * Nat.log 2 n + 4320 * K * 1729 * n * Nat.log 2 n := by ring
  rw [this]
  omega

/-- The real-valued recursive inequality for a cost bounded by one full step
plus a linear overhead. -/
theorem step_cost_rec_real {n : ℕ} (hn : 2 ^ (1729 ^ 12) ≤ n) (M : ℕ → ℕ) (C₁ C₂ : ℕ)
    (hM : M n ≤ (12 * transformSize n / rootSize 1729 n) *
      M (3 * rootSize 1729 n * precision n) + C₁ * n * Nat.log 2 n + C₂ * n) :
    (M n : ℝ) ≤ 12 * (transformSize n : ℝ) / rootSize 1729 n *
      (M (3 * rootSize 1729 n * precision n) : ℝ) +
      ((C₁ + C₂) / Real.log 2) * n * Real.log n := by
  have hd : 2 ≤ 1729 := by norm_num
  have hT := modelExponents_prod hd hn
  have hn2 : 2 ≤ n := le_trans (two_le_two_pow_pow (d := 1729) (by norm_num)) hn
  set P : ℕ := ∏ i : Fin (1729 - 1), 2 ^ modelExponents 1729 n i with hP
  clear_value P
  have hr : 0 < rootSize 1729 n := rootSize_pos 1729 n
  have hdiv : 12 * transformSize n / rootSize 1729 n = 12 * P := by
    rw [← hT, show 12 * (rootSize 1729 n * P) = rootSize 1729 n * (12 * P) by ring]
    exact Nat.mul_div_cancel_left _ hr
  rw [hdiv] at hM
  clear hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  have hr' : (0 : ℝ) < rootSize 1729 n := by exact_mod_cast hr
  have hTP : 12 * (transformSize n : ℝ) / rootSize 1729 n = 12 * (P : ℝ) := by
    rw [div_eq_iff hr'.ne', ← hT]
    push_cast
    ring
  rw [hTP]
  have hnat : (M n : ℝ) ≤ 12 * (P : ℝ) * (M (3 * rootSize 1729 n * precision n) : ℝ) +
      C₁ * n * (Nat.log 2 n : ℝ) + C₂ * n := by
    exact_mod_cast hM
  clear hM hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := natLog_mul_log_two_le hn1
  have hln : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hL : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hl2]; exact hlog
  have h1 : (1 : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hl2, one_mul]; exact hln
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hC₁ : (0 : ℝ) ≤ C₁ := Nat.cast_nonneg C₁
  have hC₂ : (0 : ℝ) ≤ C₂ := Nat.cast_nonneg C₂
  have hsplit : ((C₁ : ℝ) + C₂) / Real.log 2 * n * Real.log n =
      C₁ * n * (Real.log n / Real.log 2) + C₂ * n * (Real.log n / Real.log 2) := by
    field_simp
  rw [hsplit]
  have h2 : (C₁ : ℝ) * n * (Nat.log 2 n : ℝ) ≤ C₁ * n * (Real.log n / Real.log 2) :=
    mul_le_mul_of_nonneg_left hL (mul_nonneg hC₁ hnn)
  have h3 : (C₂ : ℝ) * n ≤ C₂ * n * (Real.log n / Real.log 2) := by
    calc (C₂ : ℝ) * n = C₂ * n * 1 := by ring
      _ ≤ C₂ * n * (Real.log n / Real.log 2) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hC₂ hnn)
  linarith

/-- Any cost bounded above `2^(1729^12)` by one full recursive step (three
pipelines plus the resampling maps with the paper's windows) plus a linear
overhead, with the per-row resampling cost at most `K b²`, and by `B n log n`
below, is `O(n log n)`. The grids `s n`, `t n` may depend on `n`. -/
theorem step_cost_nlogn (M : ℕ → ℕ) (C K : ℕ) (Ecost : ℕ → ℕ)
    (s t : ℕ → Fin 1729 → ℕ)
    (ht : ∀ n i, 0 < t n i) (hst : ∀ n i, s n i ≤ t n i)
    (hT : ∀ n, ∏ j, t n j = transformSize n)
    (hrow : ∀ n, 2 ^ (1729 ^ 12) ≤ n →
      alphaParam 1729 n * (Nat.sqrt (precision n) + 1) *
        termOps (precision n) Ecost M ≤ K * chunkSize n ^ 2)
    (hM : ∀ n, 2 ^ (1729 ^ 12) ≤ n →
      M n ≤ stepOps (rootSize 1729 n) (precision n) (modelExponents 1729 n) (s n) (t n)
        (paperWindowA (precision n) (alphaParam 1729 n))
        (paperWindowE (precision n) (alphaParam 1729 n)) (paperIter (alphaParam 1729 n))
        Ecost M + C * n)
    (hbase : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, 2 ≤ n → n < 2 ^ (1729 ^ 12) →
      (M n : ℝ) ≤ B * n * Real.log n) :
    ∃ D : ℝ, ∀ n, 2 ≤ n → (M n : ℝ) ≤ D * n * Real.log n :=
  n_log_n_of_rec (M := fun n => (M n : ℝ))
    (A := ((2880 + 4320 * K * 1729 + C : ℕ) : ℝ) / Real.log 2)
    (by have := Real.log_pos (show (1:ℝ) < 2 by norm_num); positivity)
    (fun n => by positivity)
    (fun n hn => by
      have h := le_trans (hM n hn)
        (Nat.add_le_add_right (stepOps_params_le hn (s n) (t n) (ht n) (hst n) (hT n) Ecost M K
          (hrow n hn)) _)
      have h2 := step_cost_rec_real hn M (2880 + 4320 * K * 1729) C h
      push_cast at h2 ⊢
      exact h2)
    hbase

end IntegerMultBounds.NLogN
