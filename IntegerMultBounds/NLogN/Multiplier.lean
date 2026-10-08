import IntegerMultBounds.NLogN.Pipeline
import IntegerMultBounds.NLogN.ErrorBudget
import IntegerMultBounds.NLogN.Carry

/-! The assembled fixed-point FFT multiplier on bit strings. Two `n`-bit inputs
are cut into `k`-bit digits, transformed with length `2 ^ m` and `p` bits of
precision (modelled by the error oracles of the error budget), multiplied
pointwise, transformed back, rounded, and carried into exactly `2 n` bits.
Proved: with `2 m + 4 + k ≤ p` and `2 ^ m + 1` positions for the digit
convolution, the output's `binaryValue` is the product and its length is
`2 n`; the parameter choice `k * L = 2 n`, `m = ⌈log₂ (2 L)⌉` meets the
length condition with `2 ^ m ≤ 4 L`; and the count of fixed-point complex ring
operations is `(6 m + 1) 2 ^ m`. Chunking, rounding, carries, and twiddle
generation are not counted, and nothing is compiled to tape steps. -/

namespace IntegerMultBounds.NLogN

open Complex

/-! ### Digits of a bit string -/

/-- Base-`2 ^ k` digits of a most-significant-first bit string, least
significant first. -/
def digitsOf (k : ℕ) (x : List Bool) : List ℕ :=
  (chunks k (x.reverse.map bitDigit)).map (evalBase 2)

theorem bitDigit_lt (b : Bool) : bitDigit b < 2 := by
  cases b <;> simp [bitDigit]

theorem digitsOf_lt {k : ℕ} (hk : 0 < k) (x : List Bool) :
    ∀ d ∈ digitsOf k x, d < 2 ^ k := by
  intro d hd
  simp only [digitsOf, List.mem_map] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  refine chunk_value_lt (by norm_num) hk ?_ c hc
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨b, _, rfl⟩ := he
  exact bitDigit_lt b

theorem evalBase_digitsOf {k : ℕ} (hk : 0 < k) (x : List Bool) :
    evalBase (2 ^ k) (digitsOf k x) = Machine.binaryValue x := by
  rw [binaryValue_eq_evalBase, digitsOf, ← evalBase_chunks 2 hk]
  rfl

theorem getD_lt {ds : List ℕ} {M : ℕ} (h : ∀ d ∈ ds, d < M) (hM : 0 < M) (i : ℕ) :
    ds.getD i 0 < M := by
  by_cases hi : i < ds.length
  · rw [getD_eq_getElem hi]
    exact h _ (List.getElem_mem hi)
  · rw [getD_of_length_le (by omega)]
    exact hM

/-- The zero-padded complex vector of a digit list. -/
noncomputable def vecOf (m : ℕ) (ds : List ℕ) : Fin (2 ^ m) → ℂ :=
  fun i => (ds.getD i 0 : ℂ)

theorem norm_vecOf_le {k : ℕ} (hk : 0 < k) (m : ℕ) (x : List Bool) (i : Fin (2 ^ m)) :
    ‖vecOf m (digitsOf k x) i‖ ≤ (2 : ℝ) ^ k := by
  simp only [vecOf, norm_natCast]
  have := getD_lt (digitsOf_lt hk x) (by positivity) i.val
  exact_mod_cast this.le

/-! ### The multiplier -/

/-- Rounded perturbed pipeline on the digit vectors, carried into `k * L` bits. -/
noncomputable def mulFixed (k L m : ℕ) (ω : ℂ) (e₁ e₂ e₃ : (j : ℕ) → Fin (2 ^ (j + 1)) → ℂ)
    (r : Fin (2 ^ m) → ℂ) (x y : List Bool) : List Bool :=
  toBits k L (List.ofFn fun i : Fin (2 ^ m) =>
    (round (pipelineErr m ω e₁ e₂ e₃ r (vecOf m (digitsOf k x)) (vecOf m (digitsOf k y)) i).re).toNat)

theorem pipelineExact_eq_fftMul (m : ℕ) (ω : ℂ) (a b : Fin (2 ^ m) → ℂ) :
    pipelineExact m ω a b = fftMul m ω a b := rfl

/-- The exact pipeline on digit vectors is the integer cyclic convolution. -/
theorem pipelineExact_vecOf {m : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω (2 ^ m))
    (dx dy : List ℕ) :
    pipelineExact m ω (vecOf m dx) (vecOf m dy) =
      fun i : Fin (2 ^ m) => ((((cconvList (2 ^ m) dx dy).getD i 0 : ℕ) : ℤ) : ℂ) := by
  rw [pipelineExact_eq_fftMul, fftMul_eq_cconvFin hω]
  funext i
  rw [Int.cast_natCast]
  exact cconvFin_eq_cconvList dx dy i

/-- The rounded perturbed pipeline is the list-level cyclic convolution. -/
theorem mulFixed_list {k m p : ℕ} (hk : 0 < k) {ω : ℂ} (hω : IsPrimitiveRoot ω (2 ^ m))
    {e₁ e₂ e₃ : (j : ℕ) → Fin (2 ^ (j + 1)) → ℂ} {r : Fin (2 ^ m) → ℂ}
    (hε₁ : ∀ i j, ‖e₁ i j‖ ≤ 1 / 2 ^ p) (hε₂ : ∀ i j, ‖e₂ i j‖ ≤ 1 / 2 ^ p)
    (hε₃ : ∀ i j, ‖e₃ i j‖ ≤ 1 / 2 ^ p) (hr : ∀ j, ‖r j‖ ≤ 1 / 2 ^ p)
    (hp : 2 * m + 4 + k ≤ p) (x y : List Bool) :
    (List.ofFn fun i : Fin (2 ^ m) =>
      (round (pipelineErr m ω e₁ e₂ e₃ r (vecOf m (digitsOf k x))
        (vecOf m (digitsOf k y)) i).re).toNat) =
      cconvList (2 ^ m) (digitsOf k x) (digitsOf k y) := by
  have hω1 : ‖ω‖ = 1 := hω.norm'_eq_one (pow_ne_zero m two_ne_zero)
  have hA1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hp' : (2 : ℝ) ^ (2 * m + 4) * 2 ^ k ≤ 2 ^ p := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hp
  have hround := pipeline_exact_recovery_pow m p ω hω1 (2 ^ k) e₁ e₂ e₃ r
    (vecOf m (digitsOf k x)) (vecOf m (digitsOf k y)) hε₁ hε₂ hε₃ hr
    (norm_vecOf_le hk m x) (norm_vecOf_le hk m y) hA1 hp'
    (fun i : Fin (2 ^ m) => (((cconvList (2 ^ m) (digitsOf k x) (digitsOf k y)).getD i 0 : ℕ) : ℤ))
    (pipelineExact_vecOf hω _ _)
  have hf : (fun i : Fin (2 ^ m) =>
      (round (pipelineErr m ω e₁ e₂ e₃ r (vecOf m (digitsOf k x))
        (vecOf m (digitsOf k y)) i).re).toNat) =
      fun i : Fin (2 ^ m) => (cconvList (2 ^ m) (digitsOf k x) (digitsOf k y)).getD i 0 := by
    funext i
    rw [congrFun hround i, Int.toNat_natCast]
  rw [hf]
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    rw [List.getElem_ofFn, ← getD_eq_getElem h₂]

/-- The fixed-point multiplier returns the exact `2 n`-bit product. -/
theorem mulFixed_correct {k L m p n : ℕ} (hk : 0 < k) {ω : ℂ}
    (hω : IsPrimitiveRoot ω (2 ^ m))
    {e₁ e₂ e₃ : (j : ℕ) → Fin (2 ^ (j + 1)) → ℂ} {r : Fin (2 ^ m) → ℂ}
    (hε₁ : ∀ i j, ‖e₁ i j‖ ≤ 1 / 2 ^ p) (hε₂ : ∀ i j, ‖e₂ i j‖ ≤ 1 / 2 ^ p)
    (hε₃ : ∀ i j, ‖e₃ i j‖ ≤ 1 / 2 ^ p) (hr : ∀ j, ‖r j‖ ≤ 1 / 2 ^ p)
    (hp : 2 * m + 4 + k ≤ p) {x y : List Bool} (hx : x.length = n) (hy : y.length = n)
    (hL : k * L = 2 * n)
    (hm : (digitsOf k x).length + (digitsOf k y).length ≤ 2 ^ m + 1) :
    Machine.binaryValue (mulFixed k L m ω e₁ e₂ e₃ r x y) =
        Machine.binaryValue x * Machine.binaryValue y ∧
      (mulFixed k L m ω e₁ e₂ e₃ r x y).length = 2 * n := by
  unfold mulFixed
  rw [mulFixed_list hk hω hε₁ hε₂ hε₃ hr hp x y]
  have hval : evalBase (2 ^ k) (cconvList (2 ^ m) (digitsOf k x) (digitsOf k y)) =
      Machine.binaryValue x * Machine.binaryValue y := by
    rw [evalBase_cconvList _ hm, evalBase_digitsOf hk, evalBase_digitsOf hk]
  have hfit : evalBase (2 ^ k) (cconvList (2 ^ m) (digitsOf k x) (digitsOf k y)) <
      (2 ^ k) ^ L := by
    rw [hval, ← pow_mul, hL]
    exact Machine.product_fits hx hy
  obtain ⟨h1, h2⟩ := binaryValue_toBits hk hfit
  exact ⟨h1.trans hval, h2.trans hL⟩

/-! ### Parameters -/

theorem chunks_length_le (k : ℕ) (ds : List ℕ) :
    (chunks (k + 1) ds).length ≤ (ds.length + k) / (k + 1) := by
  match ds with
  | [] => simp
  | d :: ds =>
    rw [chunks_cons]
    simp only [List.length_cons]
    have ih := chunks_length_le k (ds.drop k)
    rw [List.length_drop] at ih
    have hdiv : (ds.length + 1 + k) / (k + 1) = (ds.length - k + k) / (k + 1) + 1 := by
      by_cases hkl : k ≤ ds.length
      · have e : ds.length + 1 + k = (ds.length - k + k) + (k + 1) := by omega
        rw [e, Nat.add_div_right _ (by omega)]
      · have e1 : ds.length - k + k = k := by omega
        rw [e1, Nat.div_eq_of_lt (show k < k + 1 by omega)]
        have := Nat.div_eq_of_lt_le (show 1 * (k + 1) ≤ ds.length + 1 + k by omega)
          (show ds.length + 1 + k < (1 + 1) * (k + 1) by omega)
        omega
    omega
termination_by ds.length
decreasing_by all_goals (simp [List.length_drop]; try omega)

theorem digitsOf_length_le {k L n : ℕ} (hk : 0 < k) {x : List Bool} (hx : x.length = n)
    (hL : k * L = 2 * n) : (digitsOf k x).length ≤ L := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp only [digitsOf, List.length_map]
  have h := chunks_length_le k (x.reverse.map bitDigit)
  rw [List.length_map, List.length_reverse, hx] at h
  refine h.trans ?_
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  rw [Nat.succ_eq_add_one] at hL
  omega

/-- With `k * L = 2 n` and `m = ⌈log₂ (2 L)⌉`, the digit convolution fits. -/
theorem mulFixed_params {k L n : ℕ} (hk : 0 < k) {x y : List Bool} (hx : x.length = n)
    (hy : y.length = n) (hL : k * L = 2 * n) :
    (digitsOf k x).length + (digitsOf k y).length ≤ 2 ^ Nat.clog 2 (2 * L) + 1 := by
  have h1 := digitsOf_length_le hk hx hL
  have h2 := digitsOf_length_le hk hy hL
  have h3 := Nat.le_pow_clog (b := 2) (by norm_num) (2 * L)
  omega

theorem pow_clog_le {L : ℕ} (hL : 1 ≤ L) : 2 ^ Nat.clog 2 (2 * L) ≤ 4 * L := by
  have hpos := Nat.clog_pos (b := 2) (n := 2 * L) (by norm_num) (by omega)
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := 2 * L) (by omega)
  obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [hc] at h ⊢
  rw [Nat.pred_succ] at h
  rw [pow_succ]
  omega

/-! ### Operation count -/

/-- Three transforms and `2 ^ m` pointwise products. -/
def mulFixedOps (m : ℕ) : ℕ := 3 * fftCost m + 2 ^ m

theorem mulFixedOps_eq (m : ℕ) : mulFixedOps m = 6 * m * 2 ^ m + 2 ^ m := by
  simp only [mulFixedOps, fftCost_eq, pow_succ]
  ring

theorem mulFixedOps_le {m : ℕ} (hm : 1 ≤ m) : mulFixedOps m ≤ 7 * m * 2 ^ m := by
  rw [mulFixedOps_eq]
  nlinarith [Nat.one_le_two_pow (n := m)]

end IntegerMultBounds.NLogN
