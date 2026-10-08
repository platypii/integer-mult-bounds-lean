import IntegerMultBounds.NLogN.Contract
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The prime selection of Harvey–van der Hoeven Section 5.1, downstream of one
explicit analytic-number-theory input. The paper's Lemma 5.1 counts primes in
the window `((1 − 2η) x, (1 − η) x]` using Rosser and Schoenfeld's bound
`y − y/(2 log y) < ϑ(y) < y + y/(2 log y)` for `y ≥ 563`, which mathlib does not
have. `ChebyshevBound` states that bound; everything below it is proved: Lemma
5.1 itself, the existence of distinct odd primes `s_i` in the window below every
length of a power-of-two grid whose lengths are at least `2^(d^9)`, the size and
decay conditions of the recursive-step contract, and the headline theorem that
the explicit recursive step is exact for `n ≥ 2^(d^12)` with the moduli
supplied. The Chebyshev bound is the only remaining mathematical hypothesis of
the subroutine's correctness in the vector model. -/

namespace IntegerMultBounds.NLogN

open scoped BigOperators
open Real

/-- Rosser–Schoenfeld, Theorem 4: `y − y/(2 log y) < ϑ(y) < y + y/(2 log y)` for
`y ≥ 563`. Stated as a proposition; not proved here. -/
def ChebyshevBound : Prop :=
  ∀ y : ℝ, 563 ≤ y →
    y - y / (2 * Real.log y) < Chebyshev.theta y ∧ Chebyshev.theta y < y + y / (2 * Real.log y)

/-! ### Monotonicity of `y / log y` -/

/-- `y / log y` is monotone for `y ≥ e`. -/
theorem div_log_mono {x y : ℝ} (hy : Real.exp 1 ≤ y) (hxy : y ≤ x) :
    y / Real.log y ≤ x / Real.log x := by
  have hy1 : 1 ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos 1) hy
    rwa [Real.log_exp] at this
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos 1) hy
  have hx0 : 0 < x := lt_of_lt_of_le hy0 hxy
  have hx1 : 1 ≤ Real.log x := hy1.trans (Real.log_le_log hy0 hxy)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hdiv : Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hx0.ne' hy0.ne'] at hdiv
  have : y * Real.log x ≤ y * Real.log y + (x - y) := by
    have h := mul_le_mul_of_nonneg_left hdiv hy0.le
    have h2 : y * (x / y - 1) = x - y := by field_simp
    nlinarith [h, h2]
  nlinarith [hy1, hxy]

/-! ### Lemma 5.1 -/

/-- The primes `q` with `⌊y₀⌋₊ < q ≤ ⌊y₁⌋₊`. -/
noncomputable def primesIoc (y₀ y₁ : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊y₁⌋₊).filter (fun q => ⌊y₀⌋₊ < q)

theorem mem_primesIoc {y₀ y₁ : ℝ} (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁) {q : ℕ} :
    q ∈ primesIoc y₀ y₁ ↔ q.Prime ∧ y₀ < q ∧ (q : ℝ) ≤ y₁ := by
  unfold primesIoc
  rw [Finset.mem_filter, Nat.mem_primesLE, Nat.floor_lt hy₀, Nat.le_floor_iff hy₁]
  tauto

theorem theta_sub_eq {y₀ y₁ : ℝ} (h : ⌊y₀⌋₊ ≤ ⌊y₁⌋₊) :
    Chebyshev.theta y₁ - Chebyshev.theta y₀ = ∑ q ∈ primesIoc y₀ y₁, Real.log q := by
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Nat.primesLE ⌊y₁⌋₊)
    (fun q => ⌊y₀⌋₊ < q) (fun q => Real.log q)
  have hlow : (Nat.primesLE ⌊y₁⌋₊).filter (fun q => ¬ ⌊y₀⌋₊ < q) = Nat.primesLE ⌊y₀⌋₊ := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_primesLE, not_lt]
    constructor
    · rintro ⟨⟨_, hp⟩, hq⟩; exact ⟨hq, hp⟩
    · rintro ⟨hq, hp⟩; exact ⟨⟨hq.trans h, hp⟩, hq⟩
  rw [hlow] at hsplit
  unfold primesIoc
  linarith

theorem exp_eight_gt : (1126 : ℝ) < Real.exp 8 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc (1126 : ℝ) < (2.7 : ℝ) ^ 8 := by norm_num
    _ < Real.exp 1 ^ 8 := by gcongr

/-- Lemma 5.1: for `η ∈ (0, 1/4)` and `x ≥ e^{2/η}`, at least `η x / (2 log x)`
primes lie in `((1 − 2η) x, (1 − η) x]`. -/
theorem primes_in_window (hRS : ChebyshevBound) {η x : ℝ} (hη0 : 0 < η) (hη : η < 1 / 4)
    (hx : Real.exp (2 / η) ≤ x) :
    η * x / (2 * Real.log x) ≤ ((primesIoc ((1 - 2 * η) * x) ((1 - η) * x)).card : ℝ) := by
  have hlogx : 2 / η ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at this
  have hη8 : (8 : ℝ) ≤ 2 / η := by
    rw [le_div_iff₀ hη0]; linarith
  have hx8 : Real.exp 8 ≤ x := (Real.exp_le_exp.2 hη8).trans hx
  have hx1126 : (1126 : ℝ) < x := lt_of_lt_of_le exp_eight_gt hx8
  have hx0 : 0 < x := by linarith
  set y₀ := (1 - 2 * η) * x with hy₀
  set y₁ := (1 - η) * x with hy₁
  have hy₀563 : (563 : ℝ) ≤ y₀ := by
    rw [hy₀]; nlinarith
  have hy₁563 : (563 : ℝ) ≤ y₁ := by
    rw [hy₁]; nlinarith
  have hy₀y₁ : y₀ ≤ y₁ := by rw [hy₀, hy₁]; nlinarith
  have hy₁x : y₁ ≤ x := by rw [hy₁]; nlinarith
  have he : Real.exp 1 ≤ y₀ := by
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have hlog_pos : 0 < Real.log x := by linarith [show (0:ℝ) < 2 / η by positivity]
  -- the theta difference is the window sum
  have hfloor : ⌊y₀⌋₊ ≤ ⌊y₁⌋₊ := Nat.floor_le_floor hy₀y₁
  have hsum := theta_sub_eq hfloor
  -- upper bound: each term is at most `log x`
  set W := primesIoc y₀ y₁ with hW
  have hupper : ∑ q ∈ W, Real.log q ≤ (W.card : ℝ) * Real.log x := by
    have := Finset.sum_le_card_nsmul W (fun q => Real.log q) (Real.log x) (by
      intro q hq
      rw [hW, mem_primesIoc (by linarith) (by linarith)] at hq
      obtain ⟨hp, _, hqy⟩ := hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
      exact Real.log_le_log hq0 (hqy.trans hy₁x))
    simpa [nsmul_eq_mul] using this
  -- lower bound from the Chebyshev bound at `y₀` and `y₁`
  have h0 := (hRS y₀ hy₀563).2
  have h1 := (hRS y₁ hy₁563).1
  have hm0 : y₀ / Real.log y₀ ≤ x / Real.log x := div_log_mono he (hy₀y₁.trans hy₁x)
  have hm1 : y₁ / Real.log y₁ ≤ x / Real.log x := div_log_mono (he.trans hy₀y₁) hy₁x
  have hhalf0 : y₀ / (2 * Real.log y₀) = (y₀ / Real.log y₀) / 2 := by ring
  have hhalf1 : y₁ / (2 * Real.log y₁) = (y₁ / Real.log y₁) / 2 := by ring
  have hxlog : x / Real.log x ≤ η * x / 2 := by
    rw [div_le_iff₀ hlog_pos]
    have : 2 / η * x ≤ Real.log x * x := mul_le_mul_of_nonneg_right hlogx hx0.le
    have h2 : 2 / η * x = x * 2 / η := by ring
    rw [h2] at this
    rw [div_le_iff₀ hη0] at this
    nlinarith
  have hdiff : η * x / 2 < Chebyshev.theta y₁ - Chebyshev.theta y₀ := by
    have : y₁ - y₀ = η * x := by rw [hy₀, hy₁]; ring
    rw [hhalf0] at h0; rw [hhalf1] at h1
    linarith
  rw [hsum] at hdiff
  rw [div_le_iff₀ (by positivity)]
  nlinarith


/-! ### Counting at the paper's scale -/

theorem sq_le_two_pow {m : ℕ} (hm : 4 ≤ m) : m ^ 2 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    calc (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ m := by omega
      _ = 2 ^ (m + 1) := by ring

theorem eight_pow_twelve_le {d : ℕ} (hd : 2 ≤ d) : 8 * d ^ 12 ≤ 2 ^ (d ^ 9) := by
  have h6 : 8 ≤ d ^ 6 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ ≤ d ^ 6 := Nat.pow_le_pow_left hd 6
  have h9 : 4 ≤ d ^ 9 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ ≤ d ^ 9 := Nat.pow_le_pow_left hd 9
  calc 8 * d ^ 12 ≤ d ^ 6 * d ^ 12 := Nat.mul_le_mul_right _ h6
    _ = (d ^ 9) ^ 2 := by ring
    _ ≤ 2 ^ (d ^ 9) := sq_le_two_pow h9

theorem two_pow_ge_exp_one {m : ℕ} (hm : 2 ≤ m) : Real.exp 1 ≤ (2 : ℝ) ^ m := by
  have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc Real.exp 1 ≤ 4 := by linarith
    _ = (2 : ℝ) ^ 2 := by norm_num
    _ ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm

/-- The window below any `x ≥ 2^(d^9)` contains at least `d` primes' worth of
mass: `d ≤ (1/(4d)) x / (2 log x)`. -/
theorem window_count_ge {d : ℕ} (hd : 2 ≤ d) {x : ℝ} (hx : (2 : ℝ) ^ (d ^ 9) ≤ x) :
    (d : ℝ) ≤ 1 / (4 * (d : ℝ)) * x / (2 * Real.log x) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h9 : 2 ≤ d ^ 9 := by
    calc 2 ≤ 2 ^ 9 := by norm_num
      _ ≤ d ^ 9 := Nat.pow_le_pow_left hd 9
  have hx₀e : Real.exp 1 ≤ (2 : ℝ) ^ (d ^ 9) := two_pow_ge_exp_one h9
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) (hx₀e.trans hx)
  have hlogx : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) (hx₀e.trans hx)
    rwa [Real.log_exp] at this
  have hmono := div_log_mono hx₀e hx
  -- `x₀ / log x₀ ≥ 2^(d^9) / d^9 ≥ 8 d^3 ≥ 8 d^2`
  have hlog₀ : Real.log ((2 : ℝ) ^ (d ^ 9)) ≤ (d ^ 9 : ℕ) := by
    rw [Real.log_pow]
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    push_cast
    exact mul_le_of_le_one_right (by positivity) hl2
  have hlog₀pos : 0 < Real.log ((2 : ℝ) ^ (d ^ 9)) := by
    have := Real.log_le_log (Real.exp_pos 1) hx₀e
    rw [Real.log_exp] at this; linarith
  have h8 : (8 * d ^ 12 : ℕ) ≤ ((2 ^ (d ^ 9) : ℕ) : ℝ) := by
    exact_mod_cast eight_pow_twelve_le hd
  have hratio : 8 * (d : ℝ) ^ 2 ≤ (2 : ℝ) ^ (d ^ 9) / Real.log ((2 : ℝ) ^ (d ^ 9)) := by
    rw [le_div_iff₀ hlog₀pos]
    have h1 : 8 * (d : ℝ) ^ 2 * Real.log ((2 : ℝ) ^ (d ^ 9)) ≤ 8 * (d : ℝ) ^ 2 * (d ^ 9 : ℕ) :=
      mul_le_mul_of_nonneg_left hlog₀ (by positivity)
    have h2 : (8 * (d : ℝ) ^ 2 * (d ^ 9 : ℕ)) ≤ (8 * d ^ 12 : ℕ) := by
      push_cast
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      nlinarith [pow_nonneg hd0.le 11]
    push_cast at h8 h2 h1
    linarith
  have hfinal : 8 * (d : ℝ) ^ 2 * Real.log x ≤ x := by
    have := hratio.trans hmono
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  rw [le_div_iff₀ (by linarith)]
  have : 1 / (4 * (d : ℝ)) * x = x / (4 * d) := by ring
  rw [this, le_div_iff₀ (by positivity)]
  nlinarith

theorem exp_mul_le_two_pow {d : ℕ} (hd : 2 ≤ d) : Real.exp (8 * d) ≤ (2 : ℝ) ^ (d ^ 9) := by
  have h8 : Real.exp 8 ≤ (2 : ℝ) ^ 12 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc Real.exp 1 ^ 8 ≤ (2.7182818286 : ℝ) ^ 8 := by gcongr
      _ ≤ (2 : ℝ) ^ 12 := by norm_num
  have h12 : 12 * d ≤ d ^ 9 := by
    have : 12 ≤ d ^ 8 := by
      calc 12 ≤ 2 ^ 8 := by norm_num
        _ ≤ d ^ 8 := Nat.pow_le_pow_left hd 8
    calc 12 * d ≤ d ^ 8 * d := Nat.mul_le_mul_right _ this
      _ = d ^ 9 := by ring
  calc Real.exp (8 * d) = Real.exp 8 ^ d := by
        rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ ((2 : ℝ) ^ 12) ^ d := pow_le_pow_left₀ (Real.exp_pos 8).le h8 d
    _ = (2 : ℝ) ^ (12 * d) := by rw [← pow_mul]
    _ ≤ (2 : ℝ) ^ (d ^ 9) := pow_le_pow_right₀ (by norm_num) h12

/-! ### Moduli existence -/

/-- The window below `v` at `η = 1/(4d)`: primes in `((1 − 1/(2d)) v, (1 − 1/(4d)) v]`. -/
noncomputable def moduliWindow (d v : ℕ) : Finset ℕ :=
  primesIoc ((1 - 2 * (1 / (4 * (d : ℝ)))) * v) ((1 - 1 / (4 * (d : ℝ))) * v)

theorem mem_moduliWindow {d v q : ℕ} (hd : 2 ≤ d) :
    q ∈ moduliWindow d v ↔
      q.Prime ∧ (1 - 2 * (1 / (4 * (d : ℝ)))) * v < q ∧ (q : ℝ) ≤ (1 - 1 / (4 * (d : ℝ))) * v := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hη : 1 / (4 * (d : ℝ)) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  unfold moduliWindow
  apply mem_primesIoc
  · have : (0 : ℝ) ≤ v := Nat.cast_nonneg v
    nlinarith
  · have : (0 : ℝ) ≤ v := Nat.cast_nonneg v
    nlinarith

theorem card_moduliWindow_ge (hRS : ChebyshevBound) {d v : ℕ} (hd : 2 ≤ d)
    (hv : 2 ^ (d ^ 9) ≤ v) : d ≤ (moduliWindow d v).card := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hη0 : 0 < 1 / (4 * (d : ℝ)) := by positivity
  have hη : 1 / (4 * (d : ℝ)) < 1 / 4 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hvR : (2 : ℝ) ^ (d ^ 9) ≤ v := by exact_mod_cast hv
  have hexp : Real.exp (2 / (1 / (4 * (d : ℝ)))) ≤ v := by
    have : 2 / (1 / (4 * (d : ℝ))) = 8 * d := by field_simp; ring
    rw [this]
    exact (exp_mul_le_two_pow hd).trans hvR
  have h1 := primes_in_window hRS hη0 hη hexp
  have h2 := window_count_ge hd hvR
  have : (d : ℝ) ≤ ((moduliWindow d v).card : ℝ) := by
    unfold moduliWindow
    exact h2.trans h1
  exact_mod_cast this

theorem two_pow_lt_double {a b : ℕ} (h : 2 ^ a < 2 ^ b) : 2 * 2 ^ a ≤ 2 ^ b := by
  have hab : a < b := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h
  calc 2 * 2 ^ a = 2 ^ (a + 1) := by ring
    _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab

/-- Distinct primes `s_i` in the windows below the grid lengths `t_i`, for any
power-of-two grid with all lengths at least `2^(d^9)`. -/
theorem exists_moduli (hRS : ChebyshevBound) {d : ℕ} (hd : 2 ≤ d) (t : Fin d → ℕ)
    (hpow : ∀ i, ∃ k, t i = 2 ^ k) (hbig : ∀ i, 2 ^ (d ^ 9) ≤ t i) :
    ∃ s : Fin d → ℕ, (∀ i, (s i).Prime) ∧ Function.Injective s ∧
      ∀ i, (1 - 1 / (2 * (d : ℝ))) * t i < s i ∧ (s i : ℝ) ≤ (1 - 1 / (4 * (d : ℝ))) * t i := by
  classical
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  -- per length value, an injective assignment of window primes to its fiber
  have hfib : ∀ v : ℕ, ∃ f : {i : Fin d // t i = v} → ℕ,
      Function.Injective f ∧ ∀ i, f i ∈ moduliWindow d v := by
    intro v
    by_cases h : ∃ i, t i = v
    · obtain ⟨i₀, hi₀⟩ := h
      have hcard : d ≤ (moduliWindow d v).card := by
        rw [← hi₀]; exact card_moduliWindow_ge hRS hd (hbig i₀)
      have hle : Fintype.card {i : Fin d // t i = v} ≤ Fintype.card (moduliWindow d v) := by
        rw [Fintype.card_coe]
        exact (Fintype.card_subtype_le _).trans (by simpa using hcard)
      obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hle
      exact ⟨fun i => (emb i).val, Subtype.val_injective.comp emb.injective, fun i => (emb i).2⟩
    · push Not at h
      exact ⟨fun _ => 0, fun a _ _ => absurd a.2 (h a.1), fun i => absurd i.2 (h i.1)⟩
  choose f hfinj hfmem using hfib
  refine ⟨fun i => f (t i) ⟨i, rfl⟩, ?_, ?_, ?_⟩
  · intro i
    exact ((mem_moduliWindow hd).1 (hfmem (t i) ⟨i, rfl⟩)).1
  · -- injectivity
    have hkey : ∀ (j : Fin d) (v : ℕ) (hj : t j = v), f (t j) ⟨j, rfl⟩ = f v ⟨j, hj⟩ := by
      intro j v hj; subst hj; rfl
    have hsep : ∀ i j, t i < t j → (f (t i) ⟨i, rfl⟩ : ℝ) < f (t j) ⟨j, rfl⟩ := by
      intro i j hij
      obtain ⟨a, ha⟩ := hpow i
      obtain ⟨b, hb⟩ := hpow j
      have hdouble : 2 * t i ≤ t j := by rw [ha, hb]; exact two_pow_lt_double (ha ▸ hb ▸ hij)
      have hdR : (2 : ℝ) * t i ≤ t j := by exact_mod_cast hdouble
      have hi := ((mem_moduliWindow hd).1 (hfmem (t i) ⟨i, rfl⟩)).2.2
      have hj := ((mem_moduliWindow hd).1 (hfmem (t j) ⟨j, rfl⟩)).2.1
      have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hη : 1 / (4 * (d : ℝ)) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have hti : (0 : ℝ) ≤ t i := Nat.cast_nonneg _
      have h3 : (1 - 1 / (4 * (d : ℝ))) * t i ≤ (1 - 2 * (1 / (4 * (d : ℝ)))) * (2 * t i) := by
        nlinarith
      have h4 : (1 - 2 * (1 / (4 * (d : ℝ)))) * (2 * t i) ≤ (1 - 2 * (1 / (4 * (d : ℝ)))) * t j :=
        mul_le_mul_of_nonneg_left hdR (by linarith)
      linarith
    intro i j hij
    rcases lt_trichotomy (t i) (t j) with h | h | h
    · have := hsep i j h
      simp only at hij
      rw [hij] at this; exact absurd this (lt_irrefl _)
    · have h1 := hkey j (t i) h.symm
      simp only at hij
      have heq : f (t i) ⟨i, rfl⟩ = f (t i) ⟨j, h.symm⟩ := hij.trans h1
      have := hfinj (t i) heq
      exact congrArg Subtype.val this
    · have := hsep j i h
      simp only at hij
      rw [hij] at this; exact absurd this (lt_irrefl _)
  · intro i
    have h := ((mem_moduliWindow hd).1 (hfmem (t i) ⟨i, rfl⟩)).2
    refine ⟨?_, h.2⟩
    have : (1 - 1 / (2 * (d : ℝ))) = 1 - 2 * (1 / (4 * (d : ℝ))) := by field_simp; ring
    rw [this]; exact h.1


/-! ### The conditions of the recursive-step contract -/

theorem four_d_le_alpha {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    4 * d ≤ alphaParam d n := by
  have hb := chunkSize_ge hn
  have hα := alphaParam_pow_ge d n
  have h10 : 256 ≤ 12 * d ^ 10 := by
    calc 256 ≤ 12 * 2 ^ 10 := by norm_num
      _ ≤ 12 * d ^ 10 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 10)
  have h4 : (4 * d) ^ 4 ≤ alphaParam d n ^ 4 := by
    calc (4 * d) ^ 4 = 256 * d ^ 4 := by ring
      _ ≤ 12 * d ^ 10 * d ^ 4 := Nat.mul_le_mul_right _ h10
      _ = 12 * d ^ 2 * d ^ 12 := by ring
      _ ≤ 12 * d ^ 2 * chunkSize n := Nat.mul_le_mul_left _ hb
      _ ≤ alphaParam d n ^ 4 := hα
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h4

/-- The moduli of `exists_moduli` satisfy every side condition of the
recursive-step contract: `s_i < t_i`, `∏ s_i ≤ ∏ t_i < 2 ∏ s_i`, pairwise and
grid coprimality, and the decay condition `α²(t_i/s_i − 1) ≥ 1`. -/
theorem moduli_conditions {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) (t s : Fin d → ℕ)
    (hpow : ∀ i, ∃ k, t i = 2 ^ k) (hbig : ∀ i, 2 ^ (d ^ 9) ≤ t i)
    (hp : ∀ i, (s i).Prime) (hinj : Function.Injective s)
    (hwin : ∀ i, (1 - 1 / (2 * (d : ℝ))) * t i < s i ∧
      (s i : ℝ) ≤ (1 - 1 / (4 * (d : ℝ))) * t i) :
    (∀ i, s i < t i) ∧ ∏ i, s i ≤ ∏ i, t i ∧ ∏ i, t i < 2 * ∏ i, s i ∧
      Pairwise (Function.onFun Nat.Coprime s) ∧ (∀ i, Nat.Coprime (s i) (t i)) ∧
      ∀ i, 1 ≤ ((alphaParam d n : ℕ) : ℝ) ^ 2 * ((t i : ℝ) / (s i) - 1) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht512 : ∀ i, 512 ≤ t i := fun i =>
    calc 512 = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ (d ^ 9) := Nat.pow_le_pow_right (by norm_num) (by
          calc 9 ≤ 2 ^ 9 := by norm_num
            _ ≤ d ^ 9 := Nat.pow_le_pow_left hd 9)
      _ ≤ t i := hbig i
  have hti0 : ∀ i, 0 < t i := fun i => by have := ht512 i; omega
  have hst : ∀ i, s i < t i := by
    intro i
    have h := (hwin i).2
    have htR : (0 : ℝ) < t i := by exact_mod_cast hti0 i
    have : (s i : ℝ) < t i := by
      have : 1 / (4 * (d : ℝ)) * t i > 0 := by positivity
      nlinarith
    exact_mod_cast this
  refine ⟨hst, Finset.prod_le_prod fun i _ => (hst i).le, ?_, ?_, ?_, ?_⟩
  · apply two_mul_prod_gt (by omega) s t hti0
    intro i
    have h := (hwin i).1
    have hcast : (((4 * d - 2 : ℕ) : ℝ)) = 4 * d - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have : ((4 * d - 2 : ℕ) : ℝ) * t i < 4 * d * s i := by
      rw [hcast]
      have h' := mul_lt_mul_of_pos_left h (by positivity : (0 : ℝ) < 4 * d)
      have : (4 * (d : ℝ)) * ((1 - 1 / (2 * (d : ℝ))) * t i) = (4 * d - 2) * t i := by
        field_simp; ring
      linarith
    exact_mod_cast this
  · intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).2 fun h => hij (hinj h)
  · intro i
    obtain ⟨k, hk⟩ := hpow i
    have hne : s i ≠ 2 := by
      have h := (hwin i).1
      have h512 : (512 : ℝ) ≤ t i := by exact_mod_cast ht512 i
      have hq : (1 - 1 / (2 * (d : ℝ))) ≥ 3 / 4 := by
        have : 1 / (2 * (d : ℝ)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        linarith
      have : (2 : ℝ) < s i := by nlinarith
      intro h2; rw [h2] at this; norm_num at this
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes (hp i) Nat.prime_two).2 hne)
  · intro i
    have hα : (4 * (d : ℝ)) ≤ ((alphaParam d n : ℕ) : ℝ) := by
      exact_mod_cast four_d_le_alpha hd hn
    have hA : 16 * (d : ℝ) ^ 2 ≤ ((alphaParam d n : ℕ) : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hα 2
      nlinarith
    have hs0 : (0 : ℝ) < s i := by exact_mod_cast (hp i).pos
    have htR : (0 : ℝ) < t i := by exact_mod_cast hti0 i
    have hsleT : (s i : ℝ) ≤ t i := by exact_mod_cast (hst i).le
    have hB : (t i : ℝ) ≤ 4 * d * (t i - s i) := by
      have h := (hwin i).2
      have h' := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4 * d)
      have : (4 * (d : ℝ)) * ((1 - 1 / (4 * (d : ℝ))) * t i) = 4 * d * t i - t i := by
        field_simp
      linarith
    have hts : (0 : ℝ) ≤ t i - s i := by linarith
    have hmain : (s i : ℝ) ≤ ((alphaParam d n : ℕ) : ℝ) ^ 2 * (t i - s i) := by
      calc (s i : ℝ) ≤ t i := hsleT
        _ ≤ 4 * d * (t i - s i) := hB
        _ ≤ 4 * d * (4 * d * (t i - s i)) := by
            have := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 4 * d)
            nlinarith
        _ = 16 * d ^ 2 * (t i - s i) := by ring
        _ ≤ ((alphaParam d n : ℕ) : ℝ) ^ 2 * (t i - s i) :=
            mul_le_mul_of_nonneg_right hA hts
    rw [div_sub_one hs0.ne', ← mul_div_assoc, le_div_iff₀ hs0, one_mul]
    exact hmain

/-! ### The grid with its lower bound -/

theorem transformExp_gt {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    Nat.log 2 n / 2 + 2 < transformExp n := by
  set L := Nat.log 2 n with hL
  have hd12 := pow_twelve_ge hd
  have hLd : d ^ 12 ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have hn2 : 2 ≤ n := by
    calc 2 ≤ 2 ^ (d ^ 12) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (d ^ 12) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ n := hn
  have hnL : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hb := chunkSize_le_log_succ n
  have hT := (transformSize_bounds hn2).1
  have hL8 : 8 ≤ L := by omega
  have hhalf := succ_lt_two_pow_half hL8
  set T := transformSize n with hT'
  have hTpos : 0 < T := by unfold transformSize at hT'; rw [hT']; positivity
  have h1 : 4 * 2 ^ L < T * 2 ^ (L / 2) := by
    calc 4 * 2 ^ L ≤ 4 * n := by omega
      _ ≤ T * chunkSize n := hT
      _ ≤ T * (L + 1) := Nat.mul_le_mul_left _ hb
      _ < T * 2 ^ (L / 2) := Nat.mul_lt_mul_of_pos_left hhalf hTpos
  have h2 : 2 ^ (L / 2) * 2 ^ (L / 2) ≤ 2 ^ L := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (4 * 2 ^ (L / 2)) * 2 ^ (L / 2) < T * 2 ^ (L / 2) := by
    calc (4 * 2 ^ (L / 2)) * 2 ^ (L / 2) = 4 * (2 ^ (L / 2) * 2 ^ (L / 2)) := by ring
      _ ≤ 4 * 2 ^ L := Nat.mul_le_mul_left _ h2
      _ < T * 2 ^ (L / 2) := h1
  have h4 : 4 * 2 ^ (L / 2) < T := Nat.lt_of_mul_lt_mul_right h3
  have h5 : 2 ^ (L / 2 + 2) < 2 ^ transformExp n := by
    rw [pow_add]; unfold transformSize at hT'; rw [hT'] at h4; linarith
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h5

theorem rootExp_ge_pow {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    d ^ 9 + 1 ≤ rootExp d n := by
  have hE := transformExp_gt hd hn
  have hR := rootExp_mul_ge (n := n) (d := d) (by omega)
  have hLd : d ^ 12 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have h4 : 4 * d ^ 10 ≤ d ^ 12 := by
    calc 4 * d ^ 10 ≤ d ^ 2 * d ^ 10 := Nat.mul_le_mul_right _ (by nlinarith)
      _ = d ^ 12 := by ring
  by_contra hlt
  push Not at hlt
  have hR' : rootExp d n ≤ d ^ 9 := by omega
  have := Nat.mul_le_mul_right d hR'
  have h10 : d ^ 9 * d = d ^ 10 := by ring
  rw [h10] at this
  omega

/-- The grid of Section 5.1 with its lower bound: every length is at least
`2^(rootExp − 1) = r/2`. -/
theorem exists_grid_lower {d' n : ℕ} (hd' : 1 ≤ d') (hn : 2 ^ ((d' + 1) ^ 12) ≤ n) :
    ∃ (e : Fin d' → ℕ) (g : ℕ), (∀ i, 1 ≤ e i) ∧ 1 ≤ g ∧ (∀ i, 2 ^ e i ∣ 2 * 2 ^ g) ∧
      ∏ i, lenOf e g i = transformSize n ∧
      ∀ i, 2 ^ (rootExp (d' + 1) n - 1) ≤ lenOf e g i := by
  have hk := rootExp_ge_two (d := d' + 1) (by omega) hn
  have hd₀ := dimShift_lt (d := d' + 1) (n := n) (by omega)
  set k := rootExp (d' + 1) n with hkdef
  set d₀ := dimShift (d' + 1) n with hd₀def
  let fexp : Fin (d' + 1) → ℕ := fun i => if i.val < d₀ then k - 1 else k
  have hfexp_ge : ∀ i, k - 1 ≤ fexp i := by
    intro i; simp only [fexp]; split_ifs <;> omega
  have hfexp_le : ∀ i, fexp i ≤ k := by
    intro i; simp only [fexp]; split_ifs <;> omega
  have hlast : fexp (Fin.last d') = k := by
    simp [fexp, show ¬ d' < d₀ by omega]
  have hlen : ∀ i, lenOf (fun i => fexp (Fin.castSucc i)) (fexp (Fin.last d')) i = 2 ^ fexp i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [lenOf, Fin.snoc_last]
    · simp only [lenOf, Fin.snoc_castSucc]
  have hfac : ∀ i : Fin (d' + 1), 2 ^ fexp i = factorAt (d' + 1) n i.val := by
    intro i
    simp only [fexp, factorAt]
    split_ifs <;> rfl
  refine ⟨fun i => fexp (Fin.castSucc i), fexp (Fin.last d'), ?_, ?_, ?_, ?_, ?_⟩
  · intro i; show 1 ≤ fexp (Fin.castSucc i); have := hfexp_ge (Fin.castSucc i); omega
  · rw [hlast]; omega
  · intro i
    rw [hlast]
    exact (pow_dvd_pow 2 (hfexp_le _)).trans (Dvd.intro_left 2 rfl)
  · simp_rw [hlen, hfac]
    rw [Fin.prod_univ_eq_prod_range (fun i => factorAt (d' + 1) n i) (d' + 1)]
    exact factorAt_prod (by omega) (by omega)
  · intro i
    rw [hlen]
    exact Nat.pow_le_pow_right (by norm_num) (hfexp_ge i)

/-! ### The headline theorem -/

/-- Under the Chebyshev bound, for `d = d' + 1 ≥ 2` and `n ≥ 2^(d^12)`, there are
a power-of-two grid and prime moduli for which the explicit numerical recursive
step returns the exact product of any two `n`-bit inputs, for every admissible
rounding oracle. -/
theorem nlogn_step_of_chebyshev (hRS : ChebyshevBound) {d' n : ℕ} (hd' : 1 ≤ d')
    (hn : 2 ^ ((d' + 1) ^ 12) ≤ n) {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    ∃ (e : Fin d' → ℕ) (g : ℕ) (s : Fin (d' + 1) → ℕ) (_ : ∀ i, NeZero (s i))
      (hs : Pairwise (Function.onFun Nat.Coprime s))
      (hcop : ∀ i, Nat.Coprime (s i) (lenAll (Mof e g) i)),
      (∀ i, (s i).Prime) ∧ (∀ i, s i < lenOf e g i) ∧
      ∀ (E₁ E₂ E₃ : (i : Fin d') → (m : ℕ) → Fin (2 ^ (m + 1)) →
          (Fin (lenLast (Mof e g)) → ℂ)),
        (∀ i m k, ‖E₁ i m k‖ ≤ 1 / 2 ^ precision n) →
        (∀ i m k, ‖E₂ i m k‖ ≤ 1 / 2 ^ precision n) →
        (∀ i m k, ‖E₃ i m k‖ ≤ 1 / 2 ^ precision n) →
        recursiveStepOutput n e g s hs hcop E₁ E₂ E₃ x y
          = Machine.binaryValue x * Machine.binaryValue y := by
  obtain ⟨e, g, he, hg, hdiv, hT, hlow⟩ := exists_grid_lower hd' hn
  have hd : 2 ≤ d' + 1 := by omega
  have hk := rootExp_ge_pow (d := d' + 1) hd hn
  have hbig : ∀ i, 2 ^ ((d' + 1) ^ 9) ≤ lenOf e g i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (hlow i)
  have hpow : ∀ i, ∃ k, lenOf e g i = 2 ^ k := fun i => ⟨_, rfl⟩
  obtain ⟨s, hp, hinj, hwin⟩ := exists_moduli hRS hd (lenOf e g) hpow hbig
  obtain ⟨hst, hS, hS2, hs, hcop, hθ⟩ :=
    moduli_conditions hd hn (lenOf e g) s hpow hbig hp hinj hwin
  have : ∀ i, NeZero (s i) := fun i => ⟨(hp i).pos.ne'⟩
  rw [hT] at hS hS2
  refine ⟨e, g, s, inferInstance, hs, by rw [lenAll_Mof]; exact hcop, hp, hst, ?_⟩
  intro E₁ E₂ E₃ hE₁ hE₂ hE₃
  exact recursive_step_correct hd' hn hx hy e g he hg hdiv hT s hs hS hS2 hst hcop hθ
    E₁ E₂ E₃ hE₁ hE₂ hE₃

end IntegerMultBounds.NLogN
