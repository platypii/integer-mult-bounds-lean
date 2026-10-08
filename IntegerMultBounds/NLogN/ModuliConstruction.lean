import IntegerMultBounds.NLogN.PrimeSelection
import IntegerMultBounds.NLogN.Primes

/-! An elementary construction of the moduli, replacing the paper's Lemma 5.1.

The recursive-step contract needs, for every coordinate `i` with a power-of-two
length `t_i`, an odd modulus `s_i` with `(1 − 1/(2d)) t_i < s_i ≤ (1 − 1/(4d)) t_i`,
the moduli pairwise coprime. Primality of the moduli is never used. We take
`s_i := p_i^a q_i^b` for two odd primes `p_i ≠ q_i` assigned to coordinate `i`
(distinct across coordinates), with exponents chosen by a pigeonhole argument on
the values `a log p + b log q`: two such values within `w` of each other give a
step `δ ∈ (0, w)`, and walking from a base point by that step lands in any window
of width `w` far enough out. The step is at least `1/(pq)^M`, so the walk needs
`log t` to exceed an explicit exponential in the pigeonhole range `M`; this holds
once `n ≥ 2^(2^(1000 d³))`, a larger threshold than the paper's `2^(d^12)` but
one that changes nothing asymptotically.

Proved: the two-prime window lemma, odd moduli in every window of relative width
`η ≤ 1/8`, pairwise coprime moduli for any power-of-two grid above the
threshold, the conditions of the recursive-step contract from oddness and
pairwise coprimality alone, and the headline theorem `nlogn_step_unconditional`
with no number-theoretic hypothesis. Nothing is assumed beyond mathlib. -/

namespace IntegerMultBounds.NLogN

open scoped BigOperators
open Real

/-! ### Logarithms of prime powers -/

theorem log_natPrime_pos {p : ℕ} (hp : p.Prime) : 0 < Real.log p :=
  Real.log_pos (by exact_mod_cast hp.one_lt)

theorem factorization_pow_mul_pow_left {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : (p ^ a * q ^ b).factorization p = a := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
    Finsupp.add_apply, hp.factorization_pow, hq.factorization_pow]
  simp [hpq]

theorem factorization_pow_mul_pow_right {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : (p ^ a * q ^ b).factorization q = b := by
  rw [mul_comm]; exact factorization_pow_mul_pow_left hq hp (Ne.symm hpq)

theorem pow_mul_pow_inj {p q a b a' b' : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : p ^ a * q ^ b = p ^ a' * q ^ b') : a = a' ∧ b = b' := by
  constructor
  · have := congrArg (fun n => n.factorization p) h
    simpa [factorization_pow_mul_pow_left hp hq hpq] using this
  · have := congrArg (fun n => n.factorization q) h
    simpa [factorization_pow_mul_pow_right hp hq hpq] using this

theorem log_pow_mul_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (a b : ℕ) :
    Real.log ((p ^ a * q ^ b : ℕ) : ℝ) = a * Real.log p + b * Real.log q := by
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
    (pow_ne_zero _ (by exact_mod_cast hq.ne_zero)), Real.log_pow, Real.log_pow]

theorem nat_eq_of_log_eq {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : Real.log x = Real.log y) : x = y := by
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.2 hx') (Set.mem_Ioi.2 hy') h

/-! ### The two-prime window lemma -/

/-- Two distinct primes `p, q` and reals `A, w > 0`: if the pigeonhole range `M`
satisfies `(log p + log q)/w ≤ M` and `A` exceeds the explicit threshold
`4 (log p + log q)(M+1)(log p + 1)(pq)^M`, then some `p^a q^b` has logarithm
in `[A, A + w]`. -/
theorem exists_two_prime_power_in_window {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {A w : ℝ} (hw : 0 < w) {M : ℕ} (hM1 : 1 ≤ M)
    (hM : (Real.log p + Real.log q) / w ≤ M)
    (hA : 4 * (Real.log p + Real.log q) * (M + 1) * (Real.log p + 1) *
      ((p * q : ℕ) : ℝ) ^ M ≤ A) :
    ∃ a b : ℕ, A ≤ a * Real.log p + b * Real.log q ∧
      a * Real.log p + b * Real.log q ≤ A + w := by
  set L := Real.log p with hLdef
  set Lq := Real.log q with hLqdef
  have hL : 0 < L := log_natPrime_pos hp
  have hLq : 0 < Lq := log_natPrime_pos hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  set X : ℝ := ((p * q : ℕ) : ℝ) ^ M with hXdef
  have hpq1 : (1 : ℝ) ≤ ((p * q : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne_zero hq.ne_zero)
  have hX1 : 1 ≤ X := one_le_pow₀ hpq1
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  -- the value function and its basic facts
  let val : ℕ → ℕ → ℝ := fun a b => a * L + b * Lq
  have hval_log : ∀ a b, val a b = Real.log ((p ^ a * q ^ b : ℕ) : ℝ) := by
    intro a b; simp only [val, hLdef, hLqdef]; rw [log_pow_mul_pow hp hq]
  have hval_inj : ∀ a b a' b', val a b = val a' b' → a = a' ∧ b = b' := by
    intro a b a' b' h
    rw [hval_log, hval_log] at h
    exact pow_mul_pow_inj hp hq hpq (nat_eq_of_log_eq
      (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _))
      (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)) h)
  have hpow_le : ∀ a b, a ≤ M → b ≤ M → ((p ^ a * q ^ b : ℕ) : ℝ) ≤ X := by
    intro a b ha hb
    have : p ^ a * q ^ b ≤ (p * q) ^ M := by
      rw [mul_pow]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right hp.pos ha) (Nat.pow_le_pow_right hq.pos hb)
    rw [hXdef]; exact_mod_cast this
  -- the key step: two values within `w` give the window
  have key : ∀ a₁ b₁ a₂ b₂ : ℕ, a₁ ≤ M → b₁ ≤ M → a₂ ≤ M → b₂ ≤ M →
      val a₁ b₁ < val a₂ b₂ → val a₂ b₂ < val a₁ b₁ + w →
      ∃ a b : ℕ, A ≤ val a b ∧ val a b ≤ A + w := by
    intro a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂ hlt hclose
    set δ := val a₂ b₂ - val a₁ b₁ with hδdef
    have hδ0 : 0 < δ := by rw [hδdef]; linarith
    have hδw : δ < w := by rw [hδdef]; linarith
    -- lower bound on the step
    have hδlow : 1 / δ ≤ X := by
      set x₁ : ℕ := p ^ a₁ * q ^ b₁ with hx₁
      set x₂ : ℕ := p ^ a₂ * q ^ b₂ with hx₂
      have hx₁0 : (0 : ℝ) < x₁ := by
        rw [hx₁]; exact_mod_cast Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
      have hx₂0 : (0 : ℝ) < x₂ := by
        rw [hx₂]; exact_mod_cast Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
      have hlog : Real.log x₁ < Real.log x₂ := by
        rw [← hval_log, ← hval_log]; exact hlt
      have hx12 : (x₁ : ℝ) < x₂ := (Real.log_lt_log_iff hx₁0 hx₂0).1 hlog
      have hx12' : (x₁ : ℝ) + 1 ≤ x₂ := by
        have : x₁ < x₂ := by exact_mod_cast hx12
        exact_mod_cast this
      have hδeq : δ = Real.log ((x₂ : ℝ) / x₁) := by
        rw [Real.log_div hx₂0.ne' hx₁0.ne', hδdef, hval_log, hval_log]
      have h1 : 1 - ((x₂ : ℝ) / x₁)⁻¹ ≤ δ := by
        rw [hδeq]; exact Real.one_sub_inv_le_log_of_pos (by positivity)
      have h2 : 1 / (x₂ : ℝ) ≤ 1 - ((x₂ : ℝ) / x₁)⁻¹ := by
        rw [inv_div, div_le_iff₀ hx₂0]
        have : (1 - (x₁ : ℝ) / x₂) * x₂ = x₂ - x₁ := by field_simp
        rw [this]; linarith
      have hX' : (x₂ : ℝ) ≤ X := hpow_le a₂ b₂ ha₂ hb₂
      calc 1 / δ ≤ 1 / (1 / (x₂ : ℝ)) := by
            apply one_div_le_one_div_of_le (by positivity); linarith
        _ = x₂ := one_div_one_div _
        _ ≤ X := hX'
    -- the base point
    set b₀ : ℕ := ⌊A / (2 * Lq)⌋₊ with hb₀def
    have hb₀le : (b₀ : ℝ) * Lq ≤ A / 2 := by
      have := Nat.floor_le (a := A / (2 * Lq)) (by positivity)
      rw [← hb₀def] at this
      calc (b₀ : ℝ) * Lq ≤ A / (2 * Lq) * Lq := by gcongr
        _ = A / 2 := by field_simp
    have hb₀gt : A / (2 * Lq) - 1 < b₀ := by
      have := Nat.lt_floor_add_one (A / (2 * Lq)); rw [← hb₀def] at this; linarith only [this]
    have hrem : 0 ≤ A - b₀ * Lq := by linarith only [hb₀le, hA0]
    set a₀ : ℕ := ⌊(A - b₀ * Lq) / L⌋₊ with ha₀def
    have ha₀le : (a₀ : ℝ) * L ≤ A - b₀ * Lq := by
      have := Nat.floor_le (a := (A - b₀ * Lq) / L) (by positivity)
      rw [← ha₀def] at this
      calc (a₀ : ℝ) * L ≤ (A - b₀ * Lq) / L * L := by gcongr
        _ = A - b₀ * Lq := by field_simp
    have ha₀gt : (A - b₀ * Lq) / L - 1 < a₀ := by
      have := Nat.lt_floor_add_one ((A - b₀ * Lq) / L); rw [← ha₀def] at this; linarith only [this]
    set v₀ : ℝ := a₀ * L + b₀ * Lq with hv₀def
    have hv₀le : v₀ ≤ A := by rw [hv₀def]; linarith only [ha₀le]
    have hv₀gt : A - L < v₀ := by
      have : (A - b₀ * Lq) / L < a₀ + 1 := by linarith only [ha₀gt]
      rw [div_lt_iff₀ hL] at this
      rw [hv₀def]; linarith only [this]
    -- the number of steps
    set m : ℕ := ⌈(A - v₀) / δ⌉₊ with hmdef
    have hm1 : A - v₀ ≤ m * δ := by
      have := Nat.le_ceil ((A - v₀) / δ); rw [← hmdef] at this
      rwa [div_le_iff₀ hδ0] at this
    have hm2 : (m : ℝ) * δ < A - v₀ + δ := by
      have := Nat.ceil_lt_add_one (a := (A - v₀) / δ) (by rw [le_div_iff₀ hδ0]; linarith only [hv₀le])
      rw [← hmdef] at this
      have := mul_lt_mul_of_pos_right this hδ0
      rwa [add_mul, div_mul_cancel₀ _ hδ0.ne', one_mul] at this
    have hmle : (m : ℝ) ≤ L * X + 1 := by
      have h1 : (m : ℝ) < (A - v₀) / δ + 1 :=
        Nat.ceil_lt_add_one (by rw [le_div_iff₀ hδ0]; linarith only [hv₀le])
      have h2 : (A - v₀) / δ ≤ L / δ := by gcongr; linarith only [hv₀gt]
      have h3 : L / δ = L * (1 / δ) := by ring
      have h4 : L * (1 / δ) ≤ L * X := by gcongr
      linarith only [h1, h2, h3, h4]
    -- the base exponents dominate the walk
    have hbase : 2 * (M + 1) * (L + 1) * X ≤ A / (2 * L) := by
      rw [le_div_iff₀ (by positivity)]
      calc 2 * (M + 1) * (L + 1) * X * (2 * L) = 4 * L * (M + 1) * (L + 1) * X := by ring
        _ ≤ 4 * (L + Lq) * (M + 1) * (L + 1) * X := by gcongr; linarith
        _ ≤ A := hA
    have hbase' : 2 * (M + 1) * (L + 1) * X ≤ A / (2 * Lq) := by
      rw [le_div_iff₀ (by positivity)]
      calc 2 * (M + 1) * (L + 1) * X * (2 * Lq) = 4 * Lq * (M + 1) * (L + 1) * X := by ring
        _ ≤ 4 * (L + Lq) * (M + 1) * (L + 1) * X := by gcongr; linarith
        _ ≤ A := hA
    have hwalk : (L * X + 1) * M ≤ 2 * (M + 1) * (L + 1) * X - 1 := by
      nlinarith [mul_nonneg hL.le (sub_nonneg.2 hX1), mul_nonneg (sub_nonneg.2 hM1') hL.le,
        mul_nonneg (sub_nonneg.2 hM1') (sub_nonneg.2 hX1), hL, hX1, hM1']
    have ha₀big : (m : ℝ) * a₁ ≤ a₀ := by
      have h1 : A / (2 * L) ≤ (A - b₀ * Lq) / L := by
        have e : A / (2 * L) = A / 2 / L := by rw [div_div]
        rw [e]
        exact div_le_div_of_nonneg_right (by linarith only [hb₀le]) hL.le
      have h2 : (a₁ : ℝ) ≤ M := by exact_mod_cast ha₁
      have h3 : (m : ℝ) * a₁ ≤ (L * X + 1) * M := by
        apply mul_le_mul hmle h2 (by positivity) (by positivity)
      linarith only [h3, hwalk, hbase, h1, ha₀gt]
    have hb₀big : (m : ℝ) * b₁ ≤ b₀ := by
      have h2 : (b₁ : ℝ) ≤ M := by exact_mod_cast hb₁
      have h3 : (m : ℝ) * b₁ ≤ (L * X + 1) * M := by
        apply mul_le_mul hmle h2 (by positivity) (by positivity)
      linarith only [h3, hwalk, hbase', hb₀gt]
    have ha₀big' : m * a₁ ≤ a₀ := by exact_mod_cast ha₀big
    have hb₀big' : m * b₁ ≤ b₀ := by exact_mod_cast hb₀big
    refine ⟨a₀ - m * a₁ + m * a₂, b₀ - m * b₁ + m * b₂, ?_⟩
    have hval : val (a₀ - m * a₁ + m * a₂) (b₀ - m * b₁ + m * b₂) = v₀ + m * δ := by
      simp only [val]
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub ha₀big', Nat.cast_sub hb₀big']
      push_cast
      rw [hv₀def, hδdef]; simp only [val]; ring
    rw [hval]
    constructor
    · linarith only [hm1]
    · linarith only [hm2, hv₀le, hδw]
  -- pigeonhole on the values in `[0, M (L + Lq)]`
  classical
  let f : Fin (M + 1) × Fin (M + 1) → ℕ := fun x => ⌊val x.1 x.2 / w⌋₊
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Fin (M + 1) × Fin (M + 1))),
      f x ∈ Finset.range (M * M + 1) := by
    intro x _
    simp only [f, Finset.mem_range]
    have hx1 : (x.1 : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.1 x.1.isLt
    have hx2 : (x.2 : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.1 x.2.isLt
    have hv : val x.1 x.2 ≤ M * (L + Lq) := by
      simp only [val]; nlinarith
    have hLw : L + Lq ≤ M * w := by
      rw [div_le_iff₀ hw] at hM; exact hM
    have : val x.1 x.2 / w ≤ ((M * M : ℕ) : ℝ) := by
      rw [div_le_iff₀ hw]; push_cast
      calc val x.1 x.2 ≤ M * (L + Lq) := hv
        _ ≤ M * (M * w) := by gcongr
        _ = M * M * w := by ring
    have h := Nat.floor_le_floor this
    rw [Nat.floor_natCast] at h
    omega
  have hcard : (Finset.range (M * M + 1)).card <
      (Finset.univ : Finset (Fin (M + 1) × Fin (M + 1))).card := by
    rw [Finset.card_range, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    nlinarith
  obtain ⟨x, -, y, -, hxy, hfxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hclose : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → ⌊u / w⌋₊ = ⌊v / w⌋₊ → u < v + w := by
    intro u v hu hv h
    have h1 : u / w < ⌊u / w⌋₊ + 1 := Nat.lt_floor_add_one _
    have h2 : (⌊v / w⌋₊ : ℝ) ≤ v / w := Nat.floor_le (by positivity)
    rw [h] at h1
    have : u / w < v / w + 1 := by linarith
    rw [div_lt_iff₀ hw, add_mul, div_mul_cancel₀ _ hw.ne', one_mul] at this
    exact this
  have hvx : 0 ≤ val x.1 x.2 := by simp only [val]; positivity
  have hvy : 0 ≤ val y.1 y.2 := by simp only [val]; positivity
  have hne : val x.1 x.2 ≠ val y.1 y.2 := by
    intro h
    obtain ⟨h1, h2⟩ := hval_inj _ _ _ _ h
    exact hxy (Prod.ext (Fin.ext h1) (Fin.ext h2))
  have hx1 : (x.1 : ℕ) ≤ M := Nat.lt_succ_iff.1 x.1.isLt
  have hx2 : (x.2 : ℕ) ≤ M := Nat.lt_succ_iff.1 x.2.isLt
  have hy1 : (y.1 : ℕ) ≤ M := Nat.lt_succ_iff.1 y.1.isLt
  have hy2 : (y.2 : ℕ) ≤ M := Nat.lt_succ_iff.1 y.2.isLt
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact key x.1 x.2 y.1 y.2 hx1 hx2 hy1 hy2 hlt (hclose _ _ hvy hvx hfxy.symm)
  · exact key y.1 y.2 x.1 x.2 hy1 hy2 hx1 hx2 hgt (hclose _ _ hvx hvy hfxy)

/-! ### An odd modulus in a window -/

/-- For distinct odd primes `p, q`, every window `((1 − 2η) t, (1 − η) t]` with
`η ≤ 1/8` contains a number of the form `p^a q^b`, once `log t` exceeds the
explicit threshold determined by the pigeonhole range `M ≥ 3 (log p + log q)/η`. -/
theorem exists_odd_modulus_in_window {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (t : ℕ) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 8) {M : ℕ} (hM1 : 1 ≤ M)
    (hM : 3 * (Real.log p + Real.log q) / η ≤ M)
    (ht : 1 + 4 * (Real.log p + Real.log q) * (M + 1) * (Real.log p + 1) *
      ((p * q : ℕ) : ℝ) ^ M ≤ Real.log t) :
    ∃ s : ℕ, 0 < s ∧ (∀ r : ℕ, r.Prime → r ∣ s → r = p ∨ r = q) ∧
      (1 - 2 * η) * t < s ∧ (s : ℝ) ≤ (1 - η) * t := by
  set X : ℝ := 4 * (Real.log p + Real.log q) * (M + 1) * (Real.log p + 1) *
    ((p * q : ℕ) : ℝ) ^ M with hXdef
  have hL := log_natPrime_pos hp
  have hLq := log_natPrime_pos hq
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have ht0 : (0 : ℝ) < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; simp only [Nat.cast_zero, Real.log_zero] at ht; linarith
    · exact_mod_cast h
  have h1 : (0 : ℝ) < 1 - 2 * η := by linarith
  have h2 : (0 : ℝ) < 1 - η := by linarith
  -- the window in logarithmic coordinates
  have hlog1 : -1 ≤ Real.log (1 - 2 * η) := by
    have := Real.one_sub_inv_le_log_of_pos h1
    have : (1 - 2 * η)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ h1 (by norm_num)]; linarith
    linarith
  have hw : η ≤ Real.log (1 - η) - Real.log (1 - 2 * η) := by
    rw [← Real.log_div h2.ne' h1.ne']
    have := Real.one_sub_inv_le_log_of_pos (x := (1 - η) / (1 - 2 * η)) (by positivity)
    rw [inv_div] at this
    have h3 : (1 - 2 * η) / (1 - η) ≤ 1 - η := by
      rw [div_le_iff₀ h2]; nlinarith
    linarith
  set A₁ : ℝ := Real.log ((1 - 2 * η) * t) + η / 3 with hA₁def
  have hA₁ : X ≤ A₁ := by
    rw [hA₁def, Real.log_mul h1.ne' ht0.ne']
    linarith
  have hw3 : (0 : ℝ) < η / 3 := by positivity
  have hM' : (Real.log p + Real.log q) / (η / 3) ≤ M := by
    rw [div_div_eq_mul_div]
    calc (Real.log p + Real.log q) * 3 / η = 3 * (Real.log p + Real.log q) / η := by ring
      _ ≤ M := hM
  obtain ⟨a, b, hab1, hab2⟩ :=
    exists_two_prime_power_in_window hp hq hpq hw3 hM1 hM' hA₁
  refine ⟨p ^ a * q ^ b, Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _), ?_, ?_, ?_⟩
  · intro r hr hdvd
    rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow h))
  · have hs0 : (0 : ℝ) < ((p ^ a * q ^ b : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
    rw [← Real.log_lt_log_iff (by positivity) hs0, log_pow_mul_pow hp hq]
    linarith
  · have hs0 : (0 : ℝ) < ((p ^ a * q ^ b : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
    rw [← Real.log_le_log_iff hs0 (by positivity), log_pow_mul_pow hp hq,
      Real.log_mul h2.ne' ht0.ne']
    rw [hA₁def, Real.log_mul h1.ne' ht0.ne'] at hab2
    linarith

/-! ### The coordinate primes -/

/-- The first odd prime assigned to coordinate `i`. -/
noncomputable def coordPrime₁ (i : ℕ) : ℕ := primeChain 2 (2 * i + 1)

/-- The second odd prime assigned to coordinate `i`. -/
noncomputable def coordPrime₂ (i : ℕ) : ℕ := primeChain 2 (2 * i + 2)

theorem coordPrime₁_prime (i : ℕ) : (coordPrime₁ i).Prime := primeChain_prime (by norm_num) _

theorem coordPrime₂_prime (i : ℕ) : (coordPrime₂ i).Prime := primeChain_prime (by norm_num) _

theorem two_lt_coordPrime₁ (i : ℕ) : 2 < coordPrime₁ i := primeChain_gt (by norm_num) _

theorem two_lt_coordPrime₂ (i : ℕ) : 2 < coordPrime₂ i := primeChain_gt (by norm_num) _

theorem coordPrime_ne (i : ℕ) : coordPrime₁ i ≠ coordPrime₂ i :=
  (primeChain_strictMono (by norm_num) (show 2 * i + 1 < 2 * i + 2 by omega)).ne

theorem coordPrime₁_le {d i : ℕ} (hi : i < d) : coordPrime₁ i ≤ 2 ^ (2 * d + 1) := by
  calc coordPrime₁ i ≤ 2 ^ (2 * i + 1) * 2 := primeChain_le (by norm_num) _
    _ = 2 ^ (2 * i + 2) := by ring
    _ ≤ 2 ^ (2 * d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem coordPrime₂_le {d i : ℕ} (hi : i < d) : coordPrime₂ i ≤ 2 ^ (2 * d + 1) := by
  calc coordPrime₂ i ≤ 2 ^ (2 * i + 2) * 2 := primeChain_le (by norm_num) _
    _ = 2 ^ (2 * i + 3) := by ring
    _ ≤ 2 ^ (2 * d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The coordinate primes of distinct coordinates are distinct. -/
theorem coordPrime_disjoint {i j : ℕ} (hij : i ≠ j) :
    coordPrime₁ i ≠ coordPrime₁ j ∧ coordPrime₁ i ≠ coordPrime₂ j ∧
      coordPrime₂ i ≠ coordPrime₁ j ∧ coordPrime₂ i ≠ coordPrime₂ j := by
  have hinj := (primeChain_strictMono (x := 2) (by norm_num)).injective
  refine ⟨fun h => hij ?_, fun h => hij ?_, fun h => hij ?_, fun h => hij ?_⟩ <;>
    have := hinj h <;> omega

theorem log_le_of_le_two_pow {p k : ℕ} (hp : 0 < p) (h : p ≤ 2 ^ k) : Real.log p ≤ k := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  calc Real.log p ≤ Real.log ((2 : ℝ) ^ k) := by
        apply Real.log_le_log hp'; exact_mod_cast h
    _ = k * Real.log 2 := by rw [Real.log_pow]
    _ ≤ k * 1 := by
        gcongr
        have := Real.log_two_lt_d9; linarith
    _ = k := mul_one _

/-! ### The numerical threshold -/

theorem nat_le_two_pow (d : ℕ) : d ≤ 2 ^ d := (Nat.lt_two_pow_self).le

/-- The explicit threshold of the window lemma at the coordinate primes is below
`2^(500 d³)`. -/
theorem threshold_nat_le {d : ℕ} (hd : 1 ≤ d) :
    4 * (4 * d + 2) * (12 * d * (4 * d + 2) + 1) * (2 * d + 2) *
      2 ^ ((4 * d + 2) * (12 * d * (4 * d + 2))) + 1 ≤ 2 ^ (500 * d ^ 3) := by
  have hd2 := nat_le_two_pow d
  have hd2' : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
  have h1 : 4 * d + 2 ≤ 2 ^ (d + 2) := by
    rw [pow_add]; norm_num; omega
  have h2 : 12 * d * (4 * d + 2) + 1 ≤ 2 ^ (2 * d + 7) := by
    have : d * d ≤ 2 ^ (2 * d) := by
      rw [two_mul, pow_add]; exact Nat.mul_le_mul hd2 hd2
    calc 12 * d * (4 * d + 2) + 1 = 48 * (d * d) + 24 * d + 1 := by ring
      _ ≤ 48 * (d * d) + 24 * (d * d) + 1 * (d * d) := by nlinarith
      _ = 73 * (d * d) := by ring
      _ ≤ 128 * 2 ^ (2 * d) := by nlinarith
      _ = 2 ^ (2 * d + 7) := by rw [pow_add]; ring
  have h3 : 2 * d + 2 ≤ 2 ^ (d + 2) := by
    rw [pow_add]; norm_num; omega
  have hpre : 4 * (4 * d + 2) * (12 * d * (4 * d + 2) + 1) * (2 * d + 2) ≤ 2 ^ (4 * d + 13) := by
    calc 4 * (4 * d + 2) * (12 * d * (4 * d + 2) + 1) * (2 * d + 2)
        ≤ 4 * 2 ^ (d + 2) * 2 ^ (2 * d + 7) * 2 ^ (d + 2) := by gcongr
      _ = 2 ^ (4 * d + 13) := by
          rw [show 4 = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add]; ring_nf
  set E := (4 * d + 2) * (12 * d * (4 * d + 2)) with hE
  have hE' : E + 4 * d + 14 ≤ 500 * d ^ 3 := by
    have : 4 * d + 2 ≤ 6 * d := by omega
    have hE1 : E ≤ 432 * d ^ 3 := by
      rw [hE]
      calc (4 * d + 2) * (12 * d * (4 * d + 2)) ≤ 6 * d * (12 * d * (6 * d)) := by gcongr
        _ = 432 * d ^ 3 := by ring
    have : 4 * d + 14 ≤ 18 * d ^ 3 := by nlinarith [Nat.one_le_pow 3 d hd]
    omega
  calc 4 * (4 * d + 2) * (12 * d * (4 * d + 2) + 1) * (2 * d + 2) * 2 ^ E + 1
      ≤ 2 ^ (4 * d + 13) * 2 ^ E + 1 := by gcongr
    _ = 2 ^ (E + 4 * d + 13) + 1 := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (E + 4 * d + 13) + 2 ^ (E + 4 * d + 13) := by
        have := Nat.one_le_two_pow (n := E + 4 * d + 13); omega
    _ = 2 ^ (E + 4 * d + 14) := by ring
    _ ≤ 2 ^ (500 * d ^ 3) := Nat.pow_le_pow_right (by norm_num) hE'

/-- The real-valued threshold of the window lemma at coordinate `i < d`, with
`M = 12 d (4 d + 2)`, is at most `2^(500 d³)`. -/
theorem threshold_real_le {d i : ℕ} (hd : 1 ≤ d) (hi : i < d) :
    1 + 4 * (Real.log (coordPrime₁ i) + Real.log (coordPrime₂ i)) *
      ((12 * d * (4 * d + 2) : ℕ) + 1) * (Real.log (coordPrime₁ i) + 1) *
      ((coordPrime₁ i * coordPrime₂ i : ℕ) : ℝ) ^ (12 * d * (4 * d + 2))
      ≤ (2 : ℝ) ^ (500 * d ^ 3) := by
  have hp := coordPrime₁_prime i
  have hq := coordPrime₂_prime i
  have hL : 0 < Real.log (coordPrime₁ i) := log_natPrime_pos hp
  have hLq : 0 < Real.log (coordPrime₂ i) := log_natPrime_pos hq
  have hL1 : Real.log (coordPrime₁ i) ≤ 2 * d + 1 := by
    have := log_le_of_le_two_pow hp.pos (coordPrime₁_le hi); exact_mod_cast this
  have hL2 : Real.log (coordPrime₂ i) ≤ 2 * d + 1 := by
    have := log_le_of_le_two_pow hq.pos (coordPrime₂_le hi); exact_mod_cast this
  have hpq : coordPrime₁ i * coordPrime₂ i ≤ 2 ^ (4 * d + 2) := by
    calc coordPrime₁ i * coordPrime₂ i ≤ 2 ^ (2 * d + 1) * 2 ^ (2 * d + 1) :=
          Nat.mul_le_mul (coordPrime₁_le hi) (coordPrime₂_le hi)
      _ = 2 ^ (4 * d + 2) := by rw [← pow_add]; ring_nf
  set M := 12 * d * (4 * d + 2) with hM
  have hpqR : ((coordPrime₁ i * coordPrime₂ i : ℕ) : ℝ) ^ M ≤ (2 : ℝ) ^ ((4 * d + 2) * M) := by
    rw [pow_mul (2 : ℝ) (4 * d + 2) M]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hpq) M
  have hnat := threshold_nat_le hd
  have hcast : ((4 * (4 * d + 2) * (12 * d * (4 * d + 2) + 1) * (2 * d + 2) *
      2 ^ ((4 * d + 2) * (12 * d * (4 * d + 2))) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (500 * d ^ 3) := by
    exact_mod_cast hnat
  push_cast at hcast
  have hMR : (M : ℝ) = 12 * (d : ℝ) * (4 * (d : ℝ) + 2) := by rw [hM]; push_cast; ring
  rw [← hM, ← hMR] at hcast
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  calc 1 + 4 * (Real.log (coordPrime₁ i) + Real.log (coordPrime₂ i)) * ((M : ℕ) + 1) *
        (Real.log (coordPrime₁ i) + 1) * ((coordPrime₁ i * coordPrime₂ i : ℕ) : ℝ) ^ M
      ≤ 1 + 4 * ((2 * d + 1) + (2 * d + 1)) * ((M : ℕ) + 1) * ((2 * d + 1) + 1) *
        (2 : ℝ) ^ ((4 * d + 2) * M) := by gcongr
    _ = 4 * (4 * d + 2) * (M + 1) * (2 * d + 2) * 2 ^ ((4 * d + 2) * M) + 1 := by ring
    _ ≤ 2 ^ (500 * d ^ 3) := hcast

/-- `log t ≥ 2^(500 d³)` whenever `t ≥ 2^(2^(500 d³ + 1))`. -/
theorem log_ge_of_ge_two_pow_two_pow {d t : ℕ} (ht : 2 ^ (2 ^ (500 * d ^ 3 + 1)) ≤ t) :
    (2 : ℝ) ^ (500 * d ^ 3) ≤ Real.log t := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ (500 * d ^ 3 + 1)) := by positivity
  calc (2 : ℝ) ^ (500 * d ^ 3) = (2 : ℝ) ^ (500 * d ^ 3 + 1) * (1 / 2) := by
        rw [pow_succ]; ring
    _ ≤ (2 : ℝ) ^ (500 * d ^ 3 + 1) * Real.log 2 := by gcongr; linarith
    _ = Real.log ((2 : ℝ) ^ (2 ^ (500 * d ^ 3 + 1))) := by
        rw [Real.log_pow]; push_cast; ring
    _ ≤ Real.log t := by
        apply Real.log_le_log hpos
        exact_mod_cast ht

/-! ### Pairwise coprime odd moduli -/

/-- For `d ≥ 2` and any grid of lengths at least `2^(2^(500 d³ + 1))`, there are
pairwise coprime odd moduli in the windows `((1 − 1/(2d)) t_i, (1 − 1/(4d)) t_i]`. -/
theorem exists_moduli_elementary {d : ℕ} (hd : 2 ≤ d) (t : Fin d → ℕ)
    (hbig : ∀ i, 2 ^ (2 ^ (500 * d ^ 3 + 1)) ≤ t i) :
    ∃ s : Fin d → ℕ, (∀ i, 0 < s i) ∧ (∀ i, ¬ 2 ∣ s i) ∧
      Pairwise (Function.onFun Nat.Coprime s) ∧
      ∀ i, (1 - 1 / (2 * (d : ℝ))) * t i < s i ∧ (s i : ℝ) ≤ (1 - 1 / (4 * (d : ℝ))) * t i := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hη0 : (0 : ℝ) < 1 / (4 * (d : ℝ)) := by positivity
  have hη : (1 : ℝ) / (4 * (d : ℝ)) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set M := 12 * d * (4 * d + 2) with hM
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith
  -- the per-coordinate choice
  have hchoice : ∀ i : Fin d, ∃ s : ℕ, 0 < s ∧
      (∀ r : ℕ, r.Prime → r ∣ s → r = coordPrime₁ i ∨ r = coordPrime₂ i) ∧
      (1 - 2 * (1 / (4 * (d : ℝ)))) * t i < s ∧ (s : ℝ) ≤ (1 - 1 / (4 * (d : ℝ))) * t i := by
    intro i
    have hp := coordPrime₁_prime i
    have hq := coordPrime₂_prime i
    have hL1 : Real.log (coordPrime₁ i) ≤ 2 * d + 1 := by
      have := log_le_of_le_two_pow hp.pos (coordPrime₁_le i.isLt); exact_mod_cast this
    have hL2 : Real.log (coordPrime₂ i) ≤ 2 * d + 1 := by
      have := log_le_of_le_two_pow hq.pos (coordPrime₂_le i.isLt); exact_mod_cast this
    have hMR : 3 * (Real.log (coordPrime₁ i) + Real.log (coordPrime₂ i)) / (1 / (4 * (d : ℝ)))
        ≤ M := by
      rw [div_div_eq_mul_div, div_one]
      have : (M : ℝ) = 12 * d * (4 * d + 2) := by rw [hM]; push_cast; ring
      rw [this]; nlinarith
    have hthr := threshold_real_le hd1 i.isLt
    have hlog := log_ge_of_ge_two_pow_two_pow (hbig i)
    rw [← hM] at hthr
    exact exists_odd_modulus_in_window hp hq (coordPrime_ne i) (t i) hη0 hη hM1 hMR
      (by push_cast at hthr ⊢; linarith)
  choose s hs0 hsdvd hslo hshi using hchoice
  refine ⟨s, hs0, ?_, ?_, ?_⟩
  · intro i h2
    rcases hsdvd i 2 Nat.prime_two h2 with h | h
    · have := two_lt_coordPrime₁ i; omega
    · have := two_lt_coordPrime₂ i; omega
  · intro i j hij
    -- all prime factors of `s i` and `s j` are distinct
    have hdis := coordPrime_disjoint (show (i : ℕ) ≠ j from fun h => hij (Fin.ext h))
    apply Nat.coprime_of_dvd
    intro r hr hri hrj
    rcases hsdvd i r hr hri with h | h <;> rcases hsdvd j r hr hrj with h' | h' <;>
      [exact hdis.1 (h ▸ h'); exact hdis.2.1 (h ▸ h'); exact hdis.2.2.1 (h ▸ h');
        exact hdis.2.2.2 (h ▸ h')]
  · intro i
    refine ⟨?_, hshi i⟩
    have := hslo i
    have e : (1 - 2 * (1 / (4 * (d : ℝ)))) = 1 - 1 / (2 * (d : ℝ)) := by field_simp; ring
    rw [e] at this; exact this

/-! ### The conditions of the recursive-step contract, from oddness alone -/

theorem t_ge_512_of_big {d t : ℕ} (hd : 2 ≤ d) (ht : 2 ^ (2 ^ (500 * d ^ 3 + 1)) ≤ t) :
    512 ≤ t := by
  have h1 : 9 ≤ 2 ^ (500 * d ^ 3 + 1) := by
    calc 9 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (500 * d ^ 3 + 1) := Nat.pow_le_pow_right (by norm_num)
          (by have := Nat.pow_le_pow_left hd 3; omega)
  calc 512 = 2 ^ 9 := by norm_num
    _ ≤ 2 ^ (2 ^ (500 * d ^ 3 + 1)) := Nat.pow_le_pow_right (by norm_num) h1
    _ ≤ t := ht

/-- `moduli_conditions` with primality replaced by positivity, oddness, and
pairwise coprimality, which is all its proof uses. -/
theorem moduli_conditions_elementary {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n)
    (t s : Fin d → ℕ) (hpow : ∀ i, ∃ k, t i = 2 ^ k)
    (hbig : ∀ i, 2 ^ (2 ^ (500 * d ^ 3 + 1)) ≤ t i)
    (hs0 : ∀ i, 0 < s i) (hodd : ∀ i, ¬ 2 ∣ s i) (hcop : Pairwise (Function.onFun Nat.Coprime s))
    (hwin : ∀ i, (1 - 1 / (2 * (d : ℝ))) * t i < s i ∧
      (s i : ℝ) ≤ (1 - 1 / (4 * (d : ℝ))) * t i) :
    (∀ i, s i < t i) ∧ ∏ i, s i ≤ ∏ i, t i ∧ ∏ i, t i < 2 * ∏ i, s i ∧
      Pairwise (Function.onFun Nat.Coprime s) ∧ (∀ i, Nat.Coprime (s i) (t i)) ∧
      ∀ i, 1 ≤ ((alphaParam d n : ℕ) : ℝ) ^ 2 * ((t i : ℝ) / (s i) - 1) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht512 : ∀ i, 512 ≤ t i := fun i => t_ge_512_of_big hd (hbig i)
  have hti0 : ∀ i, 0 < t i := fun i => by have := ht512 i; omega
  have hst : ∀ i, s i < t i := by
    intro i
    have h := (hwin i).2
    have htR : (0 : ℝ) < t i := by exact_mod_cast hti0 i
    have : (s i : ℝ) < t i := by
      have : 1 / (4 * (d : ℝ)) * t i > 0 := by positivity
      nlinarith
    exact_mod_cast this
  refine ⟨hst, Finset.prod_le_prod fun i _ => (hst i).le, ?_, hcop, ?_, ?_⟩
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
  · intro i
    obtain ⟨k, hk⟩ := hpow i
    rw [hk]
    apply Nat.Coprime.pow_right
    exact Nat.coprime_two_right.2 (Nat.not_even_iff_odd.1 fun h => hodd i (even_iff_two_dvd.1 h))
  · intro i
    have hα : (4 * (d : ℝ)) ≤ ((alphaParam d n : ℕ) : ℝ) := by
      exact_mod_cast four_d_le_alpha hd hn
    have hA : 16 * (d : ℝ) ^ 2 ≤ ((alphaParam d n : ℕ) : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hα 2
      nlinarith
    have hs0' : (0 : ℝ) < s i := by exact_mod_cast hs0 i
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
    rw [div_sub_one hs0'.ne', ← mul_div_assoc, le_div_iff₀ hs0', one_mul]
    exact hmain

/-! ### The threshold on `n` -/

theorem pow_twelve_le_two_pow {d : ℕ} (hd : 1 ≤ d) : d ^ 12 ≤ 2 ^ (1000 * d ^ 3) := by
  calc d ^ 12 ≤ (2 ^ d) ^ 12 := Nat.pow_le_pow_left (nat_le_two_pow d) 12
    _ = 2 ^ (d * 12) := by rw [← pow_mul]
    _ ≤ 2 ^ (1000 * d ^ 3) := Nat.pow_le_pow_right (by norm_num)
          (by have := Nat.le_self_pow (show 3 ≠ 0 by norm_num) d; omega)

/-- Above the threshold `2^(2^(1000 d³))`, the grid exponent `rootExp` is at least
`2^(500 d³ + 1) + 1`. -/
theorem rootExp_ge_of_big {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (2 ^ (1000 * d ^ 3)) ≤ n) :
    2 ^ (500 * d ^ 3 + 1) + 1 ≤ rootExp d n := by
  have hd1 : 1 ≤ d := by omega
  have hn12 : 2 ^ (d ^ 12) ≤ n :=
    (Nat.pow_le_pow_right (by norm_num) (pow_twelve_le_two_pow hd1)).trans hn
  have hL : 2 ^ (1000 * d ^ 3) ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hT := transformExp_gt hd hn12
  set K := 500 * d ^ 3 with hK
  have hK3 : d + 3 ≤ K := by
    rw [hK]
    have h1 := Nat.le_self_pow (show 3 ≠ 0 by norm_num) d
    have h2 : 2 ^ 3 ≤ d ^ 3 := Nat.pow_le_pow_left hd 3
    omega
  have h2K : 1000 * d ^ 3 = 2 * K := by rw [hK]; ring
  rw [h2K] at hL
  -- `log₂ n / 2 ≥ 2^(2K − 1)`
  have hhalf : 2 ^ (2 * K - 1) ≤ Nat.log 2 n / 2 := by
    have e : 2 ^ (2 * K) = 2 ^ (2 * K - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    have : 2 ^ (2 * K - 1) * 2 / 2 ≤ Nat.log 2 n / 2 :=
      Nat.div_le_div_right (by rw [← e]; exact hL)
    rwa [Nat.mul_div_cancel _ (by norm_num)] at this
  have hTE : 2 ^ (2 * K - 1) + 3 ≤ transformExp n := by omega
  -- `rootExp ≥ transformExp / d`
  have hdiv : transformExp n / d ≤ rootExp d n := by
    unfold rootExp
    exact Nat.div_le_div_right (by omega)
  have hmul : (2 ^ (K + 1) + 1) * d ≤ transformExp n := by
    have hd2 := nat_le_two_pow d
    calc (2 ^ (K + 1) + 1) * d ≤ (2 ^ (K + 1) + 1) * 2 ^ d := Nat.mul_le_mul_left _ hd2
      _ = 2 ^ (K + 1 + d) + 2 ^ d := by rw [add_mul, one_mul, ← pow_add]
      _ ≤ 2 ^ (K + 1 + d) + 2 ^ (K + 1 + d) := by
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show d ≤ K + 1 + d by omega)
          omega
      _ = 2 ^ (K + 2 + d) := by rw [← two_mul, ← pow_succ']; congr 1; omega
      _ ≤ 2 ^ (2 * K - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ transformExp n := by omega
  have : 2 ^ (K + 1) + 1 ≤ transformExp n / d :=
    (Nat.le_div_iff_mul_le (by omega)).2 hmul
  omega

/-! ### The headline theorem -/

/-- For `d = d' + 1 ≥ 2` and `n ≥ 2^(2^(1000 d³))`, there are a power-of-two grid
and pairwise coprime odd moduli, constructed without any unproved input, for
which the explicit numerical recursive step returns the exact product of any two
`n`-bit inputs, for every admissible rounding oracle. -/
theorem nlogn_step_unconditional {d' n : ℕ} (hd' : 1 ≤ d')
    (hn : 2 ^ (2 ^ (1000 * (d' + 1) ^ 3)) ≤ n) {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n) :
    ∃ (e : Fin d' → ℕ) (g : ℕ) (s : Fin (d' + 1) → ℕ) (_ : ∀ i, NeZero (s i))
      (hs : Pairwise (Function.onFun Nat.Coprime s))
      (hcop : ∀ i, Nat.Coprime (s i) (lenAll (Mof e g) i)),
      (∀ i, ¬ 2 ∣ s i) ∧ (∀ i, s i < lenOf e g i) ∧
      ∀ (E₁ E₂ E₃ : (i : Fin d') → (m : ℕ) → Fin (2 ^ (m + 1)) →
          (Fin (lenLast (Mof e g)) → ℂ)),
        (∀ i m k, ‖E₁ i m k‖ ≤ 1 / 2 ^ precision n) →
        (∀ i m k, ‖E₂ i m k‖ ≤ 1 / 2 ^ precision n) →
        (∀ i m k, ‖E₃ i m k‖ ≤ 1 / 2 ^ precision n) →
        recursiveStepOutput n e g s hs hcop E₁ E₂ E₃ x y
          = Machine.binaryValue x * Machine.binaryValue y := by
  have hd : 2 ≤ d' + 1 := by omega
  have hn12 : 2 ^ ((d' + 1) ^ 12) ≤ n :=
    (Nat.pow_le_pow_right (by norm_num) (pow_twelve_le_two_pow (by omega))).trans hn
  obtain ⟨e, g, he, hg, hdiv, hT, hlow⟩ := exists_grid_lower (by omega) hn12
  have hk := rootExp_ge_of_big (d := d' + 1) hd hn
  have hbig : ∀ i, 2 ^ (2 ^ (500 * (d' + 1) ^ 3 + 1)) ≤ lenOf e g i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (hlow i)
  have hpow : ∀ i, ∃ k, lenOf e g i = 2 ^ k := fun i => ⟨_, rfl⟩
  obtain ⟨s, hs0, hodd, hcop, hwin⟩ := exists_moduli_elementary hd (lenOf e g) hbig
  obtain ⟨hst, hS, hS2, hs, hcopt, hθ⟩ :=
    moduli_conditions_elementary hd hn12 (lenOf e g) s hpow hbig hs0 hodd hcop hwin
  have : ∀ i, NeZero (s i) := fun i => ⟨(hs0 i).ne'⟩
  rw [hT] at hS hS2
  refine ⟨e, g, s, inferInstance, hs, by rw [lenAll_Mof]; exact hcopt, hodd, hst, ?_⟩
  intro E₁ E₂ E₃ hE₁ hE₂ hE₃
  exact recursive_step_correct (by omega) hn12 hx hy e g he hg hdiv hT s hs hS hS2 hst hcopt hθ
    E₁ E₂ E₃ hE₁ hE₂ hE₃

end IntegerMultBounds.NLogN
