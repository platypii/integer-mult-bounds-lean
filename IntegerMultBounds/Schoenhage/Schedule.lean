import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! The size schedule and cost recurrence of the Schönhage–Strassen recursion.
A level with ring size `N` (modulus `2^N + 1`) uses `K = 2^k` pieces with
`k = kOf N = (s - size s) / 2`, `s = bitlen N`, piece size `M = N / K` and next
ring size `nextN N`, the multiple of `K` just above `2M + k + 1`; every
quantity is a bit length, halving or rounding, so it can be computed on
tapes. Below `N0 = 2^2047` (bit length below `2048`) the base case is used.
Proved: `kOf` is monotone and the divisibility `2^k ∣ N` propagates down the
recursion (`dvd_next`); above the threshold `1 ≤ k`, `2M + k + 1 ≤ N'` (the
hypothesis of `level_correct`) and `2 N' ≤ N` (`next_facts`); the growth of
the total size per level is `2 + O(1/s)` (`growth`); the recurrence `cost`
with base cost `C0 (N+1)^2`, transform cost `A K (N'+1)(k+1)` and level
overhead `B (N+1)(s+1)` is at most `C (N+1)(s+1)(size (s^3) + 1)` with
`C = C0 2^2048 + 16 A + 2 B` (`cost_le`), i.e. `O(N log N log log N)`; and
for `m ≥ 1` input bits the power of two `topN m ∈ (2m, 4m]` is a valid
top-level ring size (`topN_facts`, `cost_topN`). -/

namespace IntegerMultBounds.Schoenhage.Schedule

/-- Bit length (number of halvings to zero). -/
def bitlen (N : ℕ) : ℕ := Nat.size N

/-- The level's transform exponent: about `(log N - log log N) / 2`. -/
def kOf (N : ℕ) : ℕ := (bitlen N - bitlen (bitlen N)) / 2

/-- Piece size `N / 2^k`. -/
def pieceOf (N : ℕ) : ℕ := N / 2 ^ kOf N

/-- The next ring size: `2M + k + 1` rounded up to a multiple of `2^k`. -/
def nextN (N : ℕ) : ℕ :=
  2 ^ kOf N * ((2 * pieceOf N + kOf N + 1 + 2 ^ kOf N - 1) / 2 ^ kOf N)

/-- The bit-length threshold of the recursion. -/
@[irreducible] def S0 : ℕ := 2048

theorem S0_eq : S0 = 2048 := by unfold S0; rfl

/-- Ring sizes below `N0` use the base case. -/
@[irreducible] def N0 : ℕ := 2 ^ (S0 - 1)

theorem N0_eq : N0 = 2 ^ (S0 - 1) := by unfold N0; rfl

/-! ### Bit-length facts -/

theorem size_succ_le (x : ℕ) : Nat.size (x + 1) ≤ Nat.size x + 1 := by
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self x
  have : 1 ≤ 2 ^ Nat.size x := Nat.one_le_two_pow
  omega

theorem size_add_le (x d : ℕ) : Nat.size (x + d) ≤ Nat.size x + d := by
  induction d with
  | zero => simp
  | succ d ih => have := size_succ_le (x + d); rw [← add_assoc]; omega

theorem sub_size_mono {a b : ℕ} (h : a ≤ b) : a - Nat.size a ≤ b - Nat.size b := by
  have := size_add_le a (b - a)
  rw [Nat.add_sub_cancel' h] at this
  omega

theorem kOf_mono {N N' : ℕ} (h : N' ≤ N) : kOf N' ≤ kOf N := by
  unfold kOf bitlen
  exact Nat.div_le_div_right (sub_size_mono (Nat.size_le_size h))

theorem two_pow_pred_le {n : ℕ} (h : 0 < n) : 2 ^ (Nat.size n - 1) ≤ n := by
  rw [← Nat.lt_size]; have := Nat.size_pos.mpr h; omega

theorem size_succ_of_double {x y : ℕ} (hx : 0 < x) (h : 2 * x ≤ y) : Nat.size x + 1 ≤ Nat.size y := by
  have h1 := two_pow_pred_le hx
  have hs := Nat.size_pos.mpr hx
  have : 2 ^ Nat.size x ≤ y := by
    calc 2 ^ Nat.size x = 2 * 2 ^ (Nat.size x - 1) := by rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * x := by omega
      _ ≤ y := h
  exact Nat.lt_size.mpr this

/-- `6 t (t + 12) ≤ 2^(t-1)` from `t = 12` on. -/
theorem poly_le_pow (t : ℕ) (ht : 12 ≤ t) : 6 * t * (t + 12) ≤ 2 ^ (t - 1) := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [show t + 1 - 1 = (t - 1) + 1 by omega, pow_succ]
    nlinarith

/-! ### The level facts -/

/-- All arithmetic facts of a level with `N ≥ N0`, with the powers named. -/
theorem level_facts {N : ℕ} (hN : N0 ≤ N) :
    let s := bitlen N; let t := bitlen s; let k := kOf N; let M := pieceOf N; let N' := nextN N
    2048 ≤ s ∧ 12 ≤ t ∧ 2 ^ (s - 1) ≤ N ∧ N < 2 ^ s ∧ s < 2 ^ t ∧ 2 ^ (t - 1) ≤ s ∧
    6 * t * (t + 12) ≤ s + 1 ∧ 2 * k ≤ s - t ∧ s - t ≤ 2 * k + 1 ∧ 4 ≤ k ∧
    2 ^ k * M ≤ N ∧ M < 2 ^ (s - k) ∧ 2 * M + k + 1 ≤ N' ∧ N' ≤ 2 * M + k + 2 ^ k ∧
    2 ^ k * 2 ^ k * 2 ^ t ≤ 2 ^ s ∧ k + 1 ≤ 2 ^ k ∧ 2 * 2 ^ k ≤ 2 ^ (s - k) ∧
    N' < 2 ^ (s - k + 2) ∧ bitlen N' ≤ s - k + 2 ∧ 0 < N' := by
  intro s t k M N'
  have hN1 : 0 < N := lt_of_lt_of_le (by rw [N0_eq]; positivity) hN
  have hs : 2048 ≤ s := by
    show 2048 ≤ Nat.size N
    have : S0 - 1 < Nat.size N := Nat.lt_size.mpr (by rw [← N0_eq]; exact hN)
    rw [S0_eq] at this; omega
  have hspos : 0 < s := by omega
  have hP1 : 2 ^ (s - 1) ≤ N := two_pow_pred_le hN1
  have hP2 : N < 2 ^ s := Nat.lt_size_self N
  have hT1 : s < 2 ^ t := Nat.lt_size_self s
  have hT2 : 2 ^ (t - 1) ≤ s := two_pow_pred_le hspos
  have ht : 12 ≤ t := by
    show 12 ≤ Nat.size s
    exact Nat.lt_size.mpr (le_trans (by norm_num) hs)
  have hpoly : 6 * t * (t + 12) ≤ s + 1 := (poly_le_pow t ht).trans (by omega)
  have htle : t + 12 ≤ s := by nlinarith
  have hk1 : 2 * k ≤ s - t := by show 2 * ((s - t) / 2) ≤ s - t; omega
  have hk2 : s - t ≤ 2 * k + 1 := by show s - t ≤ 2 * ((s - t) / 2) + 1; omega
  have hk4 : 4 ≤ k := by omega
  have hKpos : 0 < 2 ^ k := by positivity
  have hKM : 2 ^ k * M ≤ N := Nat.mul_div_le N (2 ^ k)
  have hMlt : M < 2 ^ (s - k) := by
    show N / 2 ^ k < 2 ^ (s - k)
    rw [Nat.div_lt_iff_lt_mul hKpos, ← pow_add, Nat.sub_add_cancel (by omega)]; exact hP2
  -- the rounding
  have hround := Nat.div_add_mod (2 * M + k + 1 + 2 ^ k - 1) (2 ^ k)
  have hmod := Nat.mod_lt (2 * M + k + 1 + 2 ^ k - 1) hKpos
  have hN'def : N' = 2 ^ k * ((2 * M + k + 1 + 2 ^ k - 1) / 2 ^ k) := rfl
  have hlo : 2 * M + k + 1 ≤ N' := by rw [hN'def]; omega
  have hhi : N' ≤ 2 * M + k + 2 ^ k := by rw [hN'def]; omega
  have hsq : 2 ^ k * 2 ^ k * 2 ^ t ≤ 2 ^ s := by
    rw [← pow_add, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkK : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hKsk : 2 * 2 ^ k ≤ 2 ^ (s - k) := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN'lt : N' < 2 ^ (s - k + 2) := by
    rw [pow_add]; omega
  refine ⟨hs, ht, hP1, hP2, hT1, hT2, hpoly, hk1, hk2, hk4, hKM, hMlt, hlo, hhi, hsq, hkK, hKsk,
    hN'lt, Nat.size_le.mpr hN'lt, by omega⟩

/-! ### (1) Divisibility down the recursion -/

theorem dvd_next (N : ℕ) : 2 ^ kOf N ∣ nextN N := Dvd.intro _ rfl

theorem next_le {N : ℕ} (hN : N0 ≤ N) : 2 * nextN N ≤ N := by
  obtain ⟨hs, -, hP1, -, -, -, -, -, -, hk4, -, -, -, -, -, -, -, hN'lt, -, -⟩ := level_facts hN
  have : 2 ^ (bitlen N - kOf N + 2) * 2 ≤ 2 ^ (bitlen N - 1) := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The divisibility chain: `2^(kOf N') ∣ N'`. -/
theorem dvd_chain {N : ℕ} (hN : N0 ≤ N) :
    2 ^ kOf N ∣ nextN N ∧ kOf (nextN N) ≤ kOf N ∧ 2 ^ kOf (nextN N) ∣ nextN N := by
  have hle : nextN N ≤ N := by have := next_le hN; omega
  have hk := kOf_mono hle
  exact ⟨dvd_next N, hk, (pow_dvd_pow 2 hk).trans (dvd_next N)⟩

/-- `N = 2^k M` exactly when `2^k ∣ N`. -/
theorem split_exact {N : ℕ} (h : 2 ^ kOf N ∣ N) : N = 2 ^ kOf N * pieceOf N :=
  (Nat.mul_div_cancel' h).symm

/-! ### (2) The level hypotheses -/

theorem next_facts {N : ℕ} (hN : N0 ≤ N) :
    1 ≤ kOf N ∧ 2 * pieceOf N + kOf N + 1 ≤ nextN N ∧ 2 * nextN N ≤ N ∧ nextN N < N := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hk4, -, -, hlo, -, -, -, -, -, -, hpos⟩ := level_facts hN
  have := next_le hN
  exact ⟨by omega, hlo, this, by omega⟩

/-! ### (3) Size growth per level -/

/-- `K (N'+1) ≤ 2N + 2K²` with `2K² · s ≤ 4N`: the total size grows by `2 + O(1/s)`. -/
theorem growth {N : ℕ} (hN : N0 ≤ N) :
    2 ^ kOf N * (nextN N + 1) ≤ 2 * N + 2 * (2 ^ kOf N * 2 ^ kOf N) ∧
      2 * (2 ^ kOf N * 2 ^ kOf N) * bitlen N ≤ 4 * N := by
  obtain ⟨hs, -, hP1, -, hT1, -, -, -, -, -, hKM, -, -, hhi, hsq, hkK, -, -, -, -⟩ := level_facts hN
  set K := 2 ^ kOf N
  set s := bitlen N
  constructor
  · have e1 : K * (nextN N + 1) ≤ K * (2 * pieceOf N + kOf N + K + 1) := Nat.mul_le_mul_left _ (by omega)
    have e2 : K * (kOf N + 1) ≤ K * K := Nat.mul_le_mul_left _ hkK
    have e3 : K * (2 * pieceOf N + kOf N + K + 1) = 2 * (K * pieceOf N) + K * (kOf N + 1) + K * K := by
      ring
    omega
  · have h1 : K * K * s ≤ K * K * 2 ^ bitlen s := Nat.mul_le_mul_left _ hT1.le
    have h2 : 2 ^ s ≤ 2 * N := by
      have : 2 ^ s = 2 * 2 ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    have e : 2 * (K * K) * s = 2 * (K * K * s) := by ring
    omega

/-! ### (4) The cost recurrence -/

/-- The recurrence: quadratic base case, `K` recursive products, transform and
level costs. -/
def cost (A B C0 : ℕ) (N : ℕ) : ℕ :=
  if h : N < N0 then C0 * (N + 1) ^ 2
  else 2 ^ kOf N * cost A B C0 (nextN N) +
    A * 2 ^ kOf N * (nextN N + 1) * (kOf N + 1) + B * (N + 1) * (bitlen N + 1)
termination_by N
decreasing_by exact (next_facts (not_lt.mp h)).2.2.2

/-- The explicit constant of `cost_le`. -/
def costC (A B C0 : ℕ) : ℕ := C0 * 2 ^ S0 + 16 * A + 2 * B

/-- `O(N log N log log N)`: `cost N ≤ C (N+1)(s+1)(size (s^3) + 1)`. -/
theorem cost_le (A B C0 N : ℕ) :
    cost A B C0 N ≤ costC A B C0 * (N + 1) * (bitlen N + 1) * (bitlen (bitlen N ^ 3) + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    set C := costC A B C0
    rw [cost]
    split_ifs with h
    · -- base case
      have hN : N + 1 ≤ 2 ^ S0 := by
        have : N0 ≤ 2 ^ S0 := by rw [N0_eq]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hC : C0 * 2 ^ S0 ≤ C := by
        show C0 * 2 ^ S0 ≤ C0 * 2 ^ S0 + 16 * A + 2 * B; omega
      calc C0 * (N + 1) ^ 2 ≤ C0 * (2 ^ S0 * (N + 1)) := by
            rw [sq]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hN)
        _ = C0 * 2 ^ S0 * (N + 1) := by ring
        _ ≤ C * (N + 1) * 1 * 1 := by simp only [mul_one]; exact Nat.mul_le_mul_right _ hC
        _ ≤ _ := by gcongr <;> omega
    · have hN : N0 ≤ N := not_lt.mp h
      obtain ⟨hs, ht, hP1, hP2, hT1, hT2, hpoly, hk1, hk2, hk4, hKM, hMlt, hlo, hhi, hsq, hkK, hKsk,
        hN'lt, hs', hpos⟩ := level_facts hN
      obtain ⟨-, -, hlt⟩ := (next_facts hN).2
      obtain ⟨hg1, hg2⟩ := growth hN
      set s := bitlen N
      set t := bitlen s
      set k := kOf N
      set K := 2 ^ k
      set N' := nextN N
      set s' := bitlen N'
      set V := bitlen (s ^ 3)
      have ih' := ih N' hlt
      -- arithmetic on the bit lengths
      have hpoly' : 72 * (t + 12) ≤ 6 * t * (t + 12) := Nat.mul_le_mul_right _ (by omega)
      have h4t : 4 * (t + 5) ≤ s := by omega
      have h2s : 2 * s' ≤ s + t + 5 := by omega
      have hs'pos : 0 < s' := Nat.size_pos.mpr hpos
      have hcube : 2 * s' ^ 3 ≤ s ^ 3 := by
        have h8 : 8 * s' ≤ 5 * s := by omega
        have := Nat.pow_le_pow_left h8 3
        rw [mul_pow, mul_pow] at this
        norm_num at this
        omega
      have hW : bitlen (s' ^ 3) + 1 ≤ V := size_succ_of_double (by positivity) hcube
      have hV : V ≤ 3 * t := by
        show Nat.size (s ^ 3) ≤ 3 * t
        rw [Nat.size_le, pow_mul']; exact Nat.pow_lt_pow_left hT1 (by norm_num)
      have hVt : 2 * (V * (t + 12)) ≤ s + 1 := by
        have e1 : V * (t + 12) ≤ 3 * t * (t + 12) := Nat.mul_le_mul_right _ hV
        have e2 : 6 * t * (t + 12) = 2 * (3 * t * (t + 12)) := by ring
        omega
      -- the key size inequality
      have hkey : K * (N' + 1) * (s' + 1) ≤ (N + 1) * (s + 1) + (N + 1) * (t + 12) := by
        have e1 : K * (N' + 1) * (s' + 1) ≤ (2 * N + 2 * (K * K)) * (s' + 1) := Nat.mul_le_mul_right _ hg1
        have e2 : N * (2 * (s' + 1)) ≤ N * (s + t + 7) := Nat.mul_le_mul_left _ (by omega)
        have e3 : 2 * (K * K) * (s' + 1) ≤ 4 * N :=
          (Nat.mul_le_mul_left _ (show s' + 1 ≤ s by omega)).trans hg2
        have r1 : (2 * N + 2 * (K * K)) * (s' + 1) = N * (2 * (s' + 1)) + 2 * (K * K) * (s' + 1) := by ring
        have r2 : N * (s + t + 7) = N * s + N * t + 7 * N := by ring
        have r3 : (N + 1) * (s + 1) + (N + 1) * (t + 12) = N * s + N * t + 13 * N + s + t + 13 := by ring
        omega
      have hadd : A * K * (N' + 1) * (k + 1) + B * (N + 1) * (s + 1) ≤
          (8 * A + B) * (N + 1) * (s + 1) := by
        have e1 : K * (N' + 1) * (k + 1) ≤ (2 * N + 2 * (K * K)) * (k + 1) := Nat.mul_le_mul_right _ hg1
        have e2 : N * (2 * (k + 1)) ≤ N * (s + 2) := Nat.mul_le_mul_left _ (by omega)
        have e3 : 2 * (K * K) * (k + 1) ≤ 4 * N :=
          (Nat.mul_le_mul_left _ (show k + 1 ≤ s by omega)).trans hg2
        have r1 : (2 * N + 2 * (K * K)) * (k + 1) = N * (2 * (k + 1)) + 2 * (K * K) * (k + 1) := by ring
        have r2 : N * (s + 2) = N * s + 2 * N := by ring
        have r3 : (N + 1) * (s + 1) = N * s + N + s + 1 := by ring
        have e4 : K * (N' + 1) * (k + 1) ≤ 8 * ((N + 1) * (s + 1)) := by omega
        calc A * K * (N' + 1) * (k + 1) + B * (N + 1) * (s + 1)
            = A * (K * (N' + 1) * (k + 1)) + B * ((N + 1) * (s + 1)) := by ring
          _ ≤ A * (8 * ((N + 1) * (s + 1))) + B * ((N + 1) * (s + 1)) :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ e4) _
          _ = (8 * A + B) * (N + 1) * (s + 1) := by ring
      have hC : 2 * (8 * A + B) ≤ C := by
        show 2 * (8 * A + B) ≤ C0 * 2 ^ S0 + 16 * A + 2 * B; omega
      -- assemble
      have r1 : K * cost A B C0 N' ≤ C * V * (K * (N' + 1) * (s' + 1)) := by
        calc K * cost A B C0 N' ≤ K * (C * (N' + 1) * (s' + 1) * (bitlen (s' ^ 3) + 1)) :=
              Nat.mul_le_mul_left _ ih'
          _ ≤ K * (C * (N' + 1) * (s' + 1) * V) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
          _ = C * V * (K * (N' + 1) * (s' + 1)) := by ring
      have r2 : C * V * (K * (N' + 1) * (s' + 1)) ≤
          C * V * ((N + 1) * (s + 1)) + C * ((N + 1) * (V * (t + 12))) := by
        calc C * V * (K * (N' + 1) * (s' + 1)) ≤ C * V * ((N + 1) * (s + 1) + (N + 1) * (t + 12)) :=
              Nat.mul_le_mul_left _ hkey
          _ = _ := by ring
      have r3 : 2 * (C * ((N + 1) * (V * (t + 12)))) ≤ C * ((N + 1) * (s + 1)) := by
        calc 2 * (C * ((N + 1) * (V * (t + 12)))) = C * ((N + 1) * (2 * (V * (t + 12)))) := by ring
          _ ≤ C * ((N + 1) * (s + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hVt)
      have r4 : 2 * ((8 * A + B) * (N + 1) * (s + 1)) ≤ C * ((N + 1) * (s + 1)) := by
        calc 2 * ((8 * A + B) * (N + 1) * (s + 1)) = 2 * (8 * A + B) * ((N + 1) * (s + 1)) := by ring
          _ ≤ C * ((N + 1) * (s + 1)) := Nat.mul_le_mul_right _ hC
      have r5 : C * (N + 1) * (s + 1) * (V + 1) = C * V * ((N + 1) * (s + 1)) + C * ((N + 1) * (s + 1)) := by
        ring
      rw [r5]
      omega

theorem size_cube_le (s : ℕ) : bitlen (s ^ 3) ≤ 3 * bitlen s := by
  unfold bitlen
  rw [Nat.size_le, pow_mul']
  exact Nat.pow_lt_pow_left (Nat.lt_size_self s) (by norm_num)

/-! ### (5) The top-level ring size -/

/-- For `m` input bits: the power of two `2^(bitlen (2m))`, in `(2m, 4m]`. -/
def topN (m : ℕ) : ℕ := 2 ^ bitlen (2 * m)

theorem topN_facts {m : ℕ} (hm : 1 ≤ m) :
    2 * m < topN m ∧ topN m ≤ 4 * m ∧ 2 ^ kOf (topN m) ∣ topN m := by
  have h2m : 0 < 2 * m := by omega
  have h1 : 2 * m < topN m := Nat.lt_size_self _
  have h2 := two_pow_pred_le h2m
  have hpos := Nat.size_pos.mpr h2m
  have h3 : topN m ≤ 4 * m := by
    show 2 ^ Nat.size (2 * m) ≤ 4 * m
    have : 2 ^ Nat.size (2 * m) = 2 * 2 ^ (Nat.size (2 * m) - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  refine ⟨h1, h3, pow_dvd_pow 2 ?_⟩
  -- kOf (2^j) ≤ j
  have hb : bitlen (topN m) = bitlen (2 * m) + 1 := by
    unfold topN bitlen
    exact Nat.size_pow
  unfold kOf
  rw [hb]
  omega

/-- The top-level cost: `O(m log m log log m)`. -/
theorem cost_topN (A B C0 : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    cost A B C0 (topN m) ≤
      costC A B C0 * (4 * m + 1) * (bitlen (4 * m) + 1) * (3 * bitlen (bitlen (4 * m)) + 1) := by
  obtain ⟨-, hle, -⟩ := topN_facts hm
  have h1 : bitlen (topN m) ≤ bitlen (4 * m) := Nat.size_le_size hle
  have h2 : bitlen (bitlen (topN m) ^ 3) ≤ 3 * bitlen (bitlen (4 * m)) :=
    (size_cube_le _).trans (Nat.mul_le_mul_left _ (Nat.size_le_size h1))
  refine (cost_le A B C0 (topN m)).trans ?_
  gcongr

end IntegerMultBounds.Schoenhage.Schedule
