import IntegerMultBounds.Schoenhage.SSMain

/-! The multiplier's cost within the schedule's recurrence: `ssCost N [x, y]`
is at most `cost A B C0 N` for fixed constants plus a linear term, hence
`O(N log N log log N)`. -/

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-- The constants of the recurrence the tapes meet. -/
def cA : ℕ := 800000
def cB : ℕ := 1000000
def cC0 : ℕ := 10000

/-- The base case on a batch of `l` residues. -/
def baseTerm (N l : ℕ) : ℕ := l * ((N + 2) * (420 * N + 1400)) + 2 * (l * (N + 2)) + l * (5 * N + 30)

theorem cost_lt {A B C0 N : ℕ} (h : N < N0) : cost A B C0 N = C0 * (N + 1) ^ 2 := by
  rw [cost]; simp [h]

theorem cost_ge {A B C0 N : ℕ} (h : N0 ≤ N) : cost A B C0 N = 2 ^ kOf N * cost A B C0 (nextN N) +
    A * 2 ^ kOf N * (nextN N + 1) * (kOf N + 1) + B * (N + 1) * (bitlen N + 1) := by
  rw [cost]; simp [show ¬ N < N0 by omega]

theorem upFoldCost_append (A : List (ℕ × List ℕ)) (N : ℕ) (L : List ℕ) :
    upFoldCost (A ++ [(N, L)]) = upFoldCost A + (upCost N (L.length / 2) + 10) := by
  induction A with
  | nil => simp [upFoldCost]
  | cons a A ih => obtain ⟨_, _⟩ := a; simp [upFoldCost, ih]; ring

/-- One level's down and up cost per product. -/
theorem level_le {N P : ℕ} (hP : 1 ≤ P) :
    downCost N (2 * P) + upCost N P + 30 ≤
      P * (cA * 2 ^ kOf N * (nextN N + 1) * (kOf N + 1) + cB * (N + 1) * (bitlen N + 1)) := by
  set k := kOf N
  set K := 2 ^ k
  set Np := nextN N
  have hK : 1 ≤ K := Nat.one_le_two_pow
  set X := K * (Np + 1) * (k + 1)
  have h1 : (K + 1) * (Np + 2) ≤ 4 * (K * (Np + 1)) := by nlinarith
  have h2 : (5 * k + 14) * ((K + 1) * (Np + 2)) ≤ (14 * (k + 1)) * (4 * (K * (Np + 1))) :=
    Nat.mul_le_mul (by omega) h1
  set D := (k + 2) * (10000 * (K + 1) * (Np + 2)) + 20000 * N + 100000
  set U := (k + 4) * (10000 * (K + 1) * (Np + 2)) + 30000 * N + 100000
  have hD : downCost N (2 * P) = (2 * P + 1) * D := rfl
  have hU : upCost N P = (P + 1) * U := rfl
  have h3 : 3 * D + 2 * U + 30 ≤ cA * K * (Np + 1) * (k + 1) + cB * (N + 1) * (bitlen N + 1) := by
    have e : 3 * D + 2 * U = 10000 * ((5 * k + 14) * ((K + 1) * (Np + 2))) + 120000 * N + 500000 := by
      simp only [D, U]; ring
    have e2 : cA * K * (Np + 1) * (k + 1) = 800000 * X := by simp only [cA, X]; ring
    have e3 : (14 * (k + 1)) * (4 * (K * (Np + 1))) = 56 * X := by simp only [X]; ring
    rw [e, e2]
    have : 1 ≤ bitlen N + 1 := by omega
    have h4 : (N + 1) ≤ (N + 1) * (bitlen N + 1) := Nat.le_mul_of_pos_right _ (by omega)
    simp only [cB]
    nlinarith
  rw [hD, hU]
  nlinarith

theorem base_le {N P : ℕ} : baseTerm N (2 * P) ≤ P * (cC0 * (N + 1) ^ 2) := by
  have h : 2 * ((N + 2) * (420 * N + 1400)) + 4 * (N + 2) + 2 * (5 * N + 30) ≤ 10000 * (N + 1) ^ 2 := by
    nlinarith
  unfold baseTerm cC0
  calc 2 * P * ((N + 2) * (420 * N + 1400)) + 2 * (2 * P * (N + 2)) + 2 * P * (5 * N + 30)
      = P * (2 * ((N + 2) * (420 * N + 1400)) + 4 * (N + 2) + 2 * (5 * N + 30)) := by ring
    _ ≤ P * (10000 * (N + 1) ^ 2) := Nat.mul_le_mul_left _ h

theorem trajCost_small {N : ℕ} (hN : N < N0) (L : List ℕ) : ∀ j, trajCost j N L = 20 * j
  | 0 => rfl
  | j + 1 => by simp only [trajCost, hN, ↓reduceIte, trajCost_small hN L j]; ring

theorem length_traj_le : ∀ (j N : ℕ) (L : List ℕ), (traj j N L).1.length ≤ j
  | 0, _, _ => by simp [traj]
  | j + 1, N, L => by
    by_cases hN : N < N0
    · simp [traj, hN]
    · simp only [traj, hN, ↓reduceIte, List.length_cons]
      have := length_traj_le j (nextN N) (nextBatch (nextN N) (kOf N) (pieceOf N) L); omega

/-- The levels, the base case and the up-sweep cost at most `P` products' recurrence. -/
theorem total_le : ∀ (j N : ℕ) (L : List ℕ) (P : ℕ), N ≤ j → L.length = 2 * P → 1 ≤ P →
    trajCost j N L + upFoldCost (traj j N L).1.reverse + baseTerm (traj j N L).2.1 (traj j N L).2.2.length ≤
      P * cost cA cB cC0 N + 20 * j
  | 0, N, L, P, hNj, hl, _ => by
    have h0 : N = 0 := by omega
    subst h0
    have h0' : (0 : ℕ) < N0 := by rw [N0_eq]; positivity
    simp only [traj, trajCost, List.reverse_nil, upFoldCost, Nat.zero_add, hl, cost_lt h0']
    have := base_le (N := 0) (P := P); omega
  | j + 1, N, L, P, hNj, hl, hP => by
    by_cases hN : N < N0
    · rw [traj_small hN, trajCost_small hN, cost_lt hN]
      simp only [List.reverse_nil, upFoldCost, hl]
      have := base_le (N := N) (P := P); omega
    · rw [not_lt] at hN
      have hl' : ∀ x, (tpieces (nextN N) (kOf N) (pieceOf N) x).length = 2 ^ kOf N := fun x => by
        rw [tpieces, fwdIter_length _ _ _ _ _ rfl (by simp [length_pieces]), length_pieces]
      set NB := nextBatch (nextN N) (kOf N) (pieceOf N) L
      have hNB : NB.length = 2 * (P * 2 ^ kOf N) := by
        rw [length_nextBatch_eq _ _ _ hl' L (by rw [hl]; exact even_two_mul P), hl]; ring
      have hlt := (next_facts hN).2.2.2
      have ih := total_le j (nextN N) NB (P * 2 ^ kOf N) (by omega) hNB
        (Nat.one_le_iff_ne_zero.mpr (by positivity))
      have hlev := level_le (N := N) hP
      have ht : traj (j + 1) N L = ((N, L) :: (traj j (nextN N) NB).1, (traj j (nextN N) NB).2.1,
          (traj j (nextN N) NB).2.2) := by simp [traj, show ¬ N < N0 by omega, NB]
      have htc : trajCost (j + 1) N L = downCost N L.length + 20 + trajCost j (nextN N) NB := by
        simp [trajCost, show ¬ N < N0 by omega, NB]
      rw [ht, htc, cost_ge hN]
      simp only [List.reverse_cons, upFoldCost_append, hl]
      rw [show 2 * P / 2 = P by omega]
      have e : P * (2 ^ kOf N * cost cA cB cC0 (nextN N) +
          cA * 2 ^ kOf N * (nextN N + 1) * (kOf N + 1) + cB * (N + 1) * (bitlen N + 1)) =
          P * 2 ^ kOf N * cost cA cB cC0 (nextN N) +
          P * (cA * 2 ^ kOf N * (nextN N + 1) * (kOf N + 1) + cB * (N + 1) * (bitlen N + 1)) := by ring
      rw [e]
      omega

/-- The multiplier's cost in the recurrence. -/
theorem ssCost_le (N x y : ℕ) : ssCost N [x, y] ≤ cost cA cB cC0 N + 600 * N + 50000 := by
  have h := total_le N N [x, y] 1 le_rfl rfl le_rfl
  have hl := length_traj_le N N [x, y]
  dsimp only [ssCost]
  simp only [baseTerm] at h
  omega

/-- The multiplier runs in `O(N log N log log N)` steps. -/
theorem runs_ssMain_bound {N x y : ℕ} (hN : 0 < N) (hk : 2 ^ kOf N ∣ N) (hx : x < Fm N) (hy : y < Fm N)
    (σ : Fin 𝕋 → WTape) (hS : SSStart N x y σ) :
    Runs ssMain σ (fun σ' => (σ' tIn).right = [rwd N (x * y % Fm N)])
      (costC cA cB cC0 * (N + 1) * (bitlen N + 1) * (bitlen (bitlen N ^ 3) + 1) + 600 * N + 50000) :=
  (runs_ssMain hN hk hx hy σ hS).mono (fun _ h => h)
    ((ssCost_le N x y).trans (by have := cost_le cA cB cC0 N; omega))

/-- Exact products: two operands below `2^m` multiplied at size `topN m`, in `O(m log m log log m)` steps. -/
theorem runs_ssExact {m a b : ℕ} (hm : 1 ≤ m) (ha : a < 2 ^ m) (hb : b < 2 ^ m) (σ : Fin 𝕋 → WTape)
    (hS : SSStart (topN m) a b σ) :
    Runs ssMain σ (fun σ' => (σ' tIn).right = [rwd (topN m) (a * b)])
      (costC cA cB cC0 * (4 * m + 1) * (bitlen (4 * m) + 1) * (3 * bitlen (bitlen (4 * m)) + 1) +
        2400 * m + 50000) := by
  obtain ⟨hlt, hle, hk⟩ := topN_facts hm
  have hm2 : 2 ^ m ≤ 2 ^ topN m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hab : a * b < Fm (topN m) := by
    have : a * b < 2 ^ m * 2 ^ m := Nat.mul_lt_mul'' ha hb
    have h2 : 2 ^ m * 2 ^ m ≤ 2 ^ topN m := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold Fm; omega
  have r := runs_ssMain (N := topN m) (by omega) hk (by unfold Fm; omega) (by unfold Fm; omega) σ hS
  rw [Nat.mod_eq_of_lt hab] at r
  exact r.mono (fun _ h => h) ((ssCost_le _ a b).trans (by have := cost_topN cA cB cC0 hm; omega))

end IntegerMultBounds.Schoenhage
