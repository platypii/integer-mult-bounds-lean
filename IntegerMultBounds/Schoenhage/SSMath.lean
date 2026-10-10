import IntegerMultBounds.Schoenhage.DriverUp

/-! The driver's trajectory computes `ssMul`: the up-sweep over the saved
levels of the base products returns the products of the top batch. -/

namespace IntegerMultBounds.Schoenhage

open Schedule

theorem upFold_append (A : List (ℕ × List ℕ)) (N : ℕ) (L Q : List ℕ) :
    upFold (A ++ [(N, L)]) Q = upList N (2 ^ kOf N) (L.length / 2) (upFold A Q) := by
  induction A generalizing Q with
  | nil => rfl
  | cons a A ih => obtain ⟨N', L'⟩ := a; simp [upFold, ih]

theorem traj_lt : ∀ (j N : ℕ) (L : List ℕ), N ≤ j → (traj j N L).2.1 < N0
  | 0, N, L, h => by
    have : N = 0 := by omega
    subst this; simp [traj]; rw [N0_eq]; positivity
  | j + 1, N, L, h => by
    by_cases hN : N < N0
    · simp [traj, hN]
    · rw [not_lt] at hN
      have := next_le hN
      have hpos : 0 < N := lt_of_lt_of_le (by rw [N0_eq]; positivity) hN
      simp only [traj, show ¬ N < N0 by omega, ↓reduceIte]
      exact traj_lt j _ _ (by omega)

theorem length_nextBatch_eq (Np k M : ℕ) (hl : ∀ x, (tpieces Np k M x).length = 2 ^ k) :
    ∀ L : List ℕ, Even L.length → (nextBatch Np k M L).length = L.length * 2 ^ k
  | [], _ => by simp [nextBatch]
  | [_], he => by simp at he
  | x :: y :: L, he => by
    have ih := length_nextBatch_eq Np k M hl L (by simpa [Nat.even_add_one, parity_simps] using he)
    simp only [nextBatch, List.length_append, List.length_cons]
    rw [length_zipFlat _ _ (by rw [hl, hl]), hl, ih]; ring

theorem length_pairsOf : ∀ L : List ℕ, (pairsOf L).length = L.length / 2
  | [] => rfl
  | [_] => by simp [pairsOf]
  | x :: y :: L => by simp [pairsOf, length_pairsOf L]; omega

/-- The up-sweep over the reversed trajectory of the base products gives `ssMul` on the top batch. -/
theorem upFold_traj : ∀ (j N : ℕ) (L : List ℕ), 2 ^ kOf N ∣ N → Even L.length → (∀ x ∈ L, x < Fm N) →
    upFold (traj j N L).1.reverse ((pairsOf (traj j N L).2.2).map fun p => ssMul (traj j N L).2.1 p.1 p.2) =
      (pairsOf L).map fun p => ssMul N p.1 p.2
  | 0, N, L, _, _, _ => by simp [traj, upFold]
  | j + 1, N, L, hk, he, hv => by
    by_cases hN : N < N0
    · simp [traj, hN, upFold]
    · rw [not_lt] at hN
      have hl : ∀ x, (tpieces (nextN N) (kOf N) (pieceOf N) x).length = 2 ^ kOf N := fun x => by
        rw [tpieces, fwdIter_length _ _ _ _ _ rfl (by simp [length_pieces]), length_pieces]
      have ih := upFold_traj j (nextN N) (nextBatch (nextN N) (kOf N) (pieceOf N) L) (dvd_chain hN).2.2
        (nextBatch_even _ _ _ hl L) (nextBatch_lt hN hk L hv)
      simp only [traj, show ¬ N < N0 by omega, ↓reduceIte, List.reverse_cons, upFold_append, ih]
      obtain ⟨g, hg⟩ := he
      rw [show L.length / 2 = g by omega]
      exact upList_nextBatch hN g L (by omega)

/-- The group count after the saved levels. -/
def lastQ : List (ℕ × List ℕ) → ℕ → ℕ
  | [], ql => ql
  | (_, L) :: A, _ => lastQ A (L.length / 2)

theorem UpOK_append : ∀ (A : List (ℕ × List ℕ)) (N : ℕ) (L : List ℕ) (Nc ql : ℕ),
    UpOK (A ++ [(N, L)]) Nc ql ↔ UpOK A Nc ql ∧ (N0 ≤ N ∧ 2 ^ kOf N ∣ N ∧ nextN N = lastN A Nc ∧
      lastQ A ql = L.length / 2 * 2 ^ kOf N)
  | [], N, L, Nc, ql => by simp [UpOK, lastN, lastQ]
  | (N', L') :: A, N, L, Nc, ql => by
    simp only [List.cons_append, UpOK, lastN, lastQ, UpOK_append A N L N' (L'.length / 2)]
    tauto

theorem lastN_traj : ∀ (j N : ℕ) (L : List ℕ),
    lastN (traj j N L).1.reverse (traj j N L).2.1 = N ∧ lastQ (traj j N L).1.reverse ((traj j N L).2.2.length / 2) =
      L.length / 2
  | 0, N, L => by simp [traj, lastN, lastQ]
  | j + 1, N, L => by
    by_cases hN : N < N0
    · simp [traj, hN, lastN, lastQ]
    · simp only [traj, show ¬ N < N0 by omega, ↓reduceIte, List.reverse_cons]
      have h1 : ∀ (A : List (ℕ × List ℕ)) Nc, lastN (A ++ [(N, L)]) Nc = N := by
        intro A; induction A with
        | nil => simp [lastN]
        | cons a A ih => intro Nc; obtain ⟨_, _⟩ := a; simp [lastN, ih]
      have h2 : ∀ (A : List (ℕ × List ℕ)) ql, lastQ (A ++ [(N, L)]) ql = L.length / 2 := by
        intro A; induction A with
        | nil => simp [lastQ]
        | cons a A ih => intro ql; obtain ⟨_, _⟩ := a; simp [lastQ, ih]
      exact ⟨h1 _ _, h2 _ _⟩

theorem UpOK_traj : ∀ (j N : ℕ) (L : List ℕ), 2 ^ kOf N ∣ N → Even L.length →
    UpOK (traj j N L).1.reverse (traj j N L).2.1 ((traj j N L).2.2.length / 2)
  | 0, N, L, _, _ => by simp [traj, UpOK]
  | j + 1, N, L, hk, he => by
    by_cases hN : N < N0
    · simp [traj, hN, UpOK]
    · rw [not_lt] at hN
      have hl : ∀ x, (tpieces (nextN N) (kOf N) (pieceOf N) x).length = 2 ^ kOf N := fun x => by
        rw [tpieces, fwdIter_length _ _ _ _ _ rfl (by simp [length_pieces]), length_pieces]
      set NB := nextBatch (nextN N) (kOf N) (pieceOf N) L
      have ih := UpOK_traj j (nextN N) NB (dvd_chain hN).2.2 (nextBatch_even _ _ _ hl L)
      have hlast := lastN_traj j (nextN N) NB
      simp only [traj, show ¬ N < N0 by omega, ↓reduceIte, List.reverse_cons]
      rw [UpOK_append]
      refine ⟨ih, hN, hk, hlast.1.symm, ?_⟩
      rw [hlast.2, length_nextBatch_eq _ _ _ hl L he]
      obtain ⟨g, hg⟩ := he
      rw [hg, show (g + g) / 2 = g by omega, show (g + g) * 2 ^ kOf N = 2 * (g * 2 ^ kOf N) by ring,
        Nat.mul_div_cancel_left _ two_pos]

end IntegerMultBounds.Schoenhage
