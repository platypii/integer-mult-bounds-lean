import IntegerMultBounds.Schoenhage.Recursive

/-! The up-sweep of a level as the tapes compute it. The signed coefficients
are split into two nonnegative streams, the positive parts and the negated
negative parts; each stream is evaluated at `2^M` as a plain sum of shifted
words (`wsum`), and each sum is reduced modulo `2^N + 1` from its low and
high `N`-bit halves (`red`). Proved: this equals `levelOut` (`levelTape_eq`). -/

namespace IntegerMultBounds.Schoenhage

open Schedule Polynomial

/-- `Σ pᵢ 2^(M i)`. -/
def wsum (M : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps => p + 2 ^ M * wsum M ps

/-- The coefficient if its signed representative is nonnegative. -/
def posPart (N d : ℕ) : ℕ := if 2 * d < Fm N then d else 0

/-- The negated coefficient if its signed representative is negative. -/
def negPart (N d : ℕ) : ℕ := if 2 * d < Fm N then 0 else Fm N - d

/-- Reduction modulo `2^N + 1` from the low and high halves. -/
def red (N Z : ℕ) : ℕ := (Z % 2 ^ N + Fm N - Z / 2 ^ N) % Fm N

/-- The up-sweep from the inverse transform's output words. -/
def levelTape (N : ℕ) (ws : List ℕ) : ℕ :=
  let ds := ws.map (descale (nextN N) (kOf N))
  (red N (wsum (pieceOf N) (ds.map (posPart (nextN N)))) + Fm N -
    red N (wsum (pieceOf N) (ds.map (negPart (nextN N))))) % Fm N

theorem eval_lift (N M : ℕ) : ∀ ds : List ℕ, (∀ d ∈ ds, d < Fm N) →
    (poly (ds.map (liftN N))).eval (2 ^ M : ℤ) =
      (wsum M (ds.map (posPart N)) : ℤ) - wsum M (ds.map (negPart N))
  | [], _ => by simp [wsum]
  | d :: ds, h => by
    have ih := eval_lift N M ds (fun x hx => h x (by simp [hx]))
    have hd := h d (by simp)
    simp only [List.map_cons, poly_cons, eval_add, eval_C, eval_mul, eval_X, ih, wsum]
    unfold liftN posPart negPart
    split_ifs with h1
    · push_cast; ring
    · push_cast [Nat.cast_sub hd.le]; ring

theorem red_eq {N Z : ℕ} (hZ : Z < 2 ^ (2 * N)) : red N Z = Z % Fm N := by
  unfold red Fm
  have hb : Z / 2 ^ N < 2 ^ N := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos N), ← pow_add]; rwa [two_mul] at hZ
  have hZ' : Z = Z % 2 ^ N + 2 ^ N * (Z / 2 ^ N) := (Nat.mod_add_div Z (2 ^ N)).symm
  set a := Z % 2 ^ N
  set b := Z / 2 ^ N
  have key : a + (2 ^ N + 1) - b + (2 ^ N + 1) * b = Z + (2 ^ N + 1) := by
    rw [hZ']; zify [show b ≤ a + (2 ^ N + 1) by omega]; ring
  rw [← Nat.add_mul_mod_self_left (a + (2 ^ N + 1) - b) (2 ^ N + 1) b, key, Nat.add_mod_right]

theorem wsum_lt {M c : ℕ} (hM : 1 ≤ M) : ∀ ps : List ℕ, ps ≠ [] → (∀ p ∈ ps, p < 2 ^ c) →
    wsum M ps + 2 ^ c ≤ 2 ^ (c + M * (ps.length - 1) + 1)
  | [], h, _ => absurd rfl h
  | [p], _, h => by
    have := h p (by simp)
    simp [wsum, pow_succ]; omega
  | p :: q :: ps, _, h => by
    have ih := wsum_lt hM (q :: ps) (by simp) (fun x hx => h x (by simp [hx]))
    have hp := h p (by simp)
    simp only [List.length_cons, Nat.add_sub_cancel] at ih ⊢
    simp only [wsum] at ih ⊢
    have e1 : 2 ^ (c + M * (ps.length + 1) + 1) = 2 ^ M * 2 ^ (c + M * ps.length + 1) := by
      rw [← pow_add]; congr 1; ring
    have e2 : 2 ^ M * 2 ^ c ≥ 2 * 2 ^ c := Nat.mul_le_mul_right _ (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM)
    rw [e1]
    have := Nat.mul_le_mul_left (2 ^ M) ih
    rw [Nat.mul_add] at this
    omega

/-- The parts are small: below `2^N`. -/
theorem posPart_lt {N d : ℕ} (hN : 1 ≤ N) : posPart N d < 2 ^ N := by
  unfold posPart Fm; split_ifs with h
  · have : 2 ^ N = 2 * 2 ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
    have := Nat.two_pow_pos (N - 1)
    omega
  · exact Nat.two_pow_pos N

theorem negPart_lt {N d : ℕ} (hN : 1 ≤ N) : negPart N d < 2 ^ N := by
  unfold negPart Fm; split_ifs with h
  · exact Nat.two_pow_pos N
  · have : 2 ^ N = 2 * 2 ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
    have := Nat.two_pow_pos (N - 1)
    omega

theorem wsum_parts_lt {N : ℕ} (hN : N0 ≤ N) (ds : List ℕ) (hl : ds.length = 2 ^ kOf N)
    (f : ℕ → ℕ) (hf : ∀ d, f d < 2 ^ nextN N) (hk : 2 ^ kOf N ∣ N) :
    wsum (pieceOf N) (ds.map f) < 2 ^ (2 * N) := by
  have hnf := next_facts hN
  have hs := split_exact hk
  have hM : 1 ≤ pieceOf N := by
    rcases Nat.eq_zero_or_pos (pieceOf N) with h | h
    · rw [h, mul_zero] at hs
      have : 0 < N := lt_of_lt_of_le (by rw [N0_eq]; exact Nat.two_pow_pos _) hN
      omega
    · exact h
  have hne : ds.map f ≠ [] := by
    intro h; have := congrArg List.length h; simp [hl] at this
  have := wsum_lt (c := nextN N) hM (ds.map f) hne (fun p hp => by
    simp only [List.mem_map] at hp; obtain ⟨d, -, rfl⟩ := hp; exact hf d)
  rw [List.length_map, hl] at this
  have hK : 1 ≤ 2 ^ kOf N := Nat.one_le_two_pow
  have hexp : nextN N + pieceOf N * (2 ^ kOf N - 1) + 1 ≤ 2 * N := by
    have : pieceOf N * (2 ^ kOf N - 1) + pieceOf N = pieceOf N * 2 ^ kOf N := by
      rw [← Nat.mul_succ]; congr 1; omega
    rw [mul_comm] at hs
    omega
  calc wsum (pieceOf N) (ds.map f) < 2 ^ (nextN N + pieceOf N * (2 ^ kOf N - 1) + 1) := by
        have := Nat.two_pow_pos (nextN N); omega
    _ ≤ 2 ^ (2 * N) := Nat.pow_le_pow_right (by norm_num) hexp

theorem levelTape_eq {N : ℕ} (hN : N0 ≤ N) (hk : 2 ^ kOf N ∣ N) (ws : List ℕ)
    (hl : ws.length = 2 ^ kOf N) :
    levelTape N ws = recomb N (pieceOf N)
      ((ws.map (descale (nextN N) (kOf N))).map (liftN (nextN N))) := by
  have hnf := next_facts hN
  have hN1 : 1 ≤ nextN N := by omega
  set ds := ws.map (descale (nextN N) (kOf N)) with hds
  have hdl : ds.length = 2 ^ kOf N := by simp [hds, hl]
  have hA := wsum_parts_lt hN ds hdl (posPart (nextN N)) (fun _ => posPart_lt hN1) hk
  have hB := wsum_parts_lt hN ds hdl (negPart (nextN N)) (fun _ => negPart_lt hN1) hk
  unfold levelTape recomb
  dsimp only
  rw [← hds, red_eq hA, red_eq hB, eval_lift _ _ ds (fun d hd => by
    simp only [hds, List.mem_map] at hd; obtain ⟨w, -, rfl⟩ := hd; exact descale_lt _ _ _)]
  set A := wsum (pieceOf N) (ds.map (posPart (nextN N)))
  set B := wsum (pieceOf N) (ds.map (negPart (nextN N)))
  have hF : (0 : ℤ) < Fm N := by exact_mod_cast Fm_pos N
  have hBF := Nat.mod_lt B (Fm_pos N)
  apply Int.ofNat.inj
  simp only [Int.ofNat_eq_natCast]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hF.ne')]
  push_cast [show B % Fm N ≤ A % Fm N + Fm N by omega]
  have h1 : (A : ℤ) % Fm N ≡ A [ZMOD Fm N] := Int.mod_modEq _ _
  have h2 : ((Fm N : ℕ) : ℤ) ≡ 0 [ZMOD Fm N] := by simp [Int.ModEq]
  have h3 : (B : ℤ) % Fm N ≡ B [ZMOD Fm N] := Int.mod_modEq _ _
  exact ((h1.add h2).sub h3).trans (by simp [Int.ModEq])

end IntegerMultBounds.Schoenhage
