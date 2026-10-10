import IntegerMultBounds.Schoenhage.BaseCase

/-! The schedule's parameters computed on word tapes in unary: the bit length
of a unary word by repeated halving. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

namespace Tp
abbrev qR : Fin 𝕋 := 55
abbrev qB : Fin 𝕋 := 56
abbrev qT : Fin 𝕋 := 57
abbrev qS : Fin 𝕋 := 58
end Tp

theorem size_half {r : ℕ} (h : 0 < r) : Nat.size r = Nat.size (r / 2) + 1 := by
  apply le_antisymm
  · rw [Nat.size_le, pow_succ]
    have := Nat.lt_size_self (r / 2)
    omega
  · rw [Nat.succ_le_iff, Nat.lt_size]
    rcases Nat.eq_zero_or_pos (r / 2) with h2 | h2
    · rw [h2, Nat.size_zero]; simp; omega
    · have := Nat.lt_size.mp (show Nat.size (r / 2) - 1 < Nat.size (r / 2) by
        have := Nat.size_pos.mpr h2; omega)
      have e : 2 ^ Nat.size (r / 2) = 2 * 2 ^ (Nat.size (r / 2) - 1) := by
        rw [← pow_succ']; congr 1; have := Nat.size_pos.mpr h2; omega
      omega

/-! ### Bit length -/

theorem not_startsOne_reg_nil : ¬ StartsOne (reg []) := by
  rintro ⟨w, R, h⟩; simp [reg] at h

theorem startsOne_reg_ones {r : ℕ} (hr : 0 < r) : StartsOne (reg (ones r)) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  exact ⟨ones r', [], by simp [reg, ones, List.replicate_succ]⟩

/-- One more one on the counter `qB`. -/
noncomputable def incB : Cmd 0 𝕋 :=
  .seq (skp qB tJ (by decide)) <| .seq (op0 Rules.copy true c1 qB (by decide)) <| .seq (rewind c1) (rewind qB)

/-- Halve `qR` and count. -/
noncomputable def halveIt : Cmd 0 𝕋 :=
  .seq (op0 Rules.half false qR qS (by decide)) <| .seq (clear qR) <| .seq (rewind qS) <|
  .seq (regMove qS qR (by decide)) incB

/-- Halve while nonzero, once per tick of `qT`. -/
noncomputable def halveStep : Cmd 0 𝕋 := .seq (.cond qR halveIt (rewind qR)) (skp qT tJ (by decide))

/-- The bit length loop. -/
noncomputable def sizeLoop : Cmd 0 𝕋 := .loop qT halveStep

theorem runs_halveIt {r b : ℕ} (σ : Fin 𝕋 → WTape) (hR : σ qR = reg (ones r)) (hB : σ qB = reg (ones b))
    (h1 : σ c1 = reg [true]) (hS : σ qS = emp) (hJ : σ tJ = emp) :
    Runs halveIt σ (· = Function.update (Function.update σ qR (reg (ones (r / 2)))) qB (reg (ones (b + 1))))
      (8 * r + 3 * b + 60) := by
  apply Runs.of_wp
  simp only [halveIt, incB, regMove, regIn, cpy, skp, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hR, hB, h1, hS, hJ, emp, reg, Rules.output_half_ones, Rules.output_copy, Rules.output_skip]
  have t1 := time_le Rules.half (ones r) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.copy (ones (r / 2)) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t3 := time_le Rules.skip (ones b) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t4 := time_le Rules.copy [true] (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hR, hB, h1, hS, hJ, emp, reg, ones, List.replicate_succ']
  · simp [clen, WTape.words] at t1 t2 t3 t4 ⊢; omega

/-- Halving with a counter, `j` times (halving stops at zero). -/
def hv : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, r, b => (r, b)
  | j + 1, r, b => if r = 0 then hv j 0 b else hv j (r / 2) (b + 1)

theorem hv_eq : ∀ (j r b : ℕ), Nat.size r ≤ j → hv j r b = (0, b + Nat.size r)
  | 0, r, b, h => by
    have : r = 0 := Nat.size_eq_zero.mp (by omega)
    subst this; simp [hv]
  | j + 1, r, b, h => by
    rw [hv]
    split_ifs with hr
    · subst hr; rw [hv_eq j 0 b (by simp)]
    · have hs := size_half (show 0 < r by omega)
      rw [hv_eq j (r / 2) (b + 1) (by omega), hs]
      congr 1; ring

theorem runs_sizeLoop :
    ∀ (j r b : ℕ) (σ : Fin 𝕋 → WTape) (Tl : List (List Bool)),
      σ qR = reg (ones r) → σ qB = reg (ones b) → σ c1 = reg [true] → σ qS = emp → σ tJ = emp →
      σ qT = ⟨Tl, List.replicate j []⟩ →
      Runs sizeLoop σ (· = Function.update (Function.update (Function.update σ
          qR (reg (ones (hv j r b).1))) qB (reg (ones (hv j r b).2))) qT ⟨List.replicate j [] ++ Tl, []⟩)
        (16 * r + 4 * (b + Nat.size r) * Nat.size r + 80 * Nat.size r + 20 * j)
  | 0, r, b, σ, Tl, hR, hB, _, _, _, hT => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hR, hB, hT, hv]
  | j + 1, r, b, σ, Tl, hR, hB, h1, hS, hJ, hT => by
    by_cases hr : r = 0
    · subst hr
      have s1 : Runs (a := 0) halveStep σ (· = Function.update σ qT ⟨[] :: Tl, List.replicate j []⟩) 12 := by
        unfold halveStep
        refine (Runs.then (Runs.cond_false (by rw [hR]; exact not_startsOne_reg_nil) (runs_rewind qR σ))
          (runs_skp (a := 0) (s := qT) (j := tJ) (by decide) _ (by tsimp [hT, List.replicate_succ])
            (by tsimp [hJ, emp]))).mono (fun σ' h => ?_) ?_
        · rw [h]; funext i; fin_cases i <;> tsimp [hR, hT, reg, List.replicate_succ]
        · tsimp [hR, hT, reg, ones, List.replicate_succ, clen]
      set σ₁ := Function.update σ qT ⟨[] :: Tl, List.replicate j []⟩
      have ih := runs_sizeLoop j 0 b σ₁ ([] :: Tl) (by tsimp [σ₁, hR]) (by tsimp [σ₁, hB]) (by tsimp [σ₁, h1])
        (by tsimp [σ₁, hS]) (by tsimp [σ₁, hJ]) (by tsimp [σ₁])
      refine (Runs.loop_step (by simp [hT]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
        (fun σ' h' => ?_) ?_
      · rw [h']; funext i; fin_cases i <;> tsimp [σ₁, hv, List.replicate_succ, replicate_append_cons]
      · simp; omega
    · have s1 : Runs (a := 0) halveStep σ (· = Function.update (Function.update (Function.update σ
            qR (reg (ones (r / 2)))) qB (reg (ones (b + 1)))) qT ⟨[] :: Tl, List.replicate j []⟩)
          (8 * r + 3 * b + 67) := by
        unfold halveStep
        refine (Runs.then (Runs.cond_true (by rw [hR]; exact startsOne_reg_ones (by omega))
            (runs_halveIt σ hR hB h1 hS hJ))
          (runs_skp (a := 0) (s := qT) (j := tJ) (by decide) _ (by tsimp [hT, List.replicate_succ])
            (by tsimp [hJ, emp]))).mono (fun σ' h => ?_) ?_
        · rw [h]; funext i; fin_cases i <;> tsimp [hT, List.replicate_succ]
        · tsimp [hT, List.replicate_succ]
      set σ₁ := Function.update (Function.update (Function.update σ
            qR (reg (ones (r / 2)))) qB (reg (ones (b + 1)))) qT ⟨[] :: Tl, List.replicate j []⟩
      have ih := runs_sizeLoop j (r / 2) (b + 1) σ₁ ([] :: Tl) (by tsimp [σ₁]) (by tsimp [σ₁])
        (by tsimp [σ₁, h1]) (by tsimp [σ₁, hS]) (by tsimp [σ₁, hJ]) (by tsimp [σ₁])
      refine (Runs.loop_step (by simp [hT]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
        (fun σ' h' => ?_) ?_
      · rw [h']; funext i; fin_cases i <;> tsimp [σ₁, hv, hr, List.replicate_succ, replicate_append_cons]
      · rw [size_half (show 0 < r by omega)]
        have : 2 * (r / 2) ≤ r := Nat.mul_div_le r 2
        nlinarith

/-! ### Repeated halving and doubling -/

/-- Halve `qR` once per tick of `qT`. -/
noncomputable def halveLoop : Cmd 0 𝕋 :=
  .loop qT (.seq (op0 Rules.half false qR qS (by decide)) <| .seq (clear qR) <| .seq (rewind qS) <|
    .seq (regMove qS qR (by decide)) (skp qT tJ (by decide)))

theorem runs_halveLoop :
    ∀ (j r : ℕ) (σ : Fin 𝕋 → WTape) (Tl : List (List Bool)),
      σ qR = reg (ones r) → σ qS = emp → σ tJ = emp → σ qT = ⟨Tl, List.replicate j []⟩ →
      Runs halveLoop σ (· = Function.update (Function.update σ qR (reg (ones (r / 2 ^ j))))
          qT ⟨List.replicate j [] ++ Tl, []⟩) (16 * r + 40 * j)
  | 0, r, σ, Tl, hR, _, _, hT => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hR, hT]
  | j + 1, r, σ, Tl, hR, hS, hJ, hT => by
    have s1 : Runs (a := 0) (.seq (op0 Rules.half false qR qS (by decide)) <| .seq (clear qR) <| .seq (rewind qS) <|
        .seq (regMove qS qR (by decide)) (skp qT tJ (by decide))) σ
        (· = Function.update (Function.update σ qR (reg (ones (r / 2)))) qT ⟨[] :: Tl, List.replicate j []⟩)
        (8 * r + 38) := by
      apply Runs.of_wp
      simp only [regMove, regIn, cpy, skp, WP, wp_op0, wp_rewind, wp_clear]
      tsimp [hR, hS, hJ, hT, emp, reg, List.replicate_succ, Rules.output_half_ones, Rules.output_copy,
        Rules.output_skip]
      have t1 := time_le Rules.half (ones r) (fun j => j.elim0) 0 (fun j => j.elim0)
      have t2 := time_le Rules.copy (ones (r / 2)) (fun j => j.elim0) 0 (fun j => j.elim0)
      have t3 := time_le Rules.skip [] (fun j => j.elim0) 0 (fun j => j.elim0)
      refine ⟨?_, ?_⟩
      · funext i; fin_cases i <;> tsimp [hR, hS, hJ, hT, emp, reg, List.replicate_succ]
      · simp [clen, WTape.words] at t1 t2 t3 ⊢; omega
    set σ₁ := Function.update (Function.update σ qR (reg (ones (r / 2)))) qT ⟨[] :: Tl, List.replicate j []⟩
    have ih := runs_halveLoop j (r / 2) σ₁ ([] :: Tl) (by tsimp [σ₁]) (by tsimp [σ₁, hS]) (by tsimp [σ₁, hJ])
      (by tsimp [σ₁])
    refine (Runs.loop_step (by simp [hT]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      have e : r / 2 / 2 ^ j = r / 2 ^ (j + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
      funext i; fin_cases i <;> tsimp [σ₁, e, List.replicate_succ, replicate_append_cons]
    · have : 2 * (r / 2) ≤ r := Nat.mul_div_le r 2
      omega

/-- Double `qR` once per tick of `qT`. -/
noncomputable def doubleLoop : Cmd 0 𝕋 :=
  .loop qT (.seq (op0 Rules.copy false qR qS (by decide)) <| .seq (rewind qR) <|
    .seq (op0 Rules.copy true qR qS (by decide)) <| .seq (clear qR) <| .seq (rewind qS) <|
    .seq (regMove qS qR (by decide)) (skp qT tJ (by decide)))

theorem runs_doubleLoop :
    ∀ (j r : ℕ) (σ : Fin 𝕋 → WTape) (Tl : List (List Bool)),
      σ qR = reg (ones r) → σ qS = emp → σ tJ = emp → σ qT = ⟨Tl, List.replicate j []⟩ →
      Runs doubleLoop σ (· = Function.update (Function.update σ qR (reg (ones (r * 2 ^ j))))
          qT ⟨List.replicate j [] ++ Tl, []⟩) (20 * (r * 2 ^ j - r) + 50 * j)
  | 0, r, σ, Tl, hR, _, _, hT => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hR, hT]
  | j + 1, r, σ, Tl, hR, hS, hJ, hT => by
    have s1 : Runs (a := 0) (.seq (op0 Rules.copy false qR qS (by decide)) <| .seq (rewind qR) <|
        .seq (op0 Rules.copy true qR qS (by decide)) <| .seq (clear qR) <| .seq (rewind qS) <|
        .seq (regMove qS qR (by decide)) (skp qT tJ (by decide))) σ
        (· = Function.update (Function.update σ qR (reg (ones (r * 2)))) qT ⟨[] :: Tl, List.replicate j []⟩)
        (20 * r + 48) := by
      apply Runs.of_wp
      simp only [regMove, regIn, cpy, skp, WP, wp_op0, wp_rewind, wp_clear]
      tsimp [hR, hS, hJ, hT, emp, reg, List.replicate_succ, Rules.output_copy, Rules.output_skip, ones_append]
      have t1 := time_le Rules.copy (ones r) (fun j => j.elim0) 0 (fun j => j.elim0)
      have t2 := time_le Rules.copy (ones (r + r)) (fun j => j.elim0) 0 (fun j => j.elim0)
      have t3 := time_le Rules.skip [] (fun j => j.elim0) 0 (fun j => j.elim0)
      refine ⟨?_, ?_⟩
      · funext i; fin_cases i <;> tsimp [hR, hS, hJ, hT, emp, reg, List.replicate_succ, mul_two]
      · simp [clen, WTape.words] at t1 t2 t3 ⊢; omega
    set σ₁ := Function.update (Function.update σ qR (reg (ones (r * 2)))) qT ⟨[] :: Tl, List.replicate j []⟩
    have ih := runs_doubleLoop j (r * 2) σ₁ ([] :: Tl) (by tsimp [σ₁]) (by tsimp [σ₁, hS]) (by tsimp [σ₁, hJ])
      (by tsimp [σ₁])
    refine (Runs.loop_step (by simp [hT]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      have e : r * 2 * 2 ^ j = r * 2 ^ (j + 1) := by rw [pow_succ]; ring
      funext i; fin_cases i <;> tsimp [σ₁, e, List.replicate_succ, replicate_append_cons]
    · have e : r * 2 * 2 ^ j = 2 * (r * 2 ^ j) := by ring
      have e2 : r * 2 ^ (j + 1) = 2 * (r * 2 ^ j) := by rw [pow_succ]; ring
      rw [e, e2]
      have : r ≤ r * 2 ^ j := Nat.le_mul_of_pos_right r (by positivity)
      omega

end IntegerMultBounds.Schoenhage
