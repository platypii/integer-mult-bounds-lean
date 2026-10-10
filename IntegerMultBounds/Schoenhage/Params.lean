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

/-! ### The ruler -/

/-- Alternating bits from phase `q`. -/
def altFrom : Bool → ℕ → List Bool
  | _, 0 => []
  | q, n + 1 => q :: altFrom (!q) n

namespace Rules

/-- Emit `false, true, false, …`, one bit per driver bit. -/
abbrev alt : Rule 0 where
  Q := Bool
  q0 := false
  step q _ _ := (!q, some (some q), fun _ => false)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

theorem go_alt (q : Bool) (w : List Bool) (ws : Fin 0 → List Bool) :
    (go alt q w ws).2.1 = (altFrom q w.length).map some := by
  induction w generalizing q ws with
  | nil => simp [go, altFrom]
  | cons b w ih => simp [go, ih, altFrom]

theorem output_alt (w : List Bool) (ws : Fin 0 → List Bool) :
    output alt w ws = syms [altFrom false w.length] := by
  simp [output, syms_cons, go_alt]

end Rules

theorem flatMap_copies (c : ℕ) :
    (List.replicate c Rules.Act.copy).flatMap Rules.Act.enc = List.replicate (2 * c) false := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, show 2 * (c + 1) = 2 * c + 1 + 1 by ring]
    simp [Rules.Act.enc, List.replicate_succ]

theorem flatMap_pads (p : ℕ) :
    (List.replicate p Rules.Act.pad).flatMap Rules.Act.enc = altFrom false (2 * p) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, show 2 * (p + 1) = 2 * p + 1 + 1 by ring]
    simp [Rules.Act.enc, altFrom]

/-- One non-top piece of the ruler. -/
def rpiece (M W : ℕ) : List Bool :=
  List.replicate (2 * M) false ++ altFrom false (2 * (W - M)) ++ [true, true]

/-- The top piece of the ruler. -/
def rlast (M W : ℕ) : List Bool :=
  List.replicate (2 * (M + 1)) false ++ altFrom false (2 * (W - (M + 1)))

@[simp] theorem length_altFrom (q : Bool) (n : ℕ) : (altFrom q n).length = n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp [altFrom, ih]

theorem length_rpiece (M W : ℕ) : (rpiece M W).length ≤ 2 * (M + W) + 2 := by
  simp [rpiece]; omega

theorem length_flatten_rpiece (M W K : ℕ) :
    ((List.replicate K (rpiece M W)).flatten).length ≤ K * (2 * (M + W) + 2) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.replicate_succ, List.flatten_cons, List.length_append]
    have := length_rpiece M W
    nlinarith

theorem ruler_eq (M W : ℕ) : ∀ K, Rules.ruler M W (K + 1) =
    (List.replicate K (rpiece M W)).flatten ++ rlast M W
  | 0 => by
    simp [Rules.ruler, Rules.rulerActs, rlast, flatMap_copies, flatMap_pads]
  | K + 1 => by
    have ih := ruler_eq M W K
    rw [Rules.ruler] at ih ⊢
    rw [Rules.rulerActs, List.flatMap_append, List.flatMap_append, List.flatMap_append, ih, flatMap_copies,
      flatMap_pads, List.replicate_succ, List.flatten_cons]
    simp [rpiece, Rules.Act.enc]

/-- Append one non-top piece to the ruler `cR`, once per tick of `qT`. -/
noncomputable def pieceLoop : Cmd 0 𝕋 :=
  .loop qT (.seq (op0 (Rules.fill false) true tU cR (by decide)) <| .seq (rewind tU) <|
    .seq (op0 Rules.alt true tV cR (by decide)) <| .seq (rewind tV) <|
    .seq (op0 (Rules.fill true) true tO1 cR (by decide)) <| .seq (rewind tO1) (skp qT tJ (by decide)))

theorem runs_pieceLoop {M W : ℕ} :
    ∀ (j : ℕ) (u : List Bool) (σ : Fin 𝕋 → WTape) (Tl : List (List Bool)),
      σ cR = ⟨[u], []⟩ → σ tU = reg (ones (2 * M)) → σ tV = reg (ones (2 * (W - M))) →
      σ tO1 = reg (ones 2) → σ tJ = emp → σ qT = ⟨Tl, List.replicate j []⟩ →
      Runs pieceLoop σ (· = Function.update (Function.update σ cR ⟨[u ++ (List.replicate j (rpiece M W)).flatten], []⟩)
          qT ⟨List.replicate j [] ++ Tl, []⟩) (j * (8 * (M + W) + 80))
  | 0, u, σ, Tl, hR, _, _, _, _, hT => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hR, hT]
  | j + 1, u, σ, Tl, hR, hU, hV, hO, hJ, hT => by
    have s1 : Runs (a := 0) (.seq (op0 (Rules.fill false) true tU cR (by decide)) <| .seq (rewind tU) <|
        .seq (op0 Rules.alt true tV cR (by decide)) <| .seq (rewind tV) <|
        .seq (op0 (Rules.fill true) true tO1 cR (by decide)) <| .seq (rewind tO1) (skp qT tJ (by decide))) σ
        (· = Function.update (Function.update σ cR ⟨[u ++ rpiece M W], []⟩) qT ⟨[] :: Tl, List.replicate j []⟩)
        (8 * (M + W) + 78) := by
      apply Runs.of_wp
      simp only [skp, WP, wp_op0, wp_rewind]
      tsimp [hR, hU, hV, hO, hJ, hT, emp, reg, List.replicate_succ, Rules.output_fill, Rules.output_alt,
        Rules.output_skip]
      have t1 := time_le (Rules.fill false) (ones (2 * M)) (fun j => j.elim0) 0 (fun j => j.elim0)
      have t2 := time_le Rules.alt (ones (2 * (W - M))) (fun j => j.elim0) 0 (fun j => j.elim0)
      have t3 := time_le (Rules.fill true) (ones 2) (fun j => j.elim0) 0 (fun j => j.elim0)
      have t4 := time_le Rules.skip [] (fun j => j.elim0) 0 (fun j => j.elim0)
      refine ⟨?_, ?_⟩
      · funext i; fin_cases i <;> tsimp [hR, hU, hV, hO, hJ, hT, emp, reg, List.replicate_succ, rpiece]
      · simp at t1 t2 t3 t4 ⊢; omega
    set σ₁ := Function.update (Function.update σ cR ⟨[u ++ rpiece M W], []⟩) qT ⟨[] :: Tl, List.replicate j []⟩
    have ih := runs_pieceLoop (M := M) (W := W) j (u ++ rpiece M W) σ₁ ([] :: Tl) (by tsimp [σ₁]) (by tsimp [σ₁, hU])
      (by tsimp [σ₁, hV]) (by tsimp [σ₁, hO]) (by tsimp [σ₁, hJ]) (by tsimp [σ₁])
    refine (Runs.loop_step (by simp [hT]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      funext i; fin_cases i <;> tsimp [σ₁, List.replicate_succ, replicate_append_cons]
    · nlinarith

/-- The top piece, then rewind the ruler. -/
noncomputable def lastPiece : Cmd 0 𝕋 :=
  .seq (op0 (Rules.fill false) true tO2 cR (by decide)) <| .seq (rewind tO2) <|
  .seq (op0 Rules.alt true tC cR (by decide)) <| .seq (rewind tC) (rewind cR)

/-- The ruler of `K + 1` pieces on `cR`. -/
noncomputable def rulerBuild : Cmd 0 𝕋 := .seq (emit [[]] cR) <| .seq pieceLoop lastPiece

theorem runs_rulerBuild {M W K : ℕ} (σ : Fin 𝕋 → WTape) (hR : σ cR = emp) (hU : σ tU = reg (ones (2 * M)))
    (hV : σ tV = reg (ones (2 * (W - M)))) (hO : σ tO1 = reg (ones 2))
    (hO2 : σ tO2 = reg (ones (2 * (M + 1)))) (hC : σ tC = reg (ones (2 * (W - (M + 1)))))
    (hJ : σ tJ = emp) (hT : σ qT = ⟨[], List.replicate K []⟩) :
    Runs rulerBuild σ (· = Function.update (Function.update σ cR (reg (Rules.ruler M W (K + 1))))
        qT ⟨List.replicate K [], []⟩) ((K + 2) * (12 * (M + W) + 100)) := by
  unfold rulerBuild
  have s1 := runs_emit (a := 0) [[]] cR σ (by rw [hR]; rfl)
  set σ₁ := Function.update σ cR ⟨[[]].reverse ++ (σ cR).left, []⟩
  have s2 := runs_pieceLoop (M := M) (W := W) K [] σ₁ [] (by tsimp [σ₁, hR, emp]) (by tsimp [σ₁, hU])
    (by tsimp [σ₁, hV]) (by tsimp [σ₁, hO]) (by tsimp [σ₁, hJ]) (by tsimp [σ₁, hT])
  set σ₂ := Function.update (Function.update σ₁ cR ⟨[[] ++ (List.replicate K (rpiece M W)).flatten], []⟩)
    qT ⟨List.replicate K [] ++ [], []⟩
  have s3 : Runs lastPiece σ₂ (· = Function.update (Function.update σ cR (reg (Rules.ruler M W (K + 1))))
      qT ⟨List.replicate K [], []⟩) (2 * K * (M + W + 2) + 12 * (M + W) + 100) := by
    apply Runs.of_wp
    simp only [lastPiece, WP, wp_op0, wp_rewind]
    tsimp [σ₂, σ₁, hO2, hC, emp, reg, Rules.output_fill, Rules.output_alt]
    have t1 := time_le (Rules.fill false) (ones (2 * (M + 1))) (fun j => j.elim0) 0 (fun j => j.elim0)
    have t2 := time_le Rules.alt (ones (2 * (W - (M + 1)))) (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [σ₂, σ₁, hO2, hC, emp, reg, ruler_eq, rlast]
    · have hp := Nat.mul_le_mul_left K (length_rpiece M W)
      simp at t1 t2 ⊢
      have e : 2 * K * (M + W + 2) = K * (2 * (M + W) + 2) + 2 * K := by ring
      rw [e]
      generalize K * (rpiece M W).length = X at hp ⊢
      generalize K * (2 * (M + W) + 2) = Y at hp ⊢
      omega
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun σ' h => h) ?_
  simp [clen]
  nlinarith

end IntegerMultBounds.Schoenhage
