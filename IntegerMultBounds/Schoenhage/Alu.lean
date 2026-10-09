import IntegerMultBounds.Schoenhage.Wp

/-! Residue arithmetic modulo `2^N + 1` as word programs on a fixed bank of
tapes. Residues are `(N + 1)`-bit words, least significant bit first. A
register tape holds exactly one word with the head before it. The unit keeps
its constants (the width `N + 1` in unary and the word of `2^N + 1`) in
registers, takes its operands from two registers, leaves the result in a
third, and returns every scratch tape to empty. -/

namespace IntegerMultBounds.Schoenhage

open Machine Strm

/-- The number of tapes of the Schönhage–Strassen machine. -/
scoped notation "𝕋" => (48 : ℕ)

namespace Tp
abbrev aX : Fin 𝕋 := 0
abbrev aY : Fin 𝕋 := 1
abbrev aO : Fin 𝕋 := 2
abbrev aS1 : Fin 𝕋 := 3
abbrev aS2 : Fin 𝕋 := 4
abbrev aS3 : Fin 𝕋 := 5
abbrev cW : Fin 𝕋 := 6
abbrev cF : Fin 𝕋 := 8
abbrev cT : Fin 𝕋 := 9
abbrev c1 : Fin 𝕋 := 10
abbrev cN : Fin 𝕋 := 11
end Tp

open Tp

/-- The word of `2^N + 1`. -/
def fword (N : ℕ) : List Bool := bits (N + 1) (2 ^ N + 1)

/-- The unit's constants for modulus `2^N + 1`. -/
def AluConst (N : ℕ) (σ : Fin 𝕋 → WTape) : Prop :=
  σ cW = reg (ones (N + 1)) ∧ σ cF = reg (fword N)

/-- The cleanup after a two-operand operation. -/
noncomputable def cleanup : Cmd 0 𝕋 :=
  .seq (clear aX) <| .seq (clear aY) <| .seq (clear aS1) <| .seq (clear aS2) (rewind aO)

/-! ### Modular subtraction -/

/-- `x - y mod 2^N + 1` from `aX`, `aY` into `aO`. -/
noncomputable def subMod : Cmd 0 𝕋 :=
  .seq (op1 Rules.sub false aX aY aS1 (by decide) (by decide) (by decide)) <|
  .seq (back aS1) <|
  .seq (.cond aS1
    (.seq (back aS1) <|
     .seq (op1 Rules.add false aS1 cF aS2 (by decide) (by decide) (by decide)) <|
     .seq (rewind aS2) <|
     .seq (op1 Rules.take false cW aS2 aO (by decide) (by decide) (by decide)) <|
     .seq (rewind cF) (rewind cW))
    (.seq (back aS1) <|
     op0 Rules.copy false aS1 aO (by decide))) cleanup

end IntegerMultBounds.Schoenhage

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp

theorem fword_length (N : ℕ) : (fword N).length = N + 1 := by simp [fword]

theorem bval_fword {N : ℕ} (hN : 0 < N) : bval (fword N) = 2 ^ N + 1 := by
  rw [fword, bval_bits, Nat.mod_eq_of_lt]
  rw [pow_succ]
  have : 2 ≤ 2 ^ N := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  omega

/-- The residue `x - y` modulo `2^N + 1` as a word. -/
def subRes (N : ℕ) (x y : List Bool) : List Bool := bits (N + 1) ((bval x + (2 ^ N + 1) - bval y) % (2 ^ N + 1))

theorem startsOne_mk (L : List (List Bool)) (b : Bool) (w : List Bool) (R : List (List Bool)) :
    StartsOne ⟨L, (b :: w) :: R⟩ ↔ b = true := by
  constructor
  · rintro ⟨w', R', h⟩; simp at h; exact h.1.1
  · rintro rfl; exact ⟨w, R, rfl⟩

/-- Simplify banks whose tapes are named numerals. -/
syntax "tsimp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| tsimp $[[$args,*]]? $[$loc]?) => do
    let args := args.map (·.getElems) |>.getD #[]
    `(tactic| simp (config := {decide := true}) [Function.update_apply, ↓parse_syms, $args,*] $[$loc]?)

theorem runs_subMod {N : ℕ} (hN : 0 < N) (σ : Fin 𝕋 → WTape) (hc : AluConst N σ) {x y : List Bool}
    (hx : σ aX = reg x) (hy : σ aY = reg y) (hlx : x.length = N + 1) (hly : y.length = N + 1)
    (hxv : bval x < 2 ^ N + 1) (hyv : bval y < 2 ^ N + 1)
    (hO : σ aO = emp) (h1 : σ aS1 = emp) (h2 : σ aS2 = emp) :
    Runs subMod σ (· = Function.update (Function.update (Function.update σ aX emp) aY emp) aO
      (reg (subRes N x y))) (80 * N + 200) := by
  obtain ⟨hW, hF⟩ := hc
  have key := Rules.bval_subW false x y
  rw [hlx, Rules.bval_fit _ _ (by omega)] at key
  apply Runs.of_wp
  simp only [subMod, cleanup, WP, wp_op1, wp_op0, wp_back, wp_rewind, wp_clear]
  tsimp [hx, hy, hO, h1, h2, hW, hF, emp, reg, Rules.output_sub, Rules.output_copy, Rules.output_add,
    Rules.output_take, startsOne_mk]
  have hdl : (Rules.subW false x y).1.length = N + 1 := by rw [Rules.length_subW, hlx]
  have t1 := time_le Rules.sub x (fun _ => y) (N + 1) (fun _ => by simp [hly])
  have t2 := time_le Rules.add (Rules.subW false x y).1 (fun _ => fword N) (N + 1)
    (fun _ => by simp [fword_length])
  have t3 := time_le Rules.take (ones (N + 1)) (fun _ => Rules.addW false (Rules.subW false x y).1 (fword N))
    (N + 2) (fun _ => by simp [Rules.length_addW, hdl])
  have t4 := time_le Rules.copy (Rules.subW false x y).1 (fun j => j.elim0) 0 (fun j => j.elim0)
  have hFv := bval_fword hN
  revert key hdl t1 t2 t3 t4
  generalize Rules.subW false x y = D
  rcases D with ⟨d, b⟩
  intro key hdl t1 t2 t3 t4
  have hF0 : (0 : ℕ) < 2 ^ N := Nat.two_pow_pos N
  have hxy : bval x + (2 ^ N + 1) - bval y < 2 * (2 ^ N + 1) := by omega
  have e2 : ((2 ^ (N + 1) : ℕ) : ℤ) = 2 ^ (N + 1) := by push_cast; rfl
  have hdlt : bval d < 2 ^ (N + 1) := hdl ▸ bval_lt d
  cases b
  · dsimp only at *
    simp only [Bool.toNat_false, Nat.cast_zero, mul_zero, sub_zero] at key
    have hres : d = subRes N x y := by
      rw [subRes, ← bits_bval d, hdl]
      congr 1
      have e1 : bval x + (2 ^ N + 1) - bval y = (bval x - bval y) + (2 ^ N + 1) := by omega
      rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [Bool.false_eq_true, false_implies, not_false_eq_true, true_implies, true_and]
    refine ⟨?_, ?_⟩
    · rw [hres]; funext i; fin_cases i <;> tsimp [hO, h1, h2, emp]
    · simp [WTape.words, clen, hdl, Rules.length_addW, fword_length] at t1 t2 t3 t4 ⊢; omega
  · dsimp only at *
    simp only [Bool.toNat_true, Bool.toNat_false, Nat.cast_one, Nat.cast_zero, mul_one, sub_zero] at key
    have hres : Rules.fit (N + 1) (Rules.addW false d (fword N)) = subRes N x y := by
      have hfit : Rules.fit d.length (fword N) = fword N := by
        rw [hdl, ← fword_length N, Rules.fit_of_length]
      rw [Rules.fit_eq_bits, Rules.bval_addW, hfit, hFv, subRes, ← bits_mod (N + 1)]
      have hdv : bval d = bval x + 2 ^ (N + 1) - bval y := by omega
      have hlt : bval x < bval y := by omega
      congr 1
      rw [Nat.mod_eq_of_lt (show bval x + (2 ^ N + 1) - bval y < 2 ^ N + 1 by omega)]
      rw [hdv, pow_succ]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [show bval x + 2 ^ N * 2 - bval y + (2 ^ N + 1) = (bval x + (2 ^ N + 1) - bval y) + 2 ^ N * 2 by
        omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [Bool.false_eq_true, false_implies, implies_true, true_implies, not_true_eq_false,
      not_false_eq_true, and_true, true_and, not_true]
    simp only [hres]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · funext i; fin_cases i <;> tsimp [hO, h1, h2, hW, hF, emp, reg]
    · simp [WTape.words, clen, hdl, Rules.length_addW, fword_length] at t1 t2 t3 t4 ⊢; omega
    · intro h; exact absurd h (by decide)
/-! ### Modular addition -/

/-- `x + y mod 2^N + 1` from `aX`, `aY` into `aO`. -/
noncomputable def addMod : Cmd 0 𝕋 :=
  .seq (op1 Rules.add false aX aY aS1 (by decide) (by decide) (by decide)) <|
  .seq (rewind aS1) <|
  .seq (op1 Rules.sub false aS1 cF aS2 (by decide) (by decide) (by decide)) <|
  .seq (back aS2) <|
  .seq (.cond aS2
    (.seq (rewind aS1) (op1 Rules.take false cW aS1 aO (by decide) (by decide) (by decide)))
    (.seq (back aS2) (op1 Rules.take false cW aS2 aO (by decide) (by decide) (by decide)))) <|
  .seq (rewind cF) <| .seq (rewind cW) cleanup

/-- The residue `x + y` modulo `2^N + 1` as a word. -/
def addRes (N : ℕ) (x y : List Bool) : List Bool := bits (N + 1) ((bval x + bval y) % (2 ^ N + 1))

theorem runs_addMod {N : ℕ} (hN : 0 < N) (σ : Fin 𝕋 → WTape) (hc : AluConst N σ) {x y : List Bool}
    (hx : σ aX = reg x) (hy : σ aY = reg y) (hlx : x.length = N + 1) (hly : y.length = N + 1)
    (hxv : bval x < 2 ^ N + 1) (hyv : bval y < 2 ^ N + 1)
    (hO : σ aO = emp) (h1 : σ aS1 = emp) (h2 : σ aS2 = emp) :
    Runs addMod σ (· = Function.update (Function.update (Function.update σ aX emp) aY emp) aO
      (reg (addRes N x y))) (80 * N + 200) := by
  obtain ⟨hW, hF⟩ := hc
  apply Runs.of_wp
  simp only [addMod, cleanup, WP, wp_op1, wp_op0, wp_back, wp_rewind, wp_clear]
  tsimp [hx, hy, hO, h1, h2, hW, hF, emp, reg, Rules.output_sub, Rules.output_add,
    Rules.output_take, startsOne_mk]
  have hFv := bval_fword hN
  have hF0 : (0 : ℕ) < 2 ^ N := Nat.two_pow_pos N
  have hsv : bval (Rules.addW false x y) = bval x + bval y := by
    rw [Rules.bval_addW, hlx, ← hly, Rules.fit_of_length]; simp
  have hsl : (Rules.addW false x y).length = N + 2 := by rw [Rules.length_addW, hlx]
  have key := Rules.bval_subW false (Rules.addW false x y) (fword N)
  rw [hsl, Rules.bval_fit _ _ (by rw [fword_length]; omega), hFv, hsv] at key
  have hdl : (Rules.subW false (Rules.addW false x y) (fword N)).1.length = N + 2 := by
    rw [Rules.length_subW, hsl]
  have t1 := time_le Rules.add x (fun _ => y) (N + 1) (fun _ => by simp [hly])
  have t2 := time_le Rules.sub (Rules.addW false x y) (fun _ => fword N) (N + 1)
    (fun _ => by simp [fword_length])
  have t3 := time_le Rules.take (ones (N + 1)) (fun _ => Rules.addW false x y) (N + 2)
    (fun _ => by simp [hsl])
  have t4 := time_le Rules.take (ones (N + 1))
    (fun _ => (Rules.subW false (Rules.addW false x y) (fword N)).1) (N + 2) (fun _ => by simp [hdl])
  revert key hdl t2 t4
  generalize Rules.subW false (Rules.addW false x y) (fword N) = D
  rcases D with ⟨d, b⟩
  intro key hdl t2 t4
  have e2 : ((2 ^ (N + 2) : ℕ) : ℤ) = 2 ^ (N + 2) := by push_cast; rfl
  have hdlt : bval d < 2 ^ (N + 2) := hdl ▸ bval_lt d
  dsimp only at *
  cases b
  · simp only [Bool.toNat_false, Nat.cast_zero, mul_zero, sub_zero] at key
    have hres : Rules.fit (N + 1) d = addRes N x y := by
      rw [Rules.fit_eq_bits, addRes]
      congr 1
      have e1 : bval x + bval y = (bval x + bval y - (2 ^ N + 1)) + (2 ^ N + 1) := by omega
      rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [Bool.false_eq_true, false_implies, not_false_eq_true, true_implies, true_and, hres]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [hO, h1, h2, hW, hF, emp, reg]
    · simp [WTape.words, clen, hdl, hsl, fword_length] at t1 t2 t3 t4 ⊢; omega
  · simp only [Bool.toNat_true, Bool.toNat_false, Nat.cast_one, Nat.cast_zero, mul_one, sub_zero] at key
    have hres : Rules.fit (N + 1) (Rules.addW false x y) = addRes N x y := by
      rw [Rules.fit_eq_bits, addRes, hsv, Nat.mod_eq_of_lt (by omega)]
    simp only [Bool.false_eq_true, implies_true, true_implies, not_true_eq_false, and_true, hres]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · funext i; fin_cases i <;> tsimp [hO, h1, h2, hW, hF, emp, reg]
    · simp [WTape.words, clen, hdl, hsl, fword_length] at t1 t2 t3 t4 ⊢; omega
    · intro h; exact absurd h (by decide)

/-! ### Multiplication by a power of two -/

/-- Unary `N - t` into `aS3`. -/
noncomputable def mpDiff : Cmd 0 𝕋 :=
  .seq (op1 Rules.drop false cN cT aS3 (by decide) (by decide) (by decide)) <|
  .seq (rewind aS3) <| .seq (rewind cN) (rewind cT)

/-- The shifted low part into `aS1`. -/
noncomputable def mpLow : Cmd 0 𝕋 :=
  .seq (op0 (Rules.fill false) false cT aS1 (by decide)) <|
  .seq (op1 Rules.take true aS3 aX aS1 (by decide) (by decide) (by decide)) <|
  .seq (op0 (Rules.fill false) true c1 aS1 (by decide)) <|
  .seq (rewind aS1) <| .seq (rewind cT) <| .seq (rewind aS3) <| .seq (rewind c1) (rewind aX)

/-- The high part into `aY`. -/
noncomputable def mpHigh : Cmd 0 𝕋 :=
  .seq (op1 Rules.drop false aX aS3 aS2 (by decide) (by decide) (by decide)) <|
  .seq (rewind aS2) <|
  .seq (op1 Rules.take false cW aS2 aY (by decide) (by decide) (by decide)) <|
  .seq (rewind aY) <| .seq (rewind aX) <| .seq (rewind aS3) <| .seq (rewind cW) (clear aS2)

/-- Move the low part into `aX` and clear the scratch. -/
noncomputable def mpMove : Cmd 0 𝕋 :=
  .seq (clear aX) <| .seq (op0 Rules.copy false aS1 aX (by decide)) <|
  .seq (rewind aX) <| .seq (clear aS1) (clear aS3)

/-- `2^t v mod 2^N + 1` for `t ≤ N`, with `v` in `aX` and `t` in unary in `cT`. -/
noncomputable def mulPow2 : Cmd 0 𝕋 :=
  .seq mpDiff <| .seq mpLow <| .seq mpHigh <| .seq mpMove subMod

/-- The residue `2^t v` modulo `2^N + 1` as a word. -/
def mulRes (N t : ℕ) (v : List Bool) : List Bool := bits (N + 1) (2 ^ t * bval v % (2 ^ N + 1))

/-- The shifted low part, `2^t (v mod 2^(N-t))`, as an `(N+1)`-bit word. -/
def shiftLo (N t : ℕ) (v : List Bool) : List Bool :=
  List.replicate t false ++ Rules.fit (N - t) v ++ [false]

/-- The high part `v / 2^(N-t)` as an `(N+1)`-bit word. -/
def shiftHi (N t : ℕ) (v : List Bool) : List Bool := Rules.fit (N + 1) (v.drop (N - t))

theorem shift_values {N t : ℕ} (htN : t ≤ N) {v : List Bool} (hlv : v.length = N + 1) :
    (shiftLo N t v).length = N + 1 ∧ (shiftHi N t v).length = N + 1 ∧
      bval (shiftLo N t v) = 2 ^ t * (bval v % 2 ^ (N - t)) ∧
      bval (shiftHi N t v) = bval v / 2 ^ (N - t) := by
  refine ⟨by simp [shiftLo]; omega, by simp [shiftHi], ?_, ?_⟩
  · rw [shiftLo, List.append_assoc, bval_replicate_append, bval_append, Rules.bval_fit_mod]
    simp
  · rw [shiftHi, Rules.bval_fit _ _ (by simp; omega), bval_drop _ _ (by omega)]

theorem shift_mod {N t : ℕ} (hN : 0 < N) (htN : t ≤ N) {v : List Bool} (hlv : v.length = N + 1)
    (hv : bval v < 2 ^ N + 1) :
    subRes N (shiftLo N t v) (shiftHi N t v) = mulRes N t v := by
  obtain ⟨-, -, hlo, hhi⟩ := shift_values htN hlv
  rw [subRes, mulRes, hlo, hhi]
  congr 1
  set L := bval v % 2 ^ (N - t)
  set H := bval v / 2 ^ (N - t)
  have hv' : bval v = L + 2 ^ (N - t) * H := (Nat.mod_add_div _ _).symm
  have hpow : 2 ^ t * 2 ^ (N - t) = 2 ^ N := by rw [← pow_add]; congr 1; omega
  have hH : H ≤ 2 ^ t := by
    have : 2 ^ (N - t) * H ≤ 2 ^ (N - t) * 2 ^ t := by
      have h1 : 2 ^ (N - t) * H ≤ bval v := by omega
      have h2 : bval v ≤ 2 ^ N := by omega
      calc 2 ^ (N - t) * H ≤ 2 ^ N := h1.trans h2
        _ = 2 ^ (N - t) * 2 ^ t := by rw [mul_comm, hpow]
    exact Nat.le_of_mul_le_mul_left this (Nat.two_pow_pos _)
  have ht : 2 ^ t ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) htN
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd]
  refine ⟨1 - (H : ℤ), ?_⟩
  rw [Nat.cast_sub (by omega), hv']
  push_cast
  have : ((2 : ℤ) ^ t * 2 ^ (N - t)) = 2 ^ N := by exact_mod_cast hpow
  linear_combination (-(H : ℤ)) * this

theorem runs_mpDiff {N t : ℕ} (htN : t ≤ N) (σ : Fin 𝕋 → WTape) (hcN : σ cN = reg (ones N))
    (hcT : σ cT = reg (ones t)) (h3 : σ aS3 = emp) :
    Runs mpDiff σ (· = Function.update σ aS3 (reg (ones (N - t)))) (4 * N + 20) := by
  apply Runs.of_wp
  simp only [mpDiff, WP, wp_op1, wp_rewind]
  tsimp [hcN, hcT, h3, emp, reg, Rules.output_drop]
  have t1 := time_le Rules.drop (ones N) (fun _ => ones t) N (fun _ => by simp; omega)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hcN, hcT, h3, emp, reg]
  · simp at t1; omega

theorem runs_mpLow {N t : ℕ} (htN : t ≤ N) (σ : Fin 𝕋 → WTape) (hc1 : σ c1 = reg [true])
    (hcT : σ cT = reg (ones t)) (h3 : σ aS3 = reg (ones (N - t))) {v : List Bool} (hx : σ aX = reg v)
    (hlv : v.length = N + 1) (h1 : σ aS1 = emp) :
    Runs mpLow σ (· = Function.update σ aS1 (reg (shiftLo N t v))) (12 * N + 60) := by
  apply Runs.of_wp
  simp only [mpLow, WP, wp_op1, wp_op0, wp_rewind]
  tsimp [hc1, hcT, h3, hx, h1, emp, reg, Rules.output_take, Rules.output_fill]
  have t1 := time_le (Rules.fill false) (ones t) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.take (ones (N - t)) (fun _ => v) (N + 1) (fun _ => by simp [hlv])
  have t3 := time_le (Rules.fill false) [true] (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hc1, hcT, h3, hx, h1, emp, reg, shiftLo]
  · simp at t1 t2 t3 ⊢; omega

theorem runs_mpHigh {N t : ℕ} (htN : t ≤ N) (σ : Fin 𝕋 → WTape) (hW : σ cW = reg (ones (N + 1)))
    (h3 : σ aS3 = reg (ones (N - t))) {v : List Bool} (hx : σ aX = reg v) (hlv : v.length = N + 1)
    (h2 : σ aS2 = emp) (hY : σ aY = emp) :
    Runs mpHigh σ (· = Function.update σ aY (reg (shiftHi N t v))) (16 * N + 60) := by
  apply Runs.of_wp
  simp only [mpHigh, WP, wp_op1, wp_rewind, wp_clear]
  tsimp [hW, h3, hx, h2, hY, emp, reg, Rules.output_take, Rules.output_drop]
  have t1 := time_le Rules.drop v (fun _ => ones (N - t)) (N + 1) (fun _ => by simp; omega)
  have t2 := time_le Rules.take (ones (N + 1)) (fun _ => v.drop (N - t)) (N + 1)
    (fun _ => by simp; omega)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hW, h3, hx, h2, hY, emp, reg, shiftHi]
  · simp [clen, WTape.words, hlv] at t1 t2 ⊢; omega

theorem runs_mpMove {N t : ℕ} (htN : t ≤ N) (σ : Fin 𝕋 → WTape) {v : List Bool} (hx : σ aX = reg v)
    (hlv : v.length = N + 1) (h1 : σ aS1 = reg (shiftLo N t v)) (h3 : σ aS3 = reg (ones (N - t))) :
    Runs mpMove σ (· = Function.update (Function.update (Function.update σ aX (reg (shiftLo N t v)))
      aS1 emp) aS3 emp) (12 * N + 60) := by
  have hl : (shiftLo N t v).length = N + 1 := by simp [shiftLo]; omega
  apply Runs.of_wp
  simp only [mpMove, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hx, h1, h3, emp, reg, Rules.output_copy]
  have t1 := time_le Rules.copy (shiftLo N t v) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hx, h1, h3, emp, reg]
  · simp [clen, WTape.words, hlv, hl] at t1 ⊢; omega

theorem runs_mulPow2 {N t : ℕ} (hN : 0 < N) (htN : t ≤ N) (σ : Fin 𝕋 → WTape) (hc : AluConst N σ)
    (hcN : σ cN = reg (ones N)) (hc1 : σ c1 = reg [true]) (hcT : σ cT = reg (ones t))
    {v : List Bool} (hx : σ aX = reg v) (hlv : v.length = N + 1) (hv : bval v < 2 ^ N + 1)
    (hY : σ aY = emp) (hO : σ aO = emp) (h1 : σ aS1 = emp) (h2 : σ aS2 = emp) (h3 : σ aS3 = emp) :
    Runs mulPow2 σ (· = Function.update (Function.update σ aX emp) aO (reg (mulRes N t v)))
      (200 * N + 400) := by
  obtain ⟨hW, hF⟩ := hc
  obtain ⟨hl1, hl2, hv1, hv2⟩ := shift_values htN hlv
  have hlo : bval (shiftLo N t v) < 2 ^ N + 1 := by
    rw [hv1]
    have : bval v % 2 ^ (N - t) < 2 ^ (N - t) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hpow : 2 ^ t * 2 ^ (N - t) = 2 ^ N := by rw [← pow_add]; congr 1; omega
    nlinarith [Nat.two_pow_pos t]
  have hhi : bval (shiftHi N t v) < 2 ^ N + 1 := by
    rw [hv2]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hv
  unfold mulPow2
  refine (Runs.then (runs_mpDiff htN σ hcN hcT h3) <|
    Runs.then (runs_mpLow htN _ (by tsimp [hc1]) (by tsimp [hcT]) (by tsimp) (by tsimp [hx]) hlv
      (by tsimp [h1])) <|
    Runs.then (runs_mpHigh htN _ (by tsimp [hW]) (by tsimp) (by tsimp [hx]) hlv (by tsimp [h2])
      (by tsimp [hY])) <|
    Runs.then (runs_mpMove htN _ (by tsimp [hx]) hlv (by tsimp) (by tsimp)) <|
    runs_subMod hN _ ⟨by tsimp [hW], by tsimp [hF]⟩ (x := shiftLo N t v) (y := shiftHi N t v)
      (by tsimp) (by tsimp) hl1 hl2 hlo hhi (by tsimp [hO]) (by tsimp) (by tsimp [h2])).mono ?_ (by omega)
  intro σ' h
  rw [h, shift_mod hN htN hlv hv]
  funext i; fin_cases i <;> tsimp [hY, hO, h1, h2, h3, emp]

@[simp] theorem subRes_length (N : ℕ) (x y : List Bool) : (subRes N x y).length = N + 1 := by
  simp [subRes]
@[simp] theorem addRes_length (N : ℕ) (x y : List Bool) : (addRes N x y).length = N + 1 := by
  simp [addRes]
@[simp] theorem mulRes_length (N t : ℕ) (v : List Bool) : (mulRes N t v).length = N + 1 := by
  simp [mulRes]

end IntegerMultBounds.Schoenhage
