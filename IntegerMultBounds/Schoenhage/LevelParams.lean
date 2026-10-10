import IntegerMultBounds.Schoenhage.Params

/-! A level's registers from the unary outer size `pN = ones N`: the
transform exponent `k = kOf N`, the piece size, `K = 2^k`, the next size
`nextN N`, the derived unary words, the half constant, the ruler and the
unit's constants for the inner modulus. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

theorem size_le_self (n : ℕ) : Nat.size n ≤ n := by
  rw [Nat.size_le]; exact Nat.lt_two_pow_self

theorem sq_le_two_pow : ∀ s : ℕ, s * s ≤ 2 ^ (s + 1)
  | 0 => by norm_num
  | s + 1 => by
    have ih := sq_le_two_pow s
    have h2 : s < 2 ^ s := Nat.lt_two_pow_self
    rw [pow_succ, pow_succ] at *; nlinarith

theorem size_sq_le (n : ℕ) : Nat.size n * Nat.size n ≤ 4 * n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 := two_pow_pred_le h
    have h2 := sq_le_two_pow (Nat.size n)
    have hs := Nat.size_pos.mpr h
    have e : 2 ^ (Nat.size n + 1) = 4 * 2 ^ (Nat.size n - 1) := by
      rw [show Nat.size n + 1 = Nat.size n - 1 + 2 by omega, pow_add]; ring
    omega

/-! ### The exponent -/

/-- `qR = ones N`, `N` ticks on `qT`, `qB = ones 0`, from `pN`. -/
noncomputable def sizeSetupN : Cmd 0 𝕋 :=
  .seq (op0 Rules.copy false pN qR (by decide)) <| .seq (rewind pN) <| .seq (rewind qR) <|
  .seq (op0 Rules.ticks false pN qT (by decide)) <| .seq (rewind pN) <| .seq (rewind qT) <|
  .seq (emit [[]] qB) (rewind qB)

/-- `qR = ones b`, `b` ticks on `qT`, `qB = ones 0`, from `tU`. -/
noncomputable def sizeSetupU : Cmd 0 𝕋 :=
  .seq (op0 Rules.copy false tU qR (by decide)) <| .seq (rewind tU) <| .seq (rewind qR) <|
  .seq (op0 Rules.ticks false tU qT (by decide)) <| .seq (rewind tU) <| .seq (rewind qT) <|
  .seq (emit [[]] qB) (rewind qB)

theorem runs_sizeSetupN {n : ℕ} (σ : Fin 𝕋 → WTape) (hp : σ pN = reg (ones n)) (hR : σ qR = emp)
    (hT : σ qT = emp) (hB : σ qB = emp) :
    Runs sizeSetupN σ (· = Function.update (Function.update (Function.update σ qR (reg (ones n)))
        qT ⟨[], List.replicate n []⟩) qB (reg (ones 0))) (6 * n + 40) := by
  apply Runs.of_wp
  simp only [sizeSetupN, WP, wp_op0, wp_rewind, wp_emit]
  tsimp [hp, hR, hT, hB, emp, reg, Rules.output_copy, Rules.output_ticks]
  have t1 := time_le Rules.copy (ones n) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.ticks (ones n) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hp, hR, hT, hB, emp, reg, ones]
  · simp [clen] at t1 t2 ⊢; omega

theorem runs_sizeSetupU {n : ℕ} (σ : Fin 𝕋 → WTape) (hp : σ tU = reg (ones n)) (hR : σ qR = emp)
    (hT : σ qT = emp) (hB : σ qB = emp) :
    Runs sizeSetupU σ (· = Function.update (Function.update (Function.update σ qR (reg (ones n)))
        qT ⟨[], List.replicate n []⟩) qB (reg (ones 0))) (6 * n + 40) := by
  apply Runs.of_wp
  simp only [sizeSetupU, WP, wp_op0, wp_rewind, wp_emit]
  tsimp [hp, hR, hT, hB, emp, reg, Rules.output_copy, Rules.output_ticks]
  have t1 := time_le Rules.copy (ones n) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.ticks (ones n) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hp, hR, hT, hB, emp, reg, ones]
  · simp [clen] at t1 t2 ⊢; omega

/-- The bit length of `n` from its setup, onto `qB`; `qR` and `qT` emptied. -/
theorem runs_sizeOf {n : ℕ} (σ : Fin 𝕋 → WTape) (hR : σ qR = reg (ones n)) (hB : σ qB = reg (ones 0))
    (hT : σ qT = ⟨[], List.replicate n []⟩) (h1 : σ c1 = reg [true]) (hS : σ qS = emp) (hJ : σ tJ = emp) :
    Runs (.seq sizeLoop (.seq (clear qR) (clear qT))) σ
      (· = Function.update (Function.update (Function.update σ qR emp) qB (reg (ones (Nat.size n)))) qT emp)
      (150 * n + 100) := by
  have s1 := runs_sizeLoop n n 0 σ [] hR hB h1 hS hJ hT
  rw [hv_eq n n 0 (size_le_self n)] at s1
  refine (Runs.then s1 (Runs.then (runs_clear qR _) (runs_clear qT _))).mono (fun σ' h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> tsimp [emp]
  · have hs := size_le_self n
    have hq := size_sq_le n
    tsimp [reg, WTape.words, clen]
    nlinarith

/-- `pK = ones ((b - bb) / 2)` from `tU = ones b`, `qB = ones bb`; both emptied. -/
noncomputable def kFinish : Cmd 0 𝕋 :=
  .seq (op1 Rules.drop false tU qB tV (by decide) (by decide) (by decide)) <| .seq (rewind tU) <|
  .seq (rewind qB) <| .seq (rewind tV) <| .seq (op0 Rules.half false tV pK (by decide)) <|
  .seq (rewind tV) <| .seq (rewind pK) <| .seq (clear tU) <| .seq (clear qB) (clear tV)

theorem runs_kFinish {b bb : ℕ} (σ : Fin 𝕋 → WTape) (hU : σ tU = reg (ones b)) (hB : σ qB = reg (ones bb))
    (hV : σ tV = emp) (hK : σ pK = emp) :
    Runs kFinish σ (· = Function.update (Function.update (Function.update (Function.update σ
        tU emp) qB emp) tV emp) pK (reg (ones ((b - bb) / 2)))) (12 * b + 6 * bb + 60) := by
  apply Runs.of_wp
  simp only [kFinish, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hU, hB, hV, hK, emp, reg, Rules.output_drop, Rules.output_half_ones]
  have t1 := time_le Rules.drop (ones b) (fun _ => ones bb) bb (fun _ => by simp)
  have t2 := time_le Rules.half (ones (b - bb)) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hU, hB, hV, hK, emp, reg]
  · simp [clen, WTape.words] at t1 t2 ⊢; omega

/-- The exponent `kOf N` onto `pK`. -/
noncomputable def mkK : Cmd 0 𝕋 :=
  .seq sizeSetupN <| .seq (.seq sizeLoop (.seq (clear qR) (clear qT))) <| .seq (regMove qB tU (by decide)) <|
  .seq sizeSetupU <| .seq (.seq sizeLoop (.seq (clear qR) (clear qT))) kFinish

theorem runs_mkK {N : ℕ} (σ : Fin 𝕋 → WTape) (hp : σ pN = reg (ones N)) (h1 : σ c1 = reg [true])
    (hR : σ qR = emp) (hT : σ qT = emp) (hB : σ qB = emp) (hS : σ qS = emp) (hJ : σ tJ = emp)
    (hU : σ tU = emp) (hV : σ tV = emp) (hK : σ pK = emp) :
    Runs mkK σ (· = Function.update σ pK (reg (ones (kOf N)))) (400 * N + 1000) := by
  unfold mkK
  have s1 := runs_sizeSetupN σ hp hR hT hB
  set σ₁ := Function.update (Function.update (Function.update σ qR (reg (ones N)))
        qT ⟨[], List.replicate N []⟩) qB (reg (ones 0))
  have s2 := runs_sizeOf (n := N) σ₁ (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁, h1])
    (by tsimp [σ₁, hS]) (by tsimp [σ₁, hJ])
  set σ₂ := Function.update (Function.update (Function.update σ₁ qR emp) qB (reg (ones (Nat.size N)))) qT emp
  have s3 := runs_regMove (a := 0) (r := qB) (r' := tU) (by decide) σ₂ (w := ones (Nat.size N))
    (by tsimp [σ₂]) (by tsimp [σ₂, σ₁, hU])
  set σ₃ := Function.update (Function.update σ₂ qB emp) tU (reg (ones (Nat.size N)))
  have s4 := runs_sizeSetupU (n := Nat.size N) σ₃ (by tsimp [σ₃]) (by tsimp [σ₃, σ₂]) (by tsimp [σ₃, σ₂]) (by tsimp [σ₃])
  set σ₄ := Function.update (Function.update (Function.update σ₃ qR (reg (ones (Nat.size N))))
        qT ⟨[], List.replicate (Nat.size N) []⟩) qB (reg (ones 0))
  have s5 := runs_sizeOf (n := Nat.size N) σ₄ (by tsimp [σ₄]) (by tsimp [σ₄]) (by tsimp [σ₄])
    (by tsimp [σ₄, σ₃, σ₂, σ₁, h1]) (by tsimp [σ₄, σ₃, σ₂, σ₁, hS]) (by tsimp [σ₄, σ₃, σ₂, σ₁, hJ])
  set σ₅ := Function.update (Function.update (Function.update σ₄ qR emp)
    qB (reg (ones (Nat.size (Nat.size N))))) qT emp
  have s6 := runs_kFinish (b := Nat.size N) (bb := Nat.size (Nat.size N)) σ₅ (by tsimp [σ₅, σ₄, σ₃])
    (by tsimp [σ₅]) (by tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, hV]) (by tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, hK])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono
    (fun σ' h => ?_) ?_
  · rw [h]
    have e : (Nat.size N - Nat.size (Nat.size N)) / 2 = kOf N := rfl
    funext i; fin_cases i <;> tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, hR, hT, hB, hU, hV, e, emp]
  · have h1 := size_le_self N
    have h2 := size_le_self (Nat.size N)
    simp only [length_ones]
    omega

/-! ### Piece size, `K` and the next size -/

/-- `k` ticks on `qT` from `pK`. -/
noncomputable def tickK : Cmd 0 𝕋 :=
  .seq (op0 Rules.ticks false pK qT (by decide)) <| .seq (rewind pK) (rewind qT)

theorem runs_tickK {k : ℕ} (σ : Fin 𝕋 → WTape) (hK : σ pK = reg (ones k)) (hT : σ qT = emp) :
    Runs tickK σ (· = Function.update σ qT ⟨[], List.replicate k []⟩) (3 * k + 20) := by
  apply Runs.of_wp
  simp only [tickK, WP, wp_op0, wp_rewind]
  tsimp [hK, hT, emp, reg, Rules.output_ticks]
  have t1 := time_le Rules.ticks (ones k) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hK, hT, emp, reg]
  · simp [clen] at t1 ⊢; omega

/-- Copy a unary register into `qR`. -/
noncomputable def loadR (src : Fin 𝕋) (h1 : src ≠ qR) : Cmd 0 𝕋 :=
  .seq (op0 Rules.copy false src qR h1) <| .seq (rewind src) (rewind qR)

theorem runs_loadR {src : Fin 𝕋} (h1 : src ≠ qR) {n : ℕ} (σ : Fin 𝕋 → WTape) (hs : σ src = reg (ones n))
    (hR : σ qR = emp) :
    Runs (loadR src h1) σ (· = Function.update σ qR (reg (ones n))) (3 * n + 20) := by
  apply Runs.of_wp
  simp only [loadR, WP, wp_op0, wp_rewind]
  have h2 : qR ≠ src := Ne.symm h1
  simp (config := {decide := true}) only [Function.update_apply, hs, hR, h1, h2, reg, emp,
    Rules.output_copy, ↓parse_syms, WTape.cur, WTape.next, WTape.put_false]
  refine ⟨⟨by simp, by simp, by simp, by simp⟩, ?_, ?_⟩
  · funext i
    by_cases e1 : i = qR
    · subst e1; simp
    · by_cases e2 : i = src
      · subst e2; simp [e1, hs, reg]
      · simp [e1, e2]
  · have t1 := time_le Rules.copy (ones n) (fun j => j.elim0) 0 (fun j => j.elim0)
    simp [clen] at t1 ⊢; omega

/-- `qR = ones (2M + k + K)` from `cM`, `pK`, `tU`. -/
noncomputable def buildT : Cmd 0 𝕋 :=
  .seq (op0 Rules.copy false cM qR (by decide)) <| .seq (rewind cM) <|
  .seq (op0 Rules.copy true cM qR (by decide)) <| .seq (rewind cM) <|
  .seq (op0 Rules.copy true pK qR (by decide)) <| .seq (rewind pK) <|
  .seq (op0 Rules.copy true tU qR (by decide)) <| .seq (rewind tU) (rewind qR)

theorem runs_buildT {M k K : ℕ} (σ : Fin 𝕋 → WTape) (hM : σ cM = reg (ones M)) (hK : σ pK = reg (ones k))
    (hU : σ tU = reg (ones K)) (hR : σ qR = emp) :
    Runs buildT σ (· = Function.update σ qR (reg (ones (M + M + k + K)))) (10 * (M + k + K) + 60) := by
  apply Runs.of_wp
  simp only [buildT, WP, wp_op0, wp_rewind]
  tsimp [hM, hK, hU, hR, emp, reg, Rules.output_copy, ones_append]
  have t1 := time_le Rules.copy (ones M) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.copy (ones k) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t3 := time_le Rules.copy (ones K) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hM, hK, hU, hR, emp, reg]
  · simp at t1 t2 t3 ⊢; omega

/-- `cM = ones (pieceOf N)`, `tU = ones (2^k)` and `pNp = ones (nextN N)`. -/
noncomputable def mkMK : Cmd 0 𝕋 :=
  .seq (loadR pN (by decide)) <| .seq tickK <| .seq halveLoop <| .seq (clear qT) <|
  .seq (regMove qR cM (by decide)) <|
  .seq (loadR c1 (by decide)) <| .seq tickK <| .seq doubleLoop <| .seq (clear qT) <|
  .seq (regMove qR tU (by decide)) <|
  .seq buildT <| .seq tickK <| .seq halveLoop <| .seq (clear qT) <| .seq tickK <| .seq doubleLoop <|
  .seq (clear qT) (regMove qR pNp (by decide))

set_option maxHeartbeats 1000000 in
theorem runs_mkMK {N : ℕ} (σ : Fin 𝕋 → WTape) (hp : σ pN = reg (ones N)) (h1 : σ c1 = reg [true])
    (hK : σ pK = reg (ones (kOf N))) (hR : σ qR = emp) (hT : σ qT = emp) (hS : σ qS = emp) (hJ : σ tJ = emp)
    (hU : σ tU = emp) (hM : σ cM = emp) (hNp : σ pNp = emp) :
    Runs mkMK σ (· = Function.update (Function.update (Function.update σ
        cM (reg (ones (pieceOf N)))) tU (reg (ones (2 ^ kOf N)))) pNp (reg (ones (nextN N))))
      (1000 * (N + 2 ^ kOf N + kOf N) + 2000) := by
  set k := kOf N
  set M := N / 2 ^ k
  have hMdef : pieceOf N = M := rfl
  have hc1 : σ c1 = reg (ones 1) := by rw [h1]; rfl
  unfold mkMK
  have s1 := runs_loadR (src := pN) (by decide) σ hp hR
  set σ₁ := Function.update σ qR (reg (ones N))
  have s2 := runs_tickK (k := k) σ₁ (by tsimp [σ₁, hK]) (by tsimp [σ₁, hT])
  set σ₂ := Function.update σ₁ qT ⟨[], List.replicate k []⟩
  have s3 := runs_halveLoop k N σ₂ [] (by tsimp [σ₂, σ₁]) (by tsimp [σ₂, σ₁, hS]) (by tsimp [σ₂, σ₁, hJ])
    (by tsimp [σ₂])
  set σ₃ := Function.update (Function.update σ₂ qR (reg (ones M))) qT ⟨List.replicate k [] ++ [], []⟩
  have s4 := runs_clear (a := 0) qT σ₃
  set σ₄ := Function.update σ₃ qT ⟨[], []⟩
  have s5 := runs_regMove (a := 0) (r := qR) (r' := cM) (by decide) σ₄ (w := ones M) (by tsimp [σ₄, σ₃])
    (by tsimp [σ₄, σ₃, σ₂, σ₁, hM])
  set σ₅ := Function.update (Function.update σ₄ qR emp) cM (reg (ones M))
  have s6 := runs_loadR (src := c1) (n := 1) (by decide) σ₅ (by tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, hc1]) (by tsimp [σ₅])
  set σ₆ := Function.update σ₅ qR (reg (ones 1))
  have s7 := runs_tickK (k := k) σ₆ (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hK]) (by tsimp [σ₆, σ₅, σ₄, emp])
  set σ₇ := Function.update σ₆ qT ⟨[], List.replicate k []⟩
  have s8 := runs_doubleLoop k 1 σ₇ [] (by tsimp [σ₇, σ₆]) (by tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hS])
    (by tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hJ]) (by tsimp [σ₇])
  rw [one_mul] at s8
  set σ₈ := Function.update (Function.update σ₇ qR (reg (ones (2 ^ k)))) qT ⟨List.replicate k [] ++ [], []⟩
  have s9 := runs_clear (a := 0) qT σ₈
  set σ₉ := Function.update σ₈ qT ⟨[], []⟩
  have s10 := runs_regMove (a := 0) (r := qR) (r' := tU) (by decide) σ₉ (w := ones (2 ^ k)) (by tsimp [σ₉, σ₈])
    (by tsimp [σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hU])
  set τ₁ := Function.update (Function.update σ₉ qR emp) tU (reg (ones (2 ^ k)))
  have s11 := runs_buildT (M := M) (k := k) (K := 2 ^ k) τ₁ (by tsimp [τ₁, σ₉, σ₈, σ₇, σ₆, σ₅])
    (by tsimp [τ₁, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hK]) (by tsimp [τ₁]) (by tsimp [τ₁])
  set T := M + M + k + 2 ^ k
  set τ₂ := Function.update τ₁ qR (reg (ones T))
  have s12 := runs_tickK (k := k) τ₂ (by tsimp [τ₂, τ₁, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hK])
    (by tsimp [τ₂, τ₁, σ₉, emp])
  set τ₃ := Function.update τ₂ qT ⟨[], List.replicate k []⟩
  have s13 := runs_halveLoop k T τ₃ [] (by tsimp [τ₃, τ₂]) (by tsimp [τ₃, τ₂, τ₁, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃,
    σ₂, σ₁, hS]) (by tsimp [τ₃, τ₂, τ₁, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hJ]) (by tsimp [τ₃])
  set τ₄ := Function.update (Function.update τ₃ qR (reg (ones (T / 2 ^ k)))) qT ⟨List.replicate k [] ++ [], []⟩
  have s14 := runs_clear (a := 0) qT τ₄
  set τ₅ := Function.update τ₄ qT ⟨[], []⟩
  have s15 := runs_tickK (k := k) τ₅ (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hK])
    (by tsimp [τ₅, emp])
  set τ₆ := Function.update τ₅ qT ⟨[], List.replicate k []⟩
  have s16 := runs_doubleLoop k (T / 2 ^ k) τ₆ [] (by tsimp [τ₆, τ₅, τ₄])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hS])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hJ]) (by tsimp [τ₆])
  set τ₇ := Function.update (Function.update τ₆ qR (reg (ones (T / 2 ^ k * 2 ^ k))))
    qT ⟨List.replicate k [] ++ [], []⟩
  have s17 := runs_clear (a := 0) qT τ₇
  set τ₈ := Function.update τ₇ qT ⟨[], []⟩
  have s18 := runs_regMove (a := 0) (r := qR) (r' := pNp) (by decide) τ₈ (w := ones (T / 2 ^ k * 2 ^ k))
    (by tsimp [τ₈, τ₇]) (by tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hNp])
  have hN' : T / 2 ^ k * 2 ^ k = nextN N := by
    have := Nat.one_le_two_pow (n := k)
    rw [nextN, mul_comm]; congr 2
    show M + M + k + 2 ^ k = 2 * M + k + 1 + 2 ^ k - 1
    omega
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 (Runs.then s12 (Runs.then s13 (Runs.then s14
    (Runs.then s15 (Runs.then s16 (Runs.then s17 s18))))))))))))))))).mono (fun σ' h => ?_) ?_
  · rw [h, hN']
    funext i; fin_cases i <;> tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hR, hT,
      emp, hMdef]
  · have hMN : M ≤ N := Nat.div_le_self N _
    have hTT : T / 2 ^ k * 2 ^ k ≤ T := Nat.div_mul_le_self T _
    tsimp [σ₃, σ₈, τ₄, τ₇, WTape.words, clen]
    have hT : T = M + M + k + 2 ^ k := rfl
    have f1 : 2 ^ k - 1 ≤ 2 ^ k := Nat.sub_le _ _
    have f2 : T / 2 ^ k * 2 ^ k - T / 2 ^ k ≤ T / 2 ^ k * 2 ^ k := Nat.sub_le _ _
    omega

end IntegerMultBounds.Schoenhage
