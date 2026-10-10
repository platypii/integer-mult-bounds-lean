import IntegerMultBounds.Schoenhage.InvLayers
import IntegerMultBounds.Schoenhage.Split
import IntegerMultBounds.Schoenhage.Recomb

/-! One Schönhage–Strassen level on word tapes: cutting an operand into its
padded pieces by one pass over a ruler. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp

namespace Tp
abbrev cR : Fin 𝕋 := 31
abbrev sX : Fin 𝕋 := 32
abbrev tC : Fin 𝕋 := 33
abbrev sA : Fin 𝕋 := 34
abbrev sO : Fin 𝕋 := 35
abbrev sT1 : Fin 𝕋 := 36
abbrev sT2 : Fin 𝕋 := 37
abbrev cM : Fin 𝕋 := 38
abbrev cWA : Fin 𝕋 := 39
abbrev tC2 : Fin 𝕋 := 40
abbrev cH1 : Fin 𝕋 := 41
abbrev cU : Fin 𝕋 := 42
end Tp

/-! ### Cutting into pieces -/

/-- Cut the operand in `sX` into its padded pieces, appended to `tD`. -/
noncomputable def splitOp : Cmd 0 𝕋 :=
  .seq (op1 Rules.split false cR sX tD (by decide) (by decide) (by decide)) <| .seq (rewind cR) (clear sX)

theorem runs_splitOp {M W K : ℕ} (hMW : M + 1 ≤ W) (hK : 0 < K) (σ : Fin 𝕋 → WTape) {v : List Bool}
    (hv : bval v < 2 ^ (M * K + 1)) {Dl : List (List Bool)}
    (hR : σ cR = reg (Rules.ruler M W K)) (hX : σ sX = reg v) (hD : σ tD = ⟨Dl, []⟩) :
    Runs splitOp σ (· = Function.update (Function.update σ sX emp) tD
        ⟨((pieces M K (bval v)).map (bits W)).reverse ++ Dl, []⟩)
      (2 * (Rules.ruler M W K).length + 3 * v.length + 20) := by
  apply Runs.of_wp
  simp only [splitOp, WP, wp_op1, wp_rewind, wp_clear]
  tsimp [hR, hX, hD, emp, reg, Rules.output_split_ruler hMW hK v hv]
  have t1 := time_le Rules.split (Rules.ruler M W K) (fun _ => v) v.length (fun _ => le_rfl)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hR, hX, hD, emp, reg]
  · simp [clen, WTape.words] at t1 ⊢; omega

/-! ### Shifted sums through a window -/

/-- The low `M`-bit chunks a window emits while adding the words `cs`. -/
def chunks (M : ℕ) : ℕ → List ℕ → List Bool
  | _, [] => []
  | a, c :: cs => bits M (a + c) ++ chunks M ((a + c) / 2 ^ M) cs

/-- The window left after adding the words `cs`. -/
def winFin (M : ℕ) : ℕ → List ℕ → ℕ
  | a, [] => a
  | a, c :: cs => winFin M ((a + c) / 2 ^ M) cs

theorem winFin_lt {M W : ℕ} (hM : 1 ≤ M) : ∀ (a : ℕ) (cs : List ℕ), a < 2 ^ W →
    (∀ c ∈ cs, c < 2 ^ (W - 1)) → winFin M a cs < 2 ^ W
  | a, [], ha, _ => ha
  | a, c :: cs, ha, hc => by
    apply winFin_lt hM _ cs _ (fun x hx => hc x (by simp [hx]))
    have h1 := hc c (by simp)
    have h2 : 2 ^ (W - 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ≤ 2 ^ M := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos M)]
    nlinarith

theorem bval_window {M W : ℕ} (hM : 1 ≤ M) : ∀ (a : ℕ) (cs : List ℕ), a < 2 ^ W →
    (∀ c ∈ cs, c < 2 ^ (W - 1)) →
    bval (chunks M a cs ++ bits W (winFin M a cs)) = a + wsum M cs
  | a, [], ha, _ => by simp [chunks, winFin, wsum, bval_bits, Nat.mod_eq_of_lt ha]
  | a, c :: cs, ha, hc => by
    have h1 := hc c (by simp)
    have h2 : 2 ^ (W - 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ≤ 2 ^ M := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM
    have hlt : (a + c) / 2 ^ M < 2 ^ W := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos M)]; nlinarith
    have ih := bval_window hM ((a + c) / 2 ^ M) cs hlt (fun x hx => hc x (by simp [hx]))
    simp only [chunks, winFin, wsum, List.append_assoc]
    rw [bval_append, ih, length_bits, bval_bits]
    have := Nat.mod_add_div (a + c) (2 ^ M)
    nlinarith

/-- One window step: add the next word of `tC`, emit the low `M` bits, shift. -/
noncomputable def winStep : Cmd 0 𝕋 :=
  .seq (op1 Rules.add false sA tC sT1 (by decide) (by decide) (by decide)) <| .seq (clear sA) <|
  .seq (rewind sT1) <|
  .seq (op1 Rules.take true cM sT1 sO (by decide) (by decide) (by decide)) <| .seq (rewind cM) <|
  .seq (rewind sT1) <|
  .seq (op1 Rules.drop false sT1 cM sT2 (by decide) (by decide) (by decide)) <| .seq (rewind cM) <|
  .seq (clear sT1) <| .seq (rewind sT2) <|
  .seq (op1 Rules.take false cWA sT2 sA (by decide) (by decide) (by decide)) <| .seq (rewind cWA) <|
  .seq (clear sT2) (rewind sA)

theorem runs_winStep {M W Wc a c : ℕ} (hWc : Wc ≤ W) (ha : a < 2 ^ W) (hc : c < 2 ^ Wc) (hMW : M ≤ W)
    (σ : Fin 𝕋 → WTape) {o : List Bool} {Cl Cr : List (List Bool)}
    (hA : σ sA = reg (bits W a)) (hC : σ tC = ⟨Cl, bits Wc c :: Cr⟩) (hO : σ sO = ⟨[o], []⟩)
    (h1 : σ sT1 = emp) (h2 : σ sT2 = emp) (hM : σ cM = reg (ones M)) (hW : σ cWA = reg (ones W)) :
    Runs winStep σ (· = Function.update (Function.update (Function.update σ
        sA (reg (bits W ((a + c) / 2 ^ M)))) tC ⟨bits Wc c :: Cl, Cr⟩) sO ⟨[o ++ bits M (a + c)], []⟩)
      (40 * W + 100) := by
  have hv : bval (Rules.addW false (bits W a) (bits Wc c)) = a + c := by
    rw [Rules.bval_addW, length_bits, Rules.bval_fit _ _ (by simp; omega), bval_bits, bval_bits,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc]; simp
  have e1 : Rules.fit M (Rules.addW false (bits W a) (bits Wc c)) = bits M (a + c) := by
    rw [Rules.fit_eq_bits, hv]
  have e2 : Rules.fit W ((Rules.addW false (bits W a) (bits Wc c)).drop M) = bits W ((a + c) / 2 ^ M) := by
    rw [Rules.fit_eq_bits, Rules.bval_drop', hv]
  have hl : (Rules.addW false (bits W a) (bits Wc c)).length = W + 1 := by
    rw [Rules.length_addW, length_bits]
  apply Runs.of_wp
  simp only [winStep, WP, wp_op1, wp_rewind, wp_clear]
  tsimp [hA, hC, hO, h1, h2, hM, hW, emp, reg, Rules.output_add, Rules.output_take, Rules.output_drop, e1, e2]
  have t1 := time_le Rules.add (bits W a) (fun _ => bits Wc c) Wc (fun _ => by simp)
  have t2 := time_le Rules.take (ones M) (fun _ => Rules.addW false (bits W a) (bits Wc c)) (W + 1)
    (fun _ => by simp [hl])
  have t3 := time_le Rules.drop (Rules.addW false (bits W a) (bits Wc c)) (fun _ => ones M) M
    (fun _ => by simp)
  have t4 := time_le Rules.take (ones W) (fun _ => (Rules.addW false (bits W a) (bits Wc c)).drop M) (W + 1)
    (fun _ => by simp [hl])
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hA, hC, hO, h1, h2, hM, hW, emp, reg]
  · simp [clen, WTape.words, hl] at t1 t2 t3 t4 ⊢; omega

/-- The window over every word of `tC`. -/
noncomputable def winLoop : Cmd 0 𝕋 := .loop tC winStep

theorem runs_winLoop {M W Wc : ℕ} (hM : 1 ≤ M) (hWc : Wc + 1 ≤ W) (hMW : M ≤ W) :
    ∀ (cs : List ℕ) (a : ℕ) (σ : Fin 𝕋 → WTape) (o : List Bool) (Cl : List (List Bool)),
      a < 2 ^ W → (∀ c ∈ cs, c < 2 ^ Wc) →
      σ sA = reg (bits W a) → σ tC = ⟨Cl, cs.map (bits Wc)⟩ → σ sO = ⟨[o], []⟩ →
      σ sT1 = emp → σ sT2 = emp → σ cM = reg (ones M) → σ cWA = reg (ones W) →
      Runs winLoop σ (· = Function.update (Function.update (Function.update σ
          sA (reg (bits W (winFin M a cs)))) tC ⟨(cs.map (bits Wc)).reverse ++ Cl, []⟩)
          sO ⟨[o ++ chunks M a cs], []⟩)
        (cs.length * (40 * W + 102))
  | [], a, σ, o, Cl, _, _, hA, hC, hO, _, _, _, _ => by
    refine (Runs.loop_done (by simp [hC]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hA, hC, hO, winFin, chunks]
  | c :: cs, a, σ, o, Cl, ha, hcs, hA, hC, hO, h1, h2, hMr, hW => by
    have hc := hcs c (by simp)
    have hcW : c < 2 ^ (W - 1) :=
      lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h3 : 2 ≤ 2 ^ M := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM
    have h4 : 2 ^ (W - 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hlt : (a + c) / 2 ^ M < 2 ^ W := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos M)]; nlinarith
    have hs := runs_winStep (by omega) ha hc hMW σ hA (by simpa using hC) hO h1 h2 hMr hW
    set σ₁ := Function.update (Function.update (Function.update σ
        sA (reg (bits W ((a + c) / 2 ^ M)))) tC ⟨bits Wc c :: Cl, cs.map (bits Wc)⟩)
        sO ⟨[o ++ bits M (a + c)], []⟩ with hσ₁
    have ih := runs_winLoop hM hWc hMW cs ((a + c) / 2 ^ M) σ₁ (o ++ bits M (a + c)) (bits Wc c :: Cl)
      hlt (fun x hx => hcs x (by simp [hx])) (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁])
      (by tsimp [σ₁, h1]) (by tsimp [σ₁, h2]) (by tsimp [σ₁, hMr]) (by tsimp [σ₁, hW])
    refine (Runs.loop_step (by simp [hC]) (hs.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      funext i; fin_cases i <;> tsimp [σ₁, winFin, chunks]
    · simp only [List.length_cons]; nlinarith

theorem length_chunks (M : ℕ) : ∀ (a : ℕ) (cs : List ℕ), (chunks M a cs).length = M * cs.length
  | _, [] => by simp [chunks]
  | a, c :: cs => by
    simp only [chunks, List.length_append, length_bits, length_chunks M _ cs, List.length_cons]; ring

/-- Start the window: an empty output word and a zero window. -/
noncomputable def winInit : Cmd 0 𝕋 :=
  .seq (emit [[]] sO) <| .seq (op0 (Rules.fill false) false cWA sA (by decide)) <| .seq (rewind cWA) (rewind sA)

/-- Append the last window to the output word. -/
noncomputable def winDone : Cmd 0 𝕋 := .seq (op0 Rules.copy true sA sO (by decide)) (clear sA)

/-- The shifted sum `Σ cᵢ 2^(M i)` of the words of `tC`, as one word in `sO`. -/
noncomputable def winSum : Cmd 0 𝕋 := .seq winInit <| .seq winLoop winDone

theorem runs_winSum {M W Wc : ℕ} (hM : 1 ≤ M) (hWc : Wc + 1 ≤ W) (hMW : M ≤ W)
    (cs : List ℕ) (hcs : ∀ c ∈ cs, c < 2 ^ Wc) (σ : Fin 𝕋 → WTape) {Cl : List (List Bool)}
    (hA : σ sA = emp) (hC : σ tC = ⟨Cl, cs.map (bits Wc)⟩) (hO : σ sO = emp)
    (h1 : σ sT1 = emp) (h2 : σ sT2 = emp) (hMr : σ cM = reg (ones M)) (hW : σ cWA = reg (ones W)) :
    ∃ z : List Bool, bval z = wsum M cs ∧ z.length = M * cs.length + W ∧
      Runs winSum σ (· = Function.update (Function.update σ tC ⟨(cs.map (bits Wc)).reverse ++ Cl, []⟩)
        sO ⟨[z], []⟩) ((cs.length + 1) * (40 * W + 110)) := by
  have hcs' : ∀ c ∈ cs, c < 2 ^ (W - 1) := fun c hc =>
    lt_of_lt_of_le (hcs c hc) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hval := bval_window hM 0 cs (Nat.two_pow_pos W) hcs'
  refine ⟨chunks M 0 cs ++ bits W (winFin M 0 cs), by simpa using hval, by simp [length_chunks], ?_⟩
  have s1 : Runs winInit σ (· = Function.update (Function.update σ sO ⟨[[]], []⟩) sA (reg (bits W 0)))
      (4 * W + 30) := by
    apply Runs.of_wp
    simp only [winInit, WP, wp_emit, wp_op0, wp_rewind]
    tsimp [hA, hO, hW, emp, reg, Rules.output_fill, Rules.bits_zero]
    have t1 := time_le (Rules.fill false) (ones W) (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [hA, hO, hW, emp, reg]
    · simp at t1 ⊢; omega
  set σ₁ := Function.update (Function.update σ sO ⟨[[]], []⟩) sA (reg (bits W 0))
  have s2 := runs_winLoop hM hWc hMW cs 0 σ₁ [] Cl (Nat.two_pow_pos W) hcs (by tsimp [σ₁])
    (by tsimp [σ₁, hC]) (by tsimp [σ₁]) (by tsimp [σ₁, h1]) (by tsimp [σ₁, h2]) (by tsimp [σ₁, hMr])
    (by tsimp [σ₁, hW])
  set σ₂ := Function.update (Function.update (Function.update σ₁
          sA (reg (bits W (winFin M 0 cs)))) tC ⟨(cs.map (bits Wc)).reverse ++ Cl, []⟩)
          sO ⟨[[] ++ chunks M 0 cs], []⟩
  have s3 : Runs winDone σ₂ (· = Function.update (Function.update σ tC ⟨(cs.map (bits Wc)).reverse ++ Cl, []⟩)
        sO ⟨[chunks M 0 cs ++ bits W (winFin M 0 cs)], []⟩) (4 * W + 20) := by
    apply Runs.of_wp
    simp only [winDone, WP, wp_op0, wp_clear]
    tsimp [σ₂, σ₁, emp, reg, Rules.output_copy]
    have t1 := time_le Rules.copy (bits W (winFin M 0 cs)) (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [σ₂, σ₁, hA, hO, emp, reg]
    · simp [clen, WTape.words] at t1 ⊢; omega
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun σ' h => h) ?_
  nlinarith

/-! ### Reduction modulo `2^N + 1` -/

/-- Load the low and high `N`-bit halves of `sO` into the unit's operands. -/
noncomputable def redPrep : Cmd 0 𝕋 :=
  .seq (rewind sO) <|
  .seq (op1 Rules.take false cN sO sT1 (by decide) (by decide) (by decide)) <| .seq (rewind cN) <|
  .seq (rewind sO) <| .seq (rewind sT1) <|
  .seq (op1 Rules.take false cW sT1 aX (by decide) (by decide) (by decide)) <| .seq (rewind cW) <|
  .seq (clear sT1) <| .seq (rewind aX) <|
  .seq (op1 Rules.drop false sO cN sT2 (by decide) (by decide) (by decide)) <| .seq (rewind cN) <|
  .seq (clear sO) <| .seq (rewind sT2) <|
  .seq (op1 Rules.take false cW sT2 aY (by decide) (by decide) (by decide)) <| .seq (rewind cW) <|
  .seq (clear sT2) (rewind aY)

/-- `Z mod 2^N + 1` from the word of `Z` in `sO`, into `aO`. -/
noncomputable def redOp : Cmd 0 𝕋 := .seq redPrep subMod

set_option maxHeartbeats 1000000 in
theorem runs_redOp {N : ℕ} (hN : 0 < N) (σ : Fin 𝕋 → WTape) (hr : AluReady N σ) {z : List Bool}
    (hZ : bval z < 2 ^ (2 * N)) (hO : σ sO = ⟨[z], []⟩) (h1 : σ sT1 = emp) (h2 : σ sT2 = emp) :
    Runs redOp σ (· = Function.update (Function.update σ sO emp) aO (reg (rwd N (red N (bval z)))))
      (12 * z.length + 120 * N + 400) := by
  obtain ⟨⟨hW, hF⟩, hcN, hc1, hX, hY, hAO, hS1, hS2, hS3, hbX, hbY⟩ := hr
  have e1 : Rules.fit (N + 1) (Rules.fit N z) = bits (N + 1) (bval z % 2 ^ N) := by
    rw [Rules.fit_eq_bits, Rules.bval_fit_mod]
  have e2 : Rules.fit (N + 1) (z.drop N) = bits (N + 1) (bval z / 2 ^ N) := by
    rw [Rules.fit_eq_bits, Rules.bval_drop']
  have hb : bval z / 2 ^ N < 2 ^ N := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos N), ← pow_add]; rwa [two_mul] at hZ
  have ha : bval z % 2 ^ N < 2 ^ N := Nat.mod_lt _ (Nat.two_pow_pos N)
  have s1 : Runs redPrep σ (· = Function.update (Function.update (Function.update σ sO emp)
      aX (reg (bits (N + 1) (bval z % 2 ^ N)))) aY (reg (bits (N + 1) (bval z / 2 ^ N))))
      (12 * z.length + 30 * N + 100) := by
    apply Runs.of_wp
    simp only [redPrep, WP, wp_op1, wp_rewind, wp_clear]
    tsimp [hO, hW, hcN, hX, hY, h1, h2, emp, reg, Rules.output_take, Rules.output_drop, e1, e2]
    have t1 := time_le Rules.take (ones N) (fun _ => z) z.length (fun _ => le_rfl)
    have t2 := time_le Rules.take (ones (N + 1)) (fun _ => Rules.fit N z) N (fun _ => by simp)
    have t3 := time_le Rules.drop z (fun _ => ones N) N (fun _ => by simp)
    have t4 := time_le Rules.take (ones (N + 1)) (fun _ => z.drop N) z.length (fun _ => by simp)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [hO, hW, hcN, hX, hY, h1, h2, emp, reg]
    · simp [clen, WTape.words] at t1 t2 t3 t4 ⊢
      omega
  set σ₁ := Function.update (Function.update (Function.update σ sO emp)
      aX (reg (bits (N + 1) (bval z % 2 ^ N)))) aY (reg (bits (N + 1) (bval z / 2 ^ N)))
  have hv1 : bval (bits (N + 1) (bval z % 2 ^ N)) = bval z % 2 ^ N := by
    rw [bval_bits, Nat.mod_eq_of_lt (by rw [pow_succ]; omega)]
  have hv2 : bval (bits (N + 1) (bval z / 2 ^ N)) = bval z / 2 ^ N := by
    rw [bval_bits, Nat.mod_eq_of_lt (by rw [pow_succ]; omega)]
  have s2 := runs_subMod hN σ₁ ⟨by tsimp [σ₁, hW], by tsimp [σ₁, hF]⟩
    (x := bits (N + 1) (bval z % 2 ^ N)) (y := bits (N + 1) (bval z / 2 ^ N)) (by tsimp [σ₁]) (by tsimp [σ₁])
    (by simp) (by simp) (by rw [hv1]; omega) (by rw [hv2]; omega) (by tsimp [σ₁, hAO])
    (by tsimp [σ₁, hS1]) (by tsimp [σ₁, hS2])
  refine (Runs.then s1 s2).mono (fun σ' h => ?_) (by omega)
  rw [h]
  have e3 : subRes N (bits (N + 1) (bval z % 2 ^ N)) (bits (N + 1) (bval z / 2 ^ N)) =
      rwd N (red N (bval z)) := by
    rw [subRes, hv1, hv2, rwd, red, Fm]
  rw [e3]
  funext i; fin_cases i <;> tsimp [σ₁, hO, hX, hY, emp]

/-! ### Descaling and the sign split -/

/-- Load the next word of `tD` and divide it by `2^k` (shift `cT = N - k`, then negate). -/
noncomputable def descaleOp : Cmd 0 𝕋 :=
  .seq (regIn tD aX (by decide)) <| .seq mulPow2 <| .seq (regMove aO aY (by decide)) negMod

theorem runs_descaleOp {N k w : ℕ} (hN : 0 < N) (hw : w < 2 ^ N + 1) (σ : Fin 𝕋 → WTape)
    (hr : AluReady N σ) (hcT : σ cT = reg (ones (N - k))) {Dl Dr : List (List Bool)}
    (hD : σ tD = ⟨Dl, rwd N w :: Dr⟩) :
    Runs descaleOp σ (· = Function.update (Function.update σ tD ⟨rwd N w :: Dl, Dr⟩)
        aO (reg (rwd N (descale N k w)))) (300 * N + 700) := by
  obtain ⟨⟨hW, hF⟩, hcN, hc1, hX, hY, hAO, hS1, hS2, hS3, hbX, hbY⟩ := hr
  unfold descaleOp
  have s1 := runs_regIn (a := 0) (s := tD) (r := aX) (by decide) σ hD hX
  set σ₁ := Function.update (Function.update σ tD ⟨rwd N w :: Dl, Dr⟩) aX (reg (rwd N w))
  have s2 := runs_mulPow2 (N := N) (t := N - k) hN (Nat.sub_le N k) σ₁ ⟨by tsimp [σ₁, hW], by tsimp [σ₁, hF]⟩
    (by tsimp [σ₁, hcN]) (by tsimp [σ₁, hc1]) (by tsimp [σ₁, hcT]) (v := rwd N w) (by tsimp [σ₁])
    (rwd_length N w) (by rw [bval_rwd hw]; exact hw) (by tsimp [σ₁, hY]) (by tsimp [σ₁, hAO])
    (by tsimp [σ₁, hS1]) (by tsimp [σ₁, hS2]) (by tsimp [σ₁, hS3])
  set σ₂ := Function.update (Function.update σ₁ aX emp) aO (reg (mulRes N (N - k) (rwd N w)))
  have s3 := runs_regMove (a := 0) (r := aO) (r' := aY) (by decide) σ₂ (w := mulRes N (N - k) (rwd N w))
    (by tsimp [σ₂]) (by tsimp [σ₂, σ₁, hY])
  set σ₃ := Function.update (Function.update σ₂ aO emp) aY (reg (mulRes N (N - k) (rwd N w)))
  have hm : bval (mulRes N (N - k) (rwd N w)) = 2 ^ (N - k) * w % (2 ^ N + 1) := by
    rw [mulRes_rwd _ _ _ hw, bval_rwd (mod_lt' _ _)]
  have s4 := runs_negMod hN σ₃ ⟨by tsimp [σ₃, σ₂, σ₁, hW], by tsimp [σ₃, σ₂, σ₁, hF]⟩
    (v := mulRes N (N - k) (rwd N w)) (by tsimp [σ₃]) (by simp) (by rw [hm]; exact mod_lt' _ _)
    (by tsimp [σ₃, σ₂]) (by tsimp [σ₃]) (by tsimp [σ₃, σ₂, σ₁, hS1]) (by tsimp [σ₃, σ₂, σ₁, hS2])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun σ' h => ?_) ?_
  · rw [h, hm]
    have e : (2 ^ N + 1 - 2 ^ (N - k) * w % (2 ^ N + 1)) % (2 ^ N + 1) = descale N k w := rfl
    rw [e]
    funext i; fin_cases i <;> tsimp [σ₃, σ₂, σ₁, hX, hY, hAO, emp]
  · simp [rwd_length]; omega

theorem subW_borrow (x y : List Bool) (h : y.length = x.length) :
    (Rules.subW false x y).2 = decide (bval x < bval y) := by
  have e := Rules.bval_subW false x y
  rw [← h, Rules.fit_of_length, h] at e
  have h1 := bval_lt (Rules.subW false x y).1
  rw [Rules.length_subW] at h1
  have h2 := bval_lt x
  have h3 := bval_lt y
  rw [h] at h3
  have hP : ((2 ^ x.length : ℕ) : ℤ) = 2 ^ x.length := by push_cast; ring
  cases hb : (Rules.subW false x y).2 <;> simp only [hb, Bool.toNat_false, Bool.toNat_true] at e <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_lt,
      eq_comm (a := false), eq_comm (a := true)] <;> push_cast at e <;> omega

/-- Compare the descaled coefficient in `aO` with `2^(N-1) + 1`: the borrow word becomes current in `sT1`. -/
noncomputable def signTest : Cmd 0 𝕋 :=
  .seq (op1 Rules.sub false aO cH1 sT1 (by decide) (by decide) (by decide)) <| .seq (rewind aO) <|
  .seq (rewind cH1) (back sT1)

/-- The half constant `2^(N-1) + 1`. -/
def hword (N : ℕ) : List Bool := bits (N + 1) (2 ^ (N - 1) + 1)

theorem runs_signTest {N d : ℕ} (hN : 0 < N) (hd : d < 2 ^ N + 1) (σ : Fin 𝕋 → WTape)
    (hO : σ aO = reg (rwd N d)) (hH : σ cH1 = reg (hword N)) (hT : σ sT1 = emp) :
    ∃ diff : List Bool, diff.length = N + 1 ∧ Runs signTest σ (· = Function.update σ sT1 ⟨[diff], [[decide (2 * d < 2 ^ N + 1)]]⟩)
      (6 * N + 40) := by
  have hh : bval (hword N) = 2 ^ (N - 1) + 1 := by
    rw [hword, bval_bits, Nat.mod_eq_of_lt]
    have : 2 ^ N = 2 * 2 ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
    rw [pow_succ]; have := Nat.two_pow_pos (N - 1); omega
  have hb : (Rules.subW false (rwd N d) (hword N)).2 = decide (2 * d < 2 ^ N + 1) := by
    rw [subW_borrow _ _ (by simp [hword, rwd]), bval_rwd hd, hh]
    have : 2 ^ N = 2 * 2 ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
    by_cases h : d < 2 ^ (N - 1) + 1
    · simp [h]; omega
    · simp [h]; omega
  refine ⟨(Rules.subW false (rwd N d) (hword N)).1, by rw [Rules.length_subW, rwd_length], ?_⟩
  apply Runs.of_wp
  simp only [signTest, WP, wp_op1, wp_rewind, wp_back]
  tsimp [hO, hH, hT, emp, reg, Rules.output_sub]
  have t1 := time_le Rules.sub (rwd N d) (fun _ => hword N) (N + 1) (fun _ => by simp [hword])
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hO, hH, hT, emp, reg, hb]
  · simp [rwd_length, hword] at t1 ⊢; omega

/-- Nonnegative coefficient: to `tC`, a zero to `tC2`. -/
noncomputable def posBr : Cmd 0 𝕋 :=
  .seq (regOut aO tC (by decide)) <| .seq (op0 (Rules.fill false) false cW tC2 (by decide)) (rewind cW)

/-- Negative coefficient: its negation to `tC2`, a zero to `tC`. -/
noncomputable def negBr : Cmd 0 𝕋 :=
  .seq (regMove aO aY (by decide)) <| .seq negMod <| .seq (regOut aO tC2 (by decide)) <|
  .seq (op0 (Rules.fill false) false cW tC (by decide)) (rewind cW)

/-- Route by the borrow word. -/
noncomputable def route : Cmd 0 𝕋 := .cond sT1 posBr negBr

theorem rwd_zero (N : ℕ) : rwd N 0 = List.replicate (N + 1) false := by
  rw [rwd, Rules.bits_zero]

theorem runs_route {N d : ℕ} (hN : 0 < N) (hd : d < 2 ^ N + 1) (σ : Fin 𝕋 → WTape)
    (hr : AluReady N (Function.update σ aO emp))
    {diff : List Bool} {C1 C2 : List (List Bool)}
    (hT : σ sT1 = ⟨[diff], [[decide (2 * d < 2 ^ N + 1)]]⟩) (hO : σ aO = reg (rwd N d))
    (hC : σ tC = ⟨C1, []⟩) (hC2 : σ tC2 = ⟨C2, []⟩) :
    Runs route σ (· = Function.update (Function.update (Function.update σ aO emp)
        tC ⟨rwd N (posPart N d) :: C1, []⟩) tC2 ⟨rwd N (negPart N d) :: C2, []⟩) (110 * N + 300) := by
  obtain ⟨⟨hW, hF⟩, hcN, hc1, hX, hY, -, hS1, hS2, hS3, -, -⟩ := hr
  tsimp at hW hF hcN hc1 hX hY hS1 hS2 hS3
  unfold route
  by_cases hs : 2 * d < 2 ^ N + 1
  · refine Runs.cond_true (by rw [hT]; simp [startsOne_mk, hs]) ?_
    apply Runs.of_wp
    simp only [posBr, regOut, cpy, WP, wp_op0, wp_clear, wp_rewind]
    tsimp [hO, hC, hC2, hW, emp, reg, Rules.output_copy, Rules.output_fill]
    have t1 := time_le Rules.copy (rwd N d) (fun j => j.elim0) 0 (fun j => j.elim0)
    have t2 := time_le (Rules.fill false) (ones (N + 1)) (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · have e1 : posPart N d = d := by simp [posPart, Fm, hs]
      have e2 : negPart N d = 0 := by simp [negPart, Fm, hs]
      funext i; fin_cases i <;> tsimp [hO, hC, hC2, hW, emp, reg, e1, e2, rwd_zero]
    · simp [clen, WTape.words, rwd_length] at t1 t2 ⊢; omega
  · refine Runs.cond_false (by rw [hT]; simp [startsOne_mk, hs]) ?_
    unfold negBr
    have s1 := runs_regMove (a := 0) (r := aO) (r' := aY) (by decide) σ (w := rwd N d) hO hY
    set σ₁ := Function.update (Function.update σ aO emp) aY (reg (rwd N d))
    have s2 := runs_negMod hN σ₁ ⟨by tsimp [σ₁, hW], by tsimp [σ₁, hF]⟩ (v := rwd N d) (by tsimp [σ₁])
      (rwd_length N d) (by rw [bval_rwd hd]; exact hd) (by tsimp [σ₁, hX]) (by tsimp [σ₁])
      (by tsimp [σ₁, hS1]) (by tsimp [σ₁, hS2])
    set σ₂ := Function.update (Function.update σ₁ aY emp) aO
      (reg (rwd N ((2 ^ N + 1 - bval (rwd N d)) % (2 ^ N + 1))))
    have s3 : Runs (a := 0) (.seq (regOut aO tC2 (by decide)) <|
        .seq (op0 (Rules.fill false) false cW tC (by decide)) (rewind cW)) σ₂
        (· = Function.update (Function.update (Function.update σ aO emp)
          tC ⟨rwd N (posPart N d) :: C1, []⟩) tC2 ⟨rwd N (negPart N d) :: C2, []⟩) (8 * N + 50) := by
      have e1 : posPart N d = 0 := by simp [posPart, Fm, hs]
      have e2 : negPart N d = (2 ^ N + 1 - bval (rwd N d)) % (2 ^ N + 1) := by
        rw [bval_rwd hd, Nat.mod_eq_of_lt (show 2 ^ N + 1 - d < 2 ^ N + 1 by omega)]; simp [negPart, Fm, hs]
      apply Runs.of_wp
      simp only [regOut, cpy, WP, wp_op0, wp_clear, wp_rewind]
      tsimp [σ₂, σ₁, hO, hC, hC2, hW, emp, reg, Rules.output_copy, Rules.output_fill]
      have t1 := time_le Rules.copy (rwd N ((2 ^ N + 1 - bval (rwd N d)) % (2 ^ N + 1))) (fun j => j.elim0) 0
        (fun j => j.elim0)
      have t2 := time_le (Rules.fill false) (ones (N + 1)) (fun j => j.elim0) 0 (fun j => j.elim0)
      refine ⟨?_, ?_⟩
      · funext i; fin_cases i <;> tsimp [σ₂, σ₁, hO, hC, hC2, hW, hY, emp, reg, e1, e2, rwd_zero]
      · simp [clen, WTape.words, rwd_length] at t1 t2 ⊢; omega
    exact (Runs.then s1 (Runs.then s2 s3)).mono (fun σ' h => h) (by rw [rwd_length]; omega)

/-- One coefficient of the up-sweep: descale, then route by sign. -/
noncomputable def coefStep : Cmd 0 𝕋 := .seq descaleOp <| .seq signTest <| .seq route (clear sT1)

theorem runs_coefStep {N k w : ℕ} (hN : 0 < N) (hw : w < 2 ^ N + 1) (σ : Fin 𝕋 → WTape)
    (hr : AluReady N σ) (hcT : σ cT = reg (ones (N - k))) (hH : σ cH1 = reg (hword N))
    (hT : σ sT1 = emp) {Dl Dr C1 C2 : List (List Bool)}
    (hD : σ tD = ⟨Dl, rwd N w :: Dr⟩) (hC : σ tC = ⟨C1, []⟩) (hC2 : σ tC2 = ⟨C2, []⟩) :
    Runs coefStep σ (· = Function.update (Function.update (Function.update σ
        tD ⟨rwd N w :: Dl, Dr⟩) tC ⟨rwd N (posPart N (descale N k w)) :: C1, []⟩)
        tC2 ⟨rwd N (negPart N (descale N k w)) :: C2, []⟩) (500 * N + 1200) := by
  unfold coefStep
  have s1 := runs_descaleOp hN hw σ hr hcT hD
  set σ₁ := Function.update (Function.update σ tD ⟨rwd N w :: Dl, Dr⟩) aO (reg (rwd N (descale N k w)))
  have hd := descale_lt N k w
  obtain ⟨diff, hdl, s2⟩ := runs_signTest hN hd σ₁ (by tsimp [σ₁]) (by tsimp [σ₁, hH]) (by tsimp [σ₁, hT])
  set σ₂ := Function.update σ₁ sT1 ⟨[diff], [[decide (2 * descale N k w < 2 ^ N + 1)]]⟩
  have hr₂ : AluReady N (Function.update σ₂ aO emp) := by
    obtain ⟨⟨hW, hF⟩, hcN, hc1, hX, hY, hAO, hS1, hS2, hS3, hbX, hbY⟩ := hr
    exact ⟨⟨by tsimp [σ₂, σ₁, hW], by tsimp [σ₂, σ₁, hF]⟩, by tsimp [σ₂, σ₁, hcN], by tsimp [σ₂, σ₁, hc1],
      by tsimp [σ₂, σ₁, hX], by tsimp [σ₂, σ₁, hY], by tsimp [σ₂, σ₁], by tsimp [σ₂, σ₁, hS1],
      by tsimp [σ₂, σ₁, hS2], by tsimp [σ₂, σ₁, hS3], by tsimp [σ₂, σ₁, hbX], by tsimp [σ₂, σ₁, hbY]⟩
  have s3 := runs_route hN hd σ₂ hr₂ (diff := diff) (C1 := C1) (C2 := C2) (by tsimp [σ₂]) (by tsimp [σ₂, σ₁])
    (by tsimp [σ₂, σ₁, hC]) (by tsimp [σ₂, σ₁, hC2])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (runs_clear sT1 _)))).mono (fun σ' h => ?_) ?_
  · rw [h]
    funext i; fin_cases i <;> tsimp [σ₂, σ₁, hT, hr.2.2.2.2.2.1, emp]
  · tsimp [σ₂, σ₁, WTape.words, clen, hdl]
    omega

/-- Every coefficient on `tD`. -/
noncomputable def coefLoop : Cmd 0 𝕋 := .loop tD coefStep

theorem runs_coefLoop {N k : ℕ} (hN : 0 < N) :
    ∀ (ws : List ℕ) (σ : Fin 𝕋 → WTape) (Dl C1 C2 : List (List Bool)),
      (∀ w ∈ ws, w < 2 ^ N + 1) → AluReady N σ → σ cT = reg (ones (N - k)) →
      σ cH1 = reg (hword N) → σ sT1 = emp →
      σ tD = ⟨Dl, rwds N ws⟩ → σ tC = ⟨C1, []⟩ → σ tC2 = ⟨C2, []⟩ →
      Runs coefLoop σ (· = Function.update (Function.update (Function.update σ
          tD ⟨(rwds N ws).reverse ++ Dl, []⟩)
          tC ⟨(rwds N ((ws.map (descale N k)).map (posPart N))).reverse ++ C1, []⟩)
          tC2 ⟨(rwds N ((ws.map (descale N k)).map (negPart N))).reverse ++ C2, []⟩)
        (ws.length * (500 * N + 1202))
  | [], σ, Dl, C1, C2, _, _, _, _, _, hD, hC, hC2 => by
    refine (Runs.loop_done (by simp [hD, rwds]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hD, hC, hC2, rwds]
  | w :: ws, σ, Dl, C1, C2, hws, hr, hcT, hH, hT, hD, hC, hC2 => by
    have hw := hws w (by simp)
    have s1 := runs_coefStep (k := k) hN hw σ hr hcT hH hT (Dr := rwds N ws) (C1 := C1) (C2 := C2)
      (by simpa [rwds] using hD) hC hC2
    set σ₁ := Function.update (Function.update (Function.update σ
        tD ⟨rwd N w :: Dl, rwds N ws⟩) tC ⟨rwd N (posPart N (descale N k w)) :: C1, []⟩)
        tC2 ⟨rwd N (negPart N (descale N k w)) :: C2, []⟩
    have hr₁ : AluReady N σ₁ :=
      ((hr.update tD _ (by decide)).update tC _ (by decide)).update tC2 _ (by decide)
    have ih := runs_coefLoop (k := k) hN ws σ₁ (rwd N w :: Dl) (rwd N (posPart N (descale N k w)) :: C1)
      (rwd N (negPart N (descale N k w)) :: C2) (fun x hx => hws x (by simp [hx])) hr₁
      (by tsimp [σ₁, hcT]) (by tsimp [σ₁, hH]) (by tsimp [σ₁, hT]) (by tsimp [σ₁]) (by tsimp [σ₁])
      (by tsimp [σ₁])
    refine (Runs.loop_step (by simp [hD, rwds]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      funext i; fin_cases i <;> tsimp [σ₁, rwds]
    · simp only [List.length_cons]; nlinarith

/-! ### Switching the unit's modulus -/

theorem bits_two_pow : ∀ n, bits (n + 1) (2 ^ n) = List.replicate n false ++ [true]
  | 0 => rfl
  | n + 1 => by
    have h1 : 2 ^ (n + 1) % 2 = 0 := by rw [pow_succ]; simp
    have h2 : 2 ^ (n + 1) / 2 = 2 ^ n := by rw [pow_succ]; simp
    rw [bits, h1, h2, bits_two_pow n]
    simp [List.replicate_succ]

theorem fword_eq {N : ℕ} (hN : 0 < N) : fword N = true :: (List.replicate (N - 1) false ++ [true]) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [fword, bits]
  have h1 : (2 ^ (n + 1) + 1) % 2 = 1 := by rw [pow_succ]; omega
  have h2 : (2 ^ (n + 1) + 1) / 2 = 2 ^ n := by rw [pow_succ]; omega
  rw [h1, h2, bits_two_pow]; simp

/-- The modulus words `cN = ones N` and `cW = ones (N + 1)` from `cU = ones N`. -/
noncomputable def aluSetA : Cmd 0 𝕋 :=
  .seq (clear cN) <| .seq (clear cW) <|
  .seq (op0 Rules.copy false cU cN (by decide)) <| .seq (rewind cU) <| .seq (rewind cN) <|
  .seq (op0 Rules.copy false cU cW (by decide)) <| .seq (rewind cU) <|
  .seq (op0 Rules.copy true c1 cW (by decide)) <| .seq (rewind c1) (rewind cW)

/-- The modulus word `cF = fword N` from `cU = ones N`. -/
noncomputable def aluSetB : Cmd 0 𝕋 :=
  .seq (clear cF) <| .seq (emit [[true]] cF) <|
  .seq (op1 Rules.drop false cU c1 sT1 (by decide) (by decide) (by decide)) <| .seq (rewind cU) <|
  .seq (rewind c1) <| .seq (rewind sT1) <|
  .seq (op0 (Rules.fill false) true sT1 cF (by decide)) <| .seq (clear sT1) <|
  .seq (op0 Rules.copy true c1 cF (by decide)) <| .seq (rewind c1) (rewind cF)

/-- Rebuild the unit's constants for the modulus `2^N + 1` from `cU = ones N`. -/
noncomputable def aluSet : Cmd 0 𝕋 := .seq aluSetA aluSetB

theorem runs_aluSet {N : ℕ} (hN : 0 < N) (σ : Fin 𝕋 → WTape) (hU : σ cU = reg (ones N))
    (h1 : σ c1 = reg [true]) (hT : σ sT1 = emp) :
    Runs aluSet σ (· = Function.update (Function.update (Function.update σ
        cN (reg (ones N))) cW (reg (ones (N + 1)))) cF (reg (fword N)))
      (2 * clen (σ cN).words + 2 * clen (σ cW).words + 2 * clen (σ cF).words + 20 * N + 150) := by
  have sA : Runs aluSetA σ (· = Function.update (Function.update σ cN (reg (ones N))) cW (reg (ones (N + 1))))
      (2 * clen (σ cN).words + 2 * clen (σ cW).words + 8 * N + 80) := by
    apply Runs.of_wp
    simp only [aluSetA, WP, wp_op0, wp_rewind, wp_clear]
    tsimp [hU, h1, emp, reg, Rules.output_copy]
    have t1 := time_le Rules.copy (ones N) (fun j => j.elim0) 0 (fun j => j.elim0)
    have t2 := time_le Rules.copy [true] (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [hU, h1, emp, reg, ones, List.replicate_succ']
    · generalize clen (σ cN).words = a
      generalize clen (σ cW).words = b
      simp at t1 t2 ⊢; omega
  set σ₁ := Function.update (Function.update σ cN (reg (ones N))) cW (reg (ones (N + 1)))
  have htl : (ones N).tail = ones (N - 1) := by simp [ones, List.tail_replicate]
  have sB : Runs aluSetB σ₁ (· = Function.update σ₁ cF (reg (fword N)))
      (2 * clen (σ cF).words + 10 * N + 50) := by
    apply Runs.of_wp
    simp only [aluSetB, WP, wp_op0, wp_op1, wp_rewind, wp_clear, wp_emit]
    tsimp [σ₁, hU, h1, hT, emp, reg, Rules.output_copy, Rules.output_drop, Rules.output_fill, htl]
    have t3 := time_le Rules.drop (ones N) (fun _ => [true]) 1 (fun _ => by simp)
    have t4 := time_le (Rules.fill false) (ones (N - 1)) (fun j => j.elim0) 0 (fun j => j.elim0)
    have t5 := time_le Rules.copy [true] (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [σ₁, hU, h1, hT, emp, reg, fword_eq hN]
    · generalize clen (σ cF).words = a
      simp [clen, WTape.words] at t3 t4 t5 ⊢; omega
  exact (Runs.then sA sB).mono (fun σ' h => h) (by omega)

end IntegerMultBounds.Schoenhage
