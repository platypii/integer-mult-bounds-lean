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

end IntegerMultBounds.Schoenhage
