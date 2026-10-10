import IntegerMultBounds.Schoenhage.LevelUp

/-! The down-sweep of one pair on word tapes: each operand is cut into its
padded pieces and transformed; the two transformed lists are interleaved
into the next level's batch of pairs. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

namespace Tp
abbrev pKh : Fin 𝕋 := 53
end Tp

/-! ### Transform registers -/

/-- The root shift on `tE`, `cH = ones (K/2)`, `K/2` ticks on `tH`, `k` ticks on `tL`. -/
noncomputable def fwdSetup : Cmd 0 𝕋 :=
  .seq (op0 Rules.copy false cHN tE (by decide)) <| .seq (rewind cHN) <| .seq (rewind tE) <|
  .seq (op0 Rules.copy false pKh cH (by decide)) <| .seq (rewind pKh) <| .seq (rewind cH) <|
  .seq (op0 Rules.ticks false pKh tH (by decide)) <| .seq (rewind pKh) <| .seq (rewind tH) <|
  .seq (op0 Rules.ticks false pK tL (by decide)) <| .seq (rewind pK) (rewind tL)

theorem runs_fwdSetup {Np k Kh : ℕ} (σ : Fin 𝕋 → WTape) (hHN : σ cHN = reg (ones (Np / 2)))
    (hKh : σ pKh = reg (ones Kh)) (hK : σ pK = reg (ones k))
    (hE : σ tE = emp) (hH : σ cH = emp) (htH : σ tH = emp) (hL : σ tL = emp) :
    Runs fwdSetup σ (· = Function.update (Function.update (Function.update (Function.update σ
        tE ⟨[], [ones (Np / 2)]⟩) cH (reg (ones Kh))) tH ⟨[], List.replicate Kh []⟩)
        tL ⟨[], List.replicate k []⟩) (4 * Np + 10 * Kh + 6 * k + 100) := by
  apply Runs.of_wp
  simp only [fwdSetup, WP, wp_op0, wp_rewind]
  tsimp [hHN, hKh, hK, hE, hH, htH, hL, emp, reg, Rules.output_copy, Rules.output_ticks]
  have t1 := time_le Rules.copy (ones (Np / 2)) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.copy (ones Kh) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t3 := time_le Rules.ticks (ones Kh) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t4 := time_le Rules.ticks (ones k) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hHN, hKh, hK, hE, hH, htH, hL, emp, reg]
  · simp [clen] at t1 t2 t3 t4 ⊢; omega

theorem length_rulerActs {M W : ℕ} (hMW : M + 1 ≤ W) : ∀ K, (Rules.rulerActs M W K).length ≤ K * (W + 1)
  | 0 => by simp [Rules.rulerActs]
  | 1 => by simp [Rules.rulerActs]; omega
  | K + 2 => by
    have := length_rulerActs hMW (K + 1)
    simp only [Rules.rulerActs, List.length_append, List.length_replicate, List.length_singleton]
    have : M + (W - M) = W := by omega
    nlinarith

theorem length_ruler {M W : ℕ} (hMW : M + 1 ≤ W) (K : ℕ) : (Rules.ruler M W K).length ≤ 2 * K * (W + 1) := by
  have h : ∀ as : List Rules.Act, (as.flatMap Rules.Act.enc).length = 2 * as.length := by
    intro as; induction as with
    | nil => simp
    | cons a as ih => cases a <;> simp [Rules.Act.enc, ih] <;> ring
  rw [Rules.ruler, h]
  have := length_rulerActs hMW K
  nlinarith

theorem length_kidsIter (N : ℕ) : ∀ (n : ℕ) (E : List ℕ), ((kids N)^[n] E).length = 2 ^ n * E.length
  | 0, E => by simp
  | n + 1, E => by
    rw [Function.iterate_succ_apply, length_kidsIter N n, length_kids, pow_succ]; ring

/-- Drop the transform registers. -/
noncomputable def fwdClean : Cmd 0 𝕋 := .seq (clear tE) <| .seq (clear cH) <| .seq (clear tH) (clear tL)

/-- Cut the next operand of `tIn` into pieces and transform them; the result on `tD`. -/
noncomputable def downCore : Cmd 0 𝕋 :=
  .seq (regIn tIn sX (by decide)) <| .seq splitOp <| .seq (rewind tD) <| .seq fwdSetup <|
  .seq fwdLoop fwdClean

/-- The transformed pieces of an operand, as the tapes compute them. -/
def tpieces (Np k M x : ℕ) : List ℕ := fwdIter Np k (2 ^ k / 2) [Np / 2] (pieces M (2 ^ k) x)

set_option maxHeartbeats 1000000 in
theorem runs_downCore {N Np k M x : ℕ} (hNp : 0 < Np) (hs : N = M * 2 ^ k) (hMN : M ≤ Np)
    (hx : x < 2 ^ N + 1) (σ : Fin 𝕋 → WTape) (hL : LevelRegs N Np k M σ)
    (hR : σ cR = reg (Rules.ruler M (Np + 1) (2 ^ k))) (hKh : σ pKh = reg (ones (2 ^ k / 2)))
    (hD0 : σ tD = emp) {Il Ir : List (List Bool)} (hIn : σ tIn = ⟨Il, rwd N x :: Ir⟩) :
    Runs downCore σ (· = Function.update (Function.update σ tIn ⟨rwd N x :: Il, Ir⟩)
        tD ⟨[], rwds Np (tpieces Np k M x)⟩)
      ((k + 2) * (5000 * (2 ^ k + 1) * (Np + 2)) + 10 * N + 100) := by
  obtain ⟨hr, hq, hHN, hK, hNK, hH1, hMr, hW, hpN, hpNp⟩ := hL
  have q : ∀ i ∈ quiet, σ i = emp := hq
  have qcT := q cT (by decide); have qtU := q tU (by decide); have qtV := q tV (by decide)
  have qO1 := q tO1 (by decide); have qO2 := q tO2 (by decide); have qtJ := q tJ (by decide)
  have qD2 := q tD2 (by decide); have qtE := q tE (by decide); have qE2 := q tE2 (by decide)
  have qtH := q tH (by decide); have qcH := q cH (by decide); have qH2 := q cH2 (by decide)
  have qtL := q tL (by decide); have qsX := q sX (by decide); have qtD := hD0
  unfold downCore
  have s1 := runs_regIn (a := 0) (s := tIn) (r := sX) (by decide) σ hIn qsX
  set σ₁ := Function.update (Function.update σ tIn ⟨rwd N x :: Il, Ir⟩) sX (reg (rwd N x))
  have hxv : bval (rwd N x) < 2 ^ (M * 2 ^ k + 1) := by
    have e : 2 ^ (M * 2 ^ k + 1) = 2 * 2 ^ N := by rw [hs, pow_succ]; ring
    rw [bval_rwd hx, e]; have := Nat.one_le_two_pow (n := N); omega
  have s2 := runs_splitOp (M := M) (W := Np + 1) (K := 2 ^ k) (by omega) (Nat.two_pow_pos k) σ₁ hxv
    (Dl := []) (by tsimp [σ₁, hR]) (by tsimp [σ₁]) (by tsimp [σ₁, qtD, emp])
  rw [bval_rwd hx] at s2
  set D := pieces M (2 ^ k) x
  set σ₂ := Function.update (Function.update σ₁ sX emp) tD ⟨(D.map (bits (Np + 1))).reverse ++ [], []⟩
  have s3 := runs_rewind (a := 0) tD σ₂
  set σ₃ := Function.update σ₂ tD ⟨[], (σ₂ tD).left.reverse ++ (σ₂ tD).right⟩
  have s4 := runs_fwdSetup (Np := Np) (k := k) (Kh := 2 ^ k / 2) σ₃ (by tsimp [σ₃, σ₂, σ₁, hHN])
    (by tsimp [σ₃, σ₂, σ₁, hKh]) (by tsimp [σ₃, σ₂, σ₁, hK]) (by tsimp [σ₃, σ₂, σ₁, qtE])
    (by tsimp [σ₃, σ₂, σ₁, qcH]) (by tsimp [σ₃, σ₂, σ₁, qtH]) (by tsimp [σ₃, σ₂, σ₁, qtL])
  set σ₄ := Function.update (Function.update (Function.update (Function.update σ₃
        tE ⟨[], [ones (Np / 2)]⟩) cH (reg (ones (2 ^ k / 2)))) tH ⟨[], List.replicate (2 ^ k / 2) []⟩)
        tL ⟨[], List.replicate k []⟩
  have hDl : D.length = 2 ^ k := length_pieces _ _ _
  have hDv : ∀ d ∈ D, d < 2 ^ Np + 1 := by
    intro d hd
    have h1 := pieces_le M (2 ^ k) x (by rw [← hs]; omega) d hd
    have h2 : 2 ^ M ≤ 2 ^ Np := Nat.pow_le_pow_right (by norm_num) hMN
    omega
  have hr₄ : AluReady Np σ₄ := by
    refine (((((((hr.update tIn _ (by decide)).update sX _ (by decide)).update sX _ (by decide)).update
      tD _ (by decide)).update tD _ (by decide)).update tE _ (by decide)).update cH _ (by decide)).update tH _
      (by decide) |>.update tL _ (by decide)
  have s5 := runs_fwdLoop (N := Np) hNp k (2 ^ k / 2) [Np / 2] D σ₄ [] rfl (by simp [hDl]) (by simp)
    (by intro t ht; simp at ht; omega) hDv hr₄ (by tsimp [σ₄, σ₃, σ₂, σ₁, qcT]) (by tsimp [σ₄]) (by tsimp [σ₄, σ₃, σ₂]; rfl)
    (by tsimp [σ₄]) (by tsimp [σ₄, σ₃, σ₂, σ₁, qD2]) (by tsimp [σ₄, σ₃, σ₂, σ₁, qE2])
    (by tsimp [σ₄, σ₃, σ₂, σ₁, hHN]) (by tsimp [σ₄, σ₃, σ₂, σ₁, qtU]) (by tsimp [σ₄, σ₃, σ₂, σ₁, qtV])
    (by tsimp [σ₄, σ₃, σ₂, σ₁, qO1]) (by tsimp [σ₄, σ₃, σ₂, σ₁, qO2]) (by tsimp [σ₄, σ₃, σ₂, σ₁, qtJ])
    (by tsimp [σ₄]) (by tsimp [σ₄, σ₃, σ₂, σ₁, qH2]) (by tsimp [σ₄])
  set F := fwdIter Np k (2 ^ k / 2) [Np / 2] D
  set Ek := ((kids Np)^[k] [Np / 2]).map ones
  set σ₅ := Function.update (Function.update (Function.update (Function.update
          (Function.update σ₄ tD ⟨[], rwds Np F⟩) tE ⟨[], Ek⟩)
          cH (reg (ones (2 ^ k / 2 / 2 ^ k)))) tH ⟨[], List.replicate (2 ^ k / 2 / 2 ^ k) []⟩)
          tL ⟨List.replicate k [] ++ [], []⟩
  have cE : clen Ek ≤ 2 ^ k * (Np + 1) := by
    have := clen_map_ones_le Np ((kids Np)^[k] [Np / 2]) (kidsIter_le Np k _ (by intro t ht; simp at ht; omega))
    rwa [length_kidsIter, List.length_singleton, mul_one] at this
  have hz : 2 ^ k / 2 / 2 ^ k = 0 := by
    rw [Nat.div_div_eq_div_mul]; exact Nat.div_eq_of_lt (by have := Nat.two_pow_pos k; omega)
  have s6 : Runs fwdClean σ₅ (· = Function.update (Function.update σ tIn ⟨rwd N x :: Il, Ir⟩)
        tD ⟨[], rwds Np (tpieces Np k M x)⟩) (2 * (2 ^ k * (Np + 1)) + 2 * k + 20) := by
    apply Runs.of_wp
    simp only [fwdClean, WP, wp_clear]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, qtE, qcH, qtH, qtL, qsX, emp, tpieces, F, D]
    · tsimp [σ₅, WTape.words, hz]
      simp only [clen, List.map_replicate, List.sum_replicate] at cE ⊢
      simp at cE ⊢
      omega
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono
    (fun σ' h => h) ?_
  have hrl := length_ruler (M := M) (W := Np + 1) (by omega) (2 ^ k)
  have hcl : clen (σ₂ tD).left = 2 ^ k * (Np + 2) := by
    tsimp [σ₂, clen_reverse]
    have := clen_rwds Np D; rw [hDl] at this; exact this
  rw [hcl, hDl, rwd_length]
  have hKh : 2 ^ k / 2 ≤ 2 ^ k := Nat.div_le_self _ _
  have hkK : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  have e : (k + 2) * (5000 * (2 ^ k + 1) * (Np + 2)) =
      k * (5000 * (2 ^ k + 1) * (Np + 2)) + 10000 * (2 ^ k * (Np + 2)) + 10000 * (Np + 2) := by ring
  have e2 : k * (4000 * (2 ^ k + 1) * (Np + 2)) ≤ k * (5000 * (2 ^ k + 1) * (Np + 2)) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have e3 : 2 * 2 ^ k * (Np + 1 + 1) = 2 * (2 ^ k * (Np + 2)) := by ring
  rw [e3] at hrl
  rw [e]
  have e4 : 2 ^ k * (Np + 1) ≤ 2 ^ k * (Np + 2) := Nat.mul_le_mul_left _ (by omega)
  have e5 : 2 ^ k ≤ 2 ^ k * (Np + 2) := Nat.le_mul_of_pos_right _ (by omega)
  clear_value σ₁ σ₂ σ₃ σ₄ σ₅ F Ek D
  generalize k * (4000 * (2 ^ k + 1) * (Np + 2)) = A at e2 ⊢
  generalize k * (5000 * (2 ^ k + 1) * (Np + 2)) = B at e2 ⊢
  generalize 2 ^ k * (Np + 2) = X at hrl e4 e5 ⊢
  generalize 2 ^ k * (Np + 1) = Y at e4 ⊢
  omega

/-! ### Interleaving -/

/-- Alternate the elements of two lists. -/
def zipFlat : List ℕ → List ℕ → List ℕ
  | x :: X, y :: Y => x :: y :: zipFlat X Y
  | _, _ => []

/-- Interleave `tX` and `tY` onto `tOut`. -/
noncomputable def ileave : Cmd 0 𝕋 := .loop tX (.seq (cpy tX tOut (by decide)) (cpy tY tOut (by decide)))

theorem runs_ileave {Np : ℕ} :
    ∀ (X Y : List ℕ) (σ : Fin 𝕋 → WTape) (Xl Yl O : List (List Bool)), X.length = Y.length →
      σ tX = ⟨Xl, rwds Np X⟩ → σ tY = ⟨Yl, rwds Np Y⟩ → σ tOut = ⟨O, []⟩ →
      Runs ileave σ (· = Function.update (Function.update (Function.update σ
          tX ⟨(rwds Np X).reverse ++ Xl, []⟩) tY ⟨(rwds Np Y).reverse ++ Yl, []⟩)
          tOut ⟨(rwds Np (zipFlat X Y)).reverse ++ O, []⟩) (X.length * (2 * Np + 20))
  | [], Y, σ, Xl, Yl, O, hl, hX, hY, hO => by
    have : Y = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    subst this
    refine (Runs.loop_done (by simp [hX, rwds]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hX, hY, hO, rwds, zipFlat]
  | x :: X, [], _, _, _, _, hl, _, _, _ => by simp at hl
  | x :: X, y :: Y, σ, Xl, Yl, O, hl, hX, hY, hO => by
    have s1 : Runs (a := 0) (.seq (cpy tX tOut (by decide)) (cpy tY tOut (by decide))) σ
        (· = Function.update (Function.update (Function.update σ
          tX ⟨rwd Np x :: Xl, rwds Np X⟩) tY ⟨rwd Np y :: Yl, rwds Np Y⟩)
          tOut ⟨rwd Np y :: rwd Np x :: O, []⟩) (2 * Np + 18) := by
      apply Runs.of_wp
      simp only [cpy, WP, wp_op0]
      tsimp [hX, hY, hO, rwds, Rules.output_copy]
      refine ⟨?_, ?_⟩
      · funext i; fin_cases i <;> tsimp [hX, hY, hO, rwds]
      · simp [time_copy, rwd_length]; omega
    set σ₁ := Function.update (Function.update (Function.update σ
          tX ⟨rwd Np x :: Xl, rwds Np X⟩) tY ⟨rwd Np y :: Yl, rwds Np Y⟩)
          tOut ⟨rwd Np y :: rwd Np x :: O, []⟩
    have ih := runs_ileave (Np := Np) X Y σ₁ (rwd Np x :: Xl) (rwd Np y :: Yl) (rwd Np y :: rwd Np x :: O)
      (by simpa using hl) (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁])
    refine (Runs.loop_step (by simp [hX, rwds]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      funext i; fin_cases i <;> tsimp [σ₁, rwds, zipFlat]
    · simp only [List.length_cons]; nlinarith

/-! ### One pair -/

/-- Move the transformed pieces from `tD` to `tX`. -/
noncomputable def moveX : Cmd 0 𝕋 := .seq (appendAll tD tX (by decide)) <| .seq (rewind tX) (clear tD)

/-- Move the transformed pieces from `tD` to `tY`. -/
noncomputable def moveY : Cmd 0 𝕋 := .seq (appendAll tD tY (by decide)) <| .seq (rewind tY) (clear tD)

theorem runs_moveX {Np : ℕ} (σ : Fin 𝕋 → WTape) (L : List ℕ) (hD : σ tD = ⟨[], rwds Np L⟩)
    (hX : σ tX = emp) :
    Runs moveX σ (· = Function.update (Function.update σ tD emp) tX ⟨[], rwds Np L⟩)
      (L.length * (4 * Np + 20) + 10) := by
  unfold moveX
  refine (Runs.then (runs_appendAll (a := 0) (s := tD) (d := tX) (by decide) (Np + 1) (rwds Np L) σ [] []
      hD (by simpa [emp] using hX) (rwds_length_le Np L)) <|
    Runs.then (runs_rewind tX _) (runs_clear tD _)).mono (fun σ' h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> tsimp [emp]
  · tsimp [WTape.words, clen_reverse, clen_rwds, length_rwds]; nlinarith

theorem runs_moveY {Np : ℕ} (σ : Fin 𝕋 → WTape) (L : List ℕ) (hD : σ tD = ⟨[], rwds Np L⟩)
    (hY : σ tY = emp) :
    Runs moveY σ (· = Function.update (Function.update σ tD emp) tY ⟨[], rwds Np L⟩)
      (L.length * (4 * Np + 20) + 10) := by
  unfold moveY
  refine (Runs.then (runs_appendAll (a := 0) (s := tD) (d := tY) (by decide) (Np + 1) (rwds Np L) σ [] []
      hD (by simpa [emp] using hY) (rwds_length_le Np L)) <|
    Runs.then (runs_rewind tY _) (runs_clear tD _)).mono (fun σ' h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> tsimp [emp]
  · tsimp [WTape.words, clen_reverse, clen_rwds, length_rwds]; nlinarith

theorem LevelRegs.update {N Np k M : ℕ} {σ : Fin 𝕋 → WTape} (h : LevelRegs N Np k M σ) (j : Fin 𝕋)
    (T : WTape) (hj : j ∉ [cW, cF, cN, c1, aX, aY, aO, aS1, aS2, aS3, bX, bY, cHN, pK, pNK, cH1, cM, cWA, pN,
      pNp] ++ quiet) :
    LevelRegs N Np k M (Function.update σ j T) := by
  obtain ⟨hr, hq, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only [List.mem_append, not_or] at hj
  obtain ⟨hj1, hj2⟩ := hj
  have hr' := hr.update j T (by intro hm; exact hj1 (by simp at hm ⊢; tauto))
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj1
  refine ⟨hr', hq.update j T hj2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Function.update_apply, *] <;> tauto

theorem LevelRegs.update_emp {N Np k M : ℕ} {σ : Fin 𝕋 → WTape} (h : LevelRegs N Np k M σ) (j : Fin 𝕋)
    (hj : j ∈ quiet) : LevelRegs N Np k M (Function.update σ j emp) := by
  obtain ⟨hr, hq, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hne : ∀ i ∈ [cW, cF, cN, c1, aX, aY, aO, aS1, aS2, aS3, bX, bY, cHN, pK, pNK, cH1, cM, cWA, pN, pNp],
      i ≠ j := by
    intro i hi e; subst e; revert hi hj; generalize i = i'; revert i'; decide
  have hr' := hr.update j emp (by intro hm; exact hne j (by simp at hm ⊢; tauto) rfl)
  refine ⟨hr', hq.update_emp j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [Function.update_of_ne (hne _ (by simp))] <;> assumption

theorem pair_arith (A N Np K : ℕ) :
    A + 10 * N + 100 + 1 + (K * (4 * Np + 20) + 10 + 1 + (A + 10 * N + 100 + 1 + (K * (4 * Np + 20) + 10 + 1 +
      (K * (2 * Np + 20) + 1 + (2 * (K * (Np + 2)) + 2 + 1 + (2 * (K * (Np + 2)) + 2)))))) ≤
    2 * (A + 10 * N + 100) + K * (20 * Np + 100) + 100 := by
  nlinarith [Nat.zero_le (K * Np)]

/-- The down-sweep of one pair: both operands transformed and interleaved onto `tOut`. -/
noncomputable def downPair : Cmd 0 𝕋 :=
  .seq downCore <| .seq moveX <| .seq downCore <| .seq moveY <| .seq ileave <| .seq (clear tX) (clear tY)

set_option maxHeartbeats 1000000 in
theorem runs_downPair {N Np k M x y : ℕ} (hNp : 0 < Np) (hs : N = M * 2 ^ k) (hMN : M ≤ Np)
    (hx : x < 2 ^ N + 1) (hy : y < 2 ^ N + 1) (σ : Fin 𝕋 → WTape) (hL : LevelRegs N Np k M σ)
    (hR : σ cR = reg (Rules.ruler M (Np + 1) (2 ^ k))) (hKh : σ pKh = reg (ones (2 ^ k / 2)))
    (hX : σ tX = emp) (hY : σ tY = emp) (hD0 : σ tD = emp)
    {Il Ir O : List (List Bool)} (hIn : σ tIn = ⟨Il, rwd N x :: rwd N y :: Ir⟩) (hO : σ tOut = ⟨O, []⟩) :
    Runs downPair σ (· = Function.update (Function.update σ tIn ⟨rwd N y :: rwd N x :: Il, Ir⟩)
        tOut ⟨(rwds Np (zipFlat (tpieces Np k M x) (tpieces Np k M y))).reverse ++ O, []⟩)
      (2 * ((k + 2) * (5000 * (2 ^ k + 1) * (Np + 2)) + 10 * N + 100) + 2 ^ k * (20 * Np + 100) + 100) := by
  unfold downPair
  have hlen : ∀ z, (tpieces Np k M z).length = 2 ^ k := fun z => by
    rw [tpieces, fwdIter_length _ _ _ _ _ rfl (by simp [length_pieces]), length_pieces]
  have s1 := runs_downCore hNp hs hMN hx σ hL hR hKh hD0 hIn
  set σ₁ := Function.update (Function.update σ tIn ⟨rwd N x :: Il, rwd N y :: Ir⟩)
    tD ⟨[], rwds Np (tpieces Np k M x)⟩
  have s2 := runs_moveX (Np := Np) σ₁ (tpieces Np k M x) (by tsimp [σ₁]) (by tsimp [σ₁, hX])
  set σ₂ := Function.update (Function.update σ₁ tD emp) tX ⟨[], rwds Np (tpieces Np k M x)⟩
  have hL₂ : LevelRegs N Np k M σ₂ := by
    have e : σ₂ = Function.update (Function.update (Function.update σ tIn ⟨rwd N x :: Il, rwd N y :: Ir⟩)
        tD emp) tX ⟨[], rwds Np (tpieces Np k M x)⟩ := by simp [σ₂, σ₁, Function.update_idem]
    rw [e]
    exact ((hL.update tIn _ (by decide)).update tD emp (by decide)).update tX _ (by decide)
  have s3 := runs_downCore hNp hs hMN hy σ₂ hL₂ (by tsimp [σ₂, σ₁, hR]) (by tsimp [σ₂, σ₁, hKh])
    (by tsimp [σ₂, σ₁])
    (Il := rwd N x :: Il) (Ir := Ir) (by tsimp [σ₂, σ₁])
  set σ₃ := Function.update (Function.update σ₂ tIn ⟨rwd N y :: rwd N x :: Il, Ir⟩)
    tD ⟨[], rwds Np (tpieces Np k M y)⟩
  have s4 := runs_moveY (Np := Np) σ₃ (tpieces Np k M y) (by tsimp [σ₃]) (by tsimp [σ₃, σ₂, σ₁, hY])
  set σ₄ := Function.update (Function.update σ₃ tD emp) tY ⟨[], rwds Np (tpieces Np k M y)⟩
  have s5 := runs_ileave (Np := Np) (tpieces Np k M x) (tpieces Np k M y) σ₄ [] [] O (by rw [hlen, hlen])
    (by tsimp [σ₄, σ₃, σ₂]) (by tsimp [σ₄]) (by tsimp [σ₄, σ₃, σ₂, σ₁, hO])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5
    (Runs.then (runs_clear tX _) (runs_clear tY _))))))).mono (fun σ' h => ?_) ?_
  · rw [h]
    funext i; fin_cases i <;> tsimp [σ₄, σ₃, σ₂, σ₁, hX, hY, hD0, emp]
  · tsimp [WTape.words, clen_reverse, clen_rwds, length_rwds, hlen]
    exact pair_arith _ _ _ _

end IntegerMultBounds.Schoenhage
