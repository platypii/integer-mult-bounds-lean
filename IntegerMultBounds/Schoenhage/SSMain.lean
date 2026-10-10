import IntegerMultBounds.Schoenhage.SSMath

/-! The whole Schönhage–Strassen multiplier on the 64-tape bank: from the two
operands modulo `2^N + 1` on `tIn` and `pN = ones N`, the product on `tIn`. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-- All tapes empty but the operands and the size. -/
def SSStart (N x y : ℕ) (σ : Fin 𝕋 → WTape) : Prop :=
  σ tIn = ⟨[], [rwd N x, rwd N y]⟩ ∧ σ pN = reg (ones N) ∧ ∀ i, i ≠ tIn → i ≠ pN → σ i = emp

/-- The constants, the unit for `2^N + 1`, the level test and `N` ticks of fuel. -/
noncomputable def ssInit : Cmd 0 𝕋 :=
  .seq (emit [[true]] c1) <| .seq (rewind c1) <| .seq (emit [ones 2047] c2047) <| .seq (rewind c2047) <|
  .seq loadN <| .seq aluSet <| .seq (clear cU) <| .seq testG <|
  .seq (op0 Rules.ticks false pN tG (by decide)) <| .seq (rewind pN) (rewind tG)

theorem runs_ssInit {N x y : ℕ} (hN : 0 < N) (σ : Fin 𝕋 → WTape) (hS : SSStart N x y σ) :
    ∃ σ', Runs ssInit σ (· = σ') (500 * N + 40000) ∧ Rest N [x, y] [] [] σ' ∧
      σ' tG = ⟨[], List.replicate N []⟩ := by
  obtain ⟨hIn, hp, he⟩ := hS
  have e : ∀ i, i ≠ tIn → i ≠ pN → σ i = emp := he
  have s1 := runs_emit (a := 0) [[true]] c1 σ (by rw [e c1 (by decide) (by decide)]; rfl)
  set σ₁ := Function.update σ c1 ⟨[[true]].reverse ++ (σ c1).left, []⟩
  have s2 := runs_rewind (a := 0) c1 σ₁
  set σ₂ := Function.update σ₁ c1 ⟨[], (σ₁ c1).left.reverse ++ (σ₁ c1).right⟩
  have s3 := runs_emit (a := 0) [ones 2047] c2047 σ₂ (by tsimp [σ₂, σ₁, e c2047 (by decide) (by decide), emp])
  set σ₃ := Function.update σ₂ c2047 ⟨[ones 2047].reverse ++ (σ₂ c2047).left, []⟩
  have s4 := runs_rewind (a := 0) c2047 σ₃
  set σ₄ := Function.update σ₃ c2047 ⟨[], (σ₃ c2047).left.reverse ++ (σ₃ c2047).right⟩
  have s5 := runs_loadN (N := N) σ₄ (by tsimp [σ₄, σ₃, σ₂, σ₁, hp]) (by tsimp [σ₄, σ₃, σ₂, σ₁, e cU (by decide) (by decide)])
  set σ₅ := Function.update σ₄ cU (reg (ones N))
  have s6 := runs_aluSet hN σ₅ (by tsimp [σ₅]) (by tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, e c1 (by decide) (by decide), emp, reg])
    (by tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, e sT1 (by decide) (by decide)])
  set σ₆ := Function.update (Function.update (Function.update σ₅
        cN (reg (ones N))) cW (reg (ones (N + 1)))) cF (reg (fword N))
  have s7 := runs_clear (a := 0) cU σ₆
  set σ₇ := Function.update σ₆ cU ⟨[], []⟩
  have eq : ∀ i, i ≠ tIn → i ≠ pN → i ≠ c1 → i ≠ c2047 → i ≠ cN → i ≠ cW → i ≠ cF → σ₇ i = emp := by
    intro i h1 h2 h3 h4 h5 h6 h7
    by_cases h8 : i = cU
    · subst h8; simp [σ₇, emp]
    · simp only [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, Function.update_of_ne h8, Function.update_of_ne h7,
        Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4, Function.update_of_ne h3]
      exact e i h1 h2
  have s8 := runs_testG (N := N) σ₇ (by tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hp])
    (by tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, e c1 (by decide) (by decide), emp, reg])
    (by tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, e c2047 (by decide) (by decide), emp, reg])
    (eq qR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (eq qT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (eq qB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (eq qS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (eq tJ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  set σ₈ := Function.update σ₇ fG (reg (ones (Nat.size N - 2047)))
  have s9 : Runs (a := 0) (.seq (op0 Rules.ticks false pN tG (by decide)) <| .seq (rewind pN) (rewind tG)) σ₈
      (· = Function.update σ₈ tG ⟨[], List.replicate N []⟩) (3 * N + 20) := by
    apply Runs.of_wp
    simp only [WP, wp_op0, wp_rewind]
    have hG : σ₈ tG = emp := by
      simp only [σ₈, Function.update_of_ne (show tG ≠ fG by decide)]
      exact eq tG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have eG := e tG (by decide) (by decide)
    tsimp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hp, eG, emp, reg, Rules.output_ticks]
    have t1 := time_le Rules.ticks (ones N) (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hp, eG, emp, reg]
    · simp [clen] at t1 ⊢; omega
  have eq8 : ∀ i, i ≠ tIn → i ≠ pN → i ≠ c1 → i ≠ c2047 → i ≠ cN → i ≠ cW → i ≠ cF → i ≠ fG → i ≠ tG →
      Function.update σ₈ tG ⟨[], List.replicate N []⟩ i = emp := by
    intro i h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp only [σ₈, Function.update_of_ne h9, Function.update_of_ne h8]
    exact eq i h1 h2 h3 h4 h5 h6 h7
  refine ⟨Function.update σ₈ tG ⟨[], List.replicate N []⟩, (Runs.then s1 (Runs.then s2 (Runs.then s3
    (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7 (Runs.then s8 s9)))))))).mono
    (fun σ' h => h) ?_, ⟨⟨⟨by tsimp [σ₈, σ₇, σ₆], by tsimp [σ₈, σ₇, σ₆]⟩, by tsimp [σ₈, σ₇, σ₆],
      by tsimp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, e c1 (by decide) (by decide), emp, reg], ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩, ?_, by tsimp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hp], by tsimp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hIn, rwds],
      ?_, ?_, by tsimp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, e c2047 (by decide) (by decide), emp, reg],
      by tsimp [σ₈]⟩, by tsimp⟩
  · tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, e cN (by decide) (by decide), e cW (by decide) (by decide),
      e cF (by decide) (by decide), e cU (by decide) (by decide), e fG (by decide) (by decide),
      e c1 (by decide) (by decide), e c2047 (by decide) (by decide), emp, reg, WTape.words, clen]
    omega
  all_goals first
    | exact eq8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    | (intro i hm; exact eq8 i (by revert hm; revert i; decide) (by revert hm; revert i; decide)
        (by revert hm; revert i; decide) (by revert hm; revert i; decide) (by revert hm; revert i; decide)
        (by revert hm; revert i; decide) (by revert hm; revert i; decide) (by revert hm; revert i; decide)
        (by revert hm; revert i; decide))

theorem traj_inv : ∀ (j N : ℕ) (L : List ℕ), 0 < N → 2 ^ kOf N ∣ N → Even L.length →
    (∀ x ∈ L, x < 2 ^ N + 1) →
    0 < (traj j N L).2.1 ∧ Even (traj j N L).2.2.length ∧ ∀ x ∈ (traj j N L).2.2, x < 2 ^ (traj j N L).2.1 + 1
  | 0, N, L, h0, _, he, hv => ⟨h0, he, hv⟩
  | j + 1, N, L, h0, hk, he, hv => by
    by_cases hN : N < N0
    · rw [traj_small hN]; exact ⟨h0, he, hv⟩
    · rw [not_lt] at hN
      have hl : ∀ x, (tpieces (nextN N) (kOf N) (pieceOf N) x).length = 2 ^ kOf N := fun x => by
        rw [tpieces, fwdIter_length _ _ _ _ _ rfl (by simp [length_pieces]), length_pieces]
      have hpos := (level_facts hN).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      simp only [traj, show ¬ N < N0 by omega, ↓reduceIte]
      exact traj_inv j _ _ hpos (dvd_chain hN).2.2 (nextBatch_even _ _ _ hl L) (nextBatch_lt hN hk L hv)

/-- The whole multiplier. -/
noncomputable def ssMain : Cmd 0 𝕋 :=
  .seq ssInit <| .seq downLoop <| .seq baseBatch <| .seq swapIO <| .seq (rewind tCnt) upLoop

/-- The multiplier's cost along the trajectory of a batch `L` at size `N`. -/
noncomputable def ssCost (N : ℕ) (L : List ℕ) : ℕ :=
  let t := traj N N L
  500 * N + 40000 + 1 + (trajCost N N L + 1 + (t.2.2.length * ((t.2.1 + 2) * (420 * t.2.1 + 1400)) + 1 +
    (2 * (t.2.2.length * (t.2.1 + 2)) + t.2.2.length * (5 * t.2.1 + 30) + 20 + 1 +
      (t.1.length + 2 + 1 + upFoldCost t.1.reverse))))

theorem runs_ssMain {N x y : ℕ} (hN : 0 < N) (hk : 2 ^ kOf N ∣ N) (hx : x < Fm N) (hy : y < Fm N)
    (σ : Fin 𝕋 → WTape) (hS : SSStart N x y σ) :
    Runs ssMain σ (fun σ' => (σ' tIn).right = [rwd N (x * y % Fm N)]) (ssCost N [x, y]) := by
  obtain ⟨σ1, s1, hR1, hG1⟩ := runs_ssInit hN σ hS
  have hv : ∀ z ∈ [x, y], z < 2 ^ N + 1 := by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
  have he : Even [x, y].length := by simp
  have s2 := runs_downLoop N N [x, y] [] [] σ1 [] hR1 hk he hv (by simpa using hG1)
  set t := traj N N [x, y] with ht
  have hinv := traj_inv N N [x, y] hN hk he hv
  have hsmall : t.2.1 < N0 := traj_lt N N [x, y] le_rfl
  have tail : ∀ σ', Rest t.2.1 t.2.2 ((t.1.map fun p => ones p.1).reverse ++ [])
      (List.replicate t.1.length [] ++ []) σ' →
      Runs (.seq baseBatch <| .seq swapIO <| .seq (rewind tCnt) upLoop) σ'
        (fun σ'' => (σ'' tIn).right = [rwd N (x * y % Fm N)])
        (t.2.2.length * ((t.2.1 + 2) * (420 * t.2.1 + 1400)) + 1 +
          (2 * (t.2.2.length * (t.2.1 + 2)) + t.2.2.length * (5 * t.2.1 + 30) + 20 + 1 +
            (t.1.length + 2 + 1 + upFoldCost t.1.reverse))) := by
    intro σ' hR
    obtain ⟨hr, hi, hp, hIn, hP, hC, hc, hf⟩ := hR
    have f : ∀ i ∈ idle, σ' i = emp := hi
    obtain ⟨h0, hev, hvals⟩ := hinv
    set NL := t.2.1
    set LL := t.2.2
    have b1 := runs_baseBatch h0 LL σ' [] [] hev hvals hr (f sX (by decide)) (f tY (by decide))
      (f sRA (by decide)) (f cT (by decide)) (f tS (by decide)) (f sT1 (by decide)) (f sT2 (by decide))
      (f tJ (by decide)) hIn (by rw [f tOut (by decide)]; rfl)
    set Qb := (pairsOf LL).map fun p => p.1 * p.2 % (2 ^ NL + 1)
    set τ1 := Function.update (Function.update σ' tIn ⟨(rwds NL LL).reverse ++ [], []⟩)
      tOut ⟨(rwds NL Qb).reverse ++ [], []⟩
    have b2 := runs_swapIO (N := NL) τ1 Qb (Il := (rwds NL LL).reverse ++ []) (by tsimp [τ1]) (by tsimp [τ1])
    set τ2 := Function.update (Function.update τ1 tIn ⟨[], rwds NL Qb⟩) tOut emp
    have b3 := runs_rewind (a := 0) tCnt τ2
    set τ3 := Function.update τ2 tCnt ⟨[], (τ2 tCnt).left.reverse ++ (τ2 tCnt).right⟩
    have hQb : Qb = (pairsOf LL).map fun p => ssMul NL p.1 p.2 := by
      simp only [Qb]; congr 1; funext p; rw [ssMul_eq]; simp [hsmall, Fm]
    have hok := UpOK_traj N N [x, y] hk he
    have hRU : RestU NL NL Qb ((t.1.reverse.map fun p => ones p.1) ++ []) [] τ3 := by
      refine ⟨?_, ?_, by tsimp [τ3, τ2, τ1, hp], by tsimp [τ3, τ2, τ1], by tsimp [τ3, τ2, τ1, hP, List.map_reverse]⟩
      · obtain ⟨⟨hW, hF⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hr
        exact ⟨⟨by tsimp [τ3, τ2, τ1, hW], by tsimp [τ3, τ2, τ1, hF]⟩, by tsimp [τ3, τ2, τ1, h2],
          by tsimp [τ3, τ2, τ1, h3], by tsimp [τ3, τ2, τ1, h4], by tsimp [τ3, τ2, τ1, h5], by tsimp [τ3, τ2, τ1, h6],
          by tsimp [τ3, τ2, τ1, h7], by tsimp [τ3, τ2, τ1, h8], by tsimp [τ3, τ2, τ1, h9], by tsimp [τ3, τ2, τ1, h10],
          by tsimp [τ3, τ2, τ1, h11]⟩
      · intro i hm
        by_cases e2 : i = tOut
        · subst e2; tsimp [τ3, τ2]
        · have hne : i ≠ tIn ∧ i ≠ tCnt := by revert hm; revert i; decide
          simp only [τ3, τ2, τ1, Function.update_of_ne hne.2, Function.update_of_ne e2, Function.update_of_ne hne.1]
          exact f i hm
    have b4 := runs_upLoop t.1.reverse NL NL Qb τ3 [] [] [] (by rw [hQb, List.length_map, length_pairsOf]; exact hok)
      (by intro q hq; simp only [Qb, List.mem_map] at hq; obtain ⟨p, -, rfl⟩ := hq; exact Nat.mod_lt _ (by positivity))
      le_rfl hRU (by tsimp [τ3, τ2, τ1, hC, List.length_reverse])
    refine (Runs.then b1 (Runs.then b2 (Runs.then b3 b4))).mono (fun σ'' h => ?_) ?_
    · obtain ⟨Na', h1, -, -, h4, -⟩ := h
      rw [h4, hQb, upFold_traj N N [x, y] hk he hv, (lastN_traj N N [x, y]).1]
      simp [pairsOf, rwds, ssMul_correct N x y hk hx hy]
    · have c1 : clen (rwds NL LL) = LL.length * (NL + 2) := clen_rwds _ _
      have c2 : Qb.length ≤ LL.length := by simp [Qb, length_pairsOf]; omega
      have c3 := Nat.mul_le_mul_right (5 * NL + 30) c2
      tsimp [τ2, τ1, hC, List.length_reverse, WTape.words, clen_reverse, clen_append, c1]
      simp [clen]
      omega
  exact Runs.then s1 (Runs.seq (s2.mono (fun σ' h => tail σ' h.1) le_rfl))

end IntegerMultBounds.Schoenhage
