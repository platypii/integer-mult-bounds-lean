import IntegerMultBounds.Schoenhage.SSProgram

/-! The multiplier returned to a clean bank, so that it can be called again:
after `ssMain`, every tape but the product is cleared. The final state of
`ssMain` is described tape by tape: the up-sweep's rest state, the counters,
and the tapes it never names, which a decidable syntactic check
(`Cmd.touches`) shows unchanged. `runs_ssClean`: from the start state, the
product modulo `2^N + 1` alone on `tIn`, every other tape empty. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

variable {a t : ℕ}

/-! ### Tapes a program never names -/

/-- Whether a program names tape `x`. -/
def Cmd.touches (x : Fin t) : Cmd a t → Bool
  | .prim P slot _ => (List.finRange P.s).any fun i => slot i == x
  | .seq c d => c.touches x || d.touches x
  | .loop _ b => b.touches x
  | .cond _ c d => c.touches x || d.touches x

theorem Exec.frame {c : Cmd a t} {σ σ' : Fin t → WTape} {k : ℕ} (h : Exec c σ σ' k) (x : Fin t)
    (hx : c.touches x = false) : σ' x = σ x := by
  induction h with
  | @prim P slot hinj σ hpre =>
    refine upd_other _ _ _ _ (fun i hi => ?_)
    simp only [Cmd.touches, List.any_eq_false, List.mem_finRange, beq_iff_eq, true_implies] at hx
    exact hx i hi
  | seq h₁ h₂ ih₁ ih₂ =>
    simp only [Cmd.touches, Bool.or_eq_false_iff] at hx
    rw [ih₂ hx.2, ih₁ hx.1]
  | loop_done => rfl
  | loop_step _ h₁ h₂ ih₁ ih₂ =>
    rw [ih₂ hx, ih₁ (by simpa [Cmd.touches] using hx)]
  | cond_true _ h₁ ih =>
    simp only [Cmd.touches, Bool.or_eq_false_iff] at hx
    exact ih hx.1
  | cond_false _ h₁ ih =>
    simp only [Cmd.touches, Bool.or_eq_false_iff] at hx
    exact ih hx.2

theorem Runs.frame {c : Cmd a t} {σ : Fin t → WTape} {Q : (Fin t → WTape) → Prop} {B : ℕ}
    (h : Runs c σ Q B) (xs : List (Fin t)) (hx : ∀ x ∈ xs, c.touches x = false) :
    Runs c σ (fun σ' => Q σ' ∧ ∀ x ∈ xs, σ' x = σ x) B := by
  obtain ⟨σ', k, he, hq, hk⟩ := h
  exact ⟨σ', k, he, ⟨hq, fun x hm => he.frame x (hx x hm)⟩, hk⟩

theorem upLoop_touches : ∀ x ∈ [c2047, fG, tG], (upLoop.touches x : Bool) = false := by decide

theorem ssMain_touches : ∀ x ∈ [(7 : Fin 𝕋), 49], (ssMain.touches x : Bool) = false := by decide

/-! ### The up-sweep with its counter -/

theorem runs_upLoop' :
    ∀ (rs : List (ℕ × List ℕ)) (Na Nc : ℕ) (Q : List ℕ) (σ : Fin 𝕋 → WTape) (Pl R Cl : List (List Bool)),
      UpOK rs Nc Q.length → (∀ q ∈ Q, q < Fm Nc) → Na ≤ Nc →
      RestU Na Nc Q ((rs.map fun p => ones p.1) ++ Pl) R σ → σ tCnt = ⟨Cl, List.replicate rs.length []⟩ →
      Runs upLoop σ (fun σ' => ∃ Na', Na' ≤ lastN rs Nc ∧ RestU Na' (lastN rs Nc) (upFold rs Q) Pl
          ((rs.map fun p => ones p.1).reverse ++ R) σ' ∧
          σ' tCnt = ⟨List.replicate rs.length [] ++ Cl, []⟩) (upFoldCost rs)
  | [], Na, Nc, Q, σ, Pl, R, Cl, _, _, hNa, hR, hC => by
    refine (Runs.loop_done (by simp [hC]) ⟨Na, by simpa [lastN] using hNa,
      by simpa [lastN, upFold] using hR, by simpa using hC⟩).mono (fun σ' h => h)
      (by simp [upFoldCost])
  | (N, L) :: rs, Na, Nc, Q, σ, Pl, R, Cl, hok, hQv, hNa, hR, hC => by
    obtain ⟨hN, hk, hNc, hql, hok'⟩ := hok
    subst hNc
    have hJ : σ tJ = emp := hR.2.1 tJ (by decide)
    have s1 := runs_upLevel hN hk hNa hql hQv σ (by simpa using hR)
    set U := upList N (2 ^ kOf N) (L.length / 2) Q
    set σ₁ := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update σ
        cN (reg (ones (nextN N)))) cW (reg (ones (nextN N + 1)))) cF (reg (fword (nextN N))))
        pN (reg (ones N))) tIn ⟨[], rwds N U⟩) tP ⟨(rs.map fun p => ones p.1) ++ Pl, ones N :: R⟩
    have hR₁ : RestU (nextN N) N U ((rs.map fun p => ones p.1) ++ Pl) (ones N :: R) σ₁ := hR.of_update
    have s2 := runs_skp (a := 0) (s := tCnt) (j := tJ) (by decide) σ₁ (by tsimp [σ₁, hC, List.replicate_succ])
      (by tsimp [σ₁, hJ, emp])
    have hUv : ∀ q ∈ U, q < Fm N := by
      intro q hq
      have : ∀ g Q, ∀ q ∈ upList N (2 ^ kOf N) g Q, q < Fm N := by
        intro g; induction g with
        | zero => simp [upList]
        | succ g ih => intro Q q hq; simp only [upList, List.mem_cons] at hq; rcases hq with rfl | hq
                       · exact recomb_lt _ _ _
                       · exact ih _ q hq
      exact this _ _ q hq
    have ih := runs_upLoop' rs (nextN N) N U _ Pl (ones N :: R) ([] :: Cl)
      (by rw [length_upList]; exact hok') hUv (by have := (next_facts hN).2.2.2; omega)
      (hR₁.update_cnt ⟨[] :: Cl, List.replicate rs.length []⟩) (by tsimp)
    have e : Function.update σ₁ tCnt (σ₁ tCnt).next =
        Function.update σ₁ tCnt ⟨[] :: Cl, List.replicate rs.length []⟩ := by
      congr 1; tsimp [σ₁, hC, List.replicate_succ]
    refine (Runs.loop_step (by simp [hC]) ((Runs.then s1 s2).mono (fun σ' h' => by rw [h', e]; exact ih)
      le_rfl)).mono (fun σ' h => ?_) ?_
    · obtain ⟨Na', hle, h', hc⟩ := h
      refine ⟨Na', by simpa [lastN] using hle, ?_, ?_⟩
      · simpa [lastN, upFold, U, List.reverse_cons, List.append_assoc] using h'
      · rw [hc, List.length_cons, List.replicate_succ', List.append_assoc]; rfl
    · have hc : (σ₁ tCnt).cur.length = 0 := by tsimp [σ₁, hC, List.replicate_succ]
      simp [upFoldCost]; omega

/-! ### The final state of the multiplier -/

/-- The level sizes a down-sweep saves sum to at most twice the size plus the fuel. -/
theorem traj_sizes : ∀ (j N : ℕ) (L : List ℕ),
    clen ((traj j N L).1.map fun p => ones p.1) ≤ 2 * N + j
  | 0, N, L => by simp [traj]
  | j + 1, N, L => by
    unfold traj
    split_ifs with h
    · simp
    · have ih := traj_sizes j (nextN N) (nextBatch (nextN N) (kOf N) (pieceOf N) L)
      have := (next_facts (not_lt.mp h)).2.2.1
      simp only [List.map_cons, clen_cons, length_ones]
      omega

/-- What `ssMain` leaves on the tapes it names: the product on `tIn`, and every other
tape empty or one of a few registers and counters of size `O(N)`. -/
def SSEnd0 (N v : ℕ) (σ : Fin 𝕋 → WTape) : Prop :=
  (∃ Na, Na ≤ N ∧ AluReady Na σ) ∧ (∀ i ∈ idle, σ i = emp) ∧ σ pN = reg (ones N) ∧
    σ tIn = ⟨[], [rwd N v]⟩ ∧ clen (σ tP).words ≤ 3 * N ∧ clen (σ tCnt).words ≤ N ∧
    clen (σ tG).words ≤ N ∧ σ c2047 = reg (ones 2047) ∧ clen (σ fG).words ≤ 1

/-- What `ssMain` leaves on the whole bank. -/
def SSEnd (N v : ℕ) (σ : Fin 𝕋 → WTape) : Prop := SSEnd0 N v σ ∧ σ 7 = emp ∧ σ 49 = emp

theorem runs_ssMain_end0 {N x y : ℕ} (hN : 0 < N) (hk : 2 ^ kOf N ∣ N) (hx : x < Fm N) (hy : y < Fm N)
    (σ : Fin 𝕋 → WTape) (hS : SSStart N x y σ) :
    Runs ssMain σ (SSEnd0 N (x * y % Fm N)) (ssCost N [x, y]) := by
  obtain ⟨σ1, s1, hR1, hG1⟩ := runs_ssInit hN σ hS
  have hv : ∀ z ∈ [x, y], z < 2 ^ N + 1 := by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
  have he : Even [x, y].length := by simp
  have s2 := runs_downLoop N N [x, y] [] [] σ1 [] hR1 hk he hv (by simpa using hG1)
  set t := traj N N [x, y] with ht
  have hinv := traj_inv N N [x, y] hN hk he hv
  have hsmall : t.2.1 < N0 := traj_lt N N [x, y] le_rfl
  have hlen : t.1.length ≤ N := length_traj_le N N [x, y]
  have hsz : clen (t.1.map fun p => ones p.1) ≤ 2 * N + N := traj_sizes N N [x, y]
  have tail : ∀ σ', Rest t.2.1 t.2.2 ((t.1.map fun p => ones p.1).reverse ++ [])
      (List.replicate t.1.length [] ++ []) σ' → σ' tG = ⟨List.replicate N [] ++ [], []⟩ →
      Runs (.seq baseBatch <| .seq swapIO <| .seq (rewind tCnt) upLoop) σ'
        (SSEnd0 N (x * y % Fm N))
        (t.2.2.length * ((t.2.1 + 2) * (420 * t.2.1 + 1400)) + 1 +
          (2 * (t.2.2.length * (t.2.1 + 2)) + t.2.2.length * (5 * t.2.1 + 30) + 20 + 1 +
            (t.1.length + 2 + 1 + upFoldCost t.1.reverse))) := by
    intro σ' hR hG
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
    have b4 := (runs_upLoop' t.1.reverse NL NL Qb τ3 [] [] [] (by rw [hQb, List.length_map, length_pairsOf]; exact hok)
      (by intro q hq; simp only [Qb, List.mem_map] at hq; obtain ⟨p, -, rfl⟩ := hq; exact Nat.mod_lt _ (by positivity))
      le_rfl hRU (by tsimp [τ3, τ2, τ1, hC, List.length_reverse])).frame _ upLoop_touches
    refine (Runs.then b1 (Runs.then b2 (Runs.then b3 b4))).mono (fun σ'' h => ?_) ?_
    · obtain ⟨⟨Na', hle, ⟨hA, hi', hp', h4, hP'⟩, hC'⟩, hfr⟩ := h
      have e1 : σ'' c2047 = σ' c2047 := by rw [hfr c2047 (by simp)]; tsimp [τ3, τ2, τ1]
      have e2 : σ'' fG = σ' fG := by rw [hfr fG (by simp)]; tsimp [τ3, τ2, τ1]
      have e3 : σ'' tG = σ' tG := by rw [hfr tG (by simp)]; tsimp [τ3, τ2, τ1]
      have hl := (lastN_traj N N [x, y]).1
      rw [hl] at hle hp' h4
      refine ⟨⟨Na', hle, hA⟩, hi', hp', ?_, ?_, ?_, ?_, by rw [e1, hc], ?_⟩
      · rw [h4, hQb, upFold_traj N N [x, y] hk he hv]
        simp [pairsOf, rwds, ssMul_correct N x y hk hx hy]
      · rw [hP']
        simp only [WTape.words, List.reverse_nil, List.nil_append, List.append_nil, List.map_reverse,
          List.reverse_reverse, clen_reverse]
        omega
      · rw [hC']; simp [WTape.words, clen, List.map_replicate]; omega
      · rw [e3, hG]; simp [WTape.words, clen, List.map_replicate]
      · rw [e2, hf]
        have h1 : Nat.size NL ≤ S0 - 1 := Nat.size_le.mpr (by rw [← N0_eq]; exact hsmall)
        rw [S0_eq] at h1
        simp [WTape.words, clen, reg]; omega
    · have c1 : clen (rwds NL LL) = LL.length * (NL + 2) := clen_rwds _ _
      have c2 : Qb.length ≤ LL.length := by simp [Qb, length_pairsOf]; omega
      have c3 := Nat.mul_le_mul_right (5 * NL + 30) c2
      tsimp [τ2, τ1, hC, List.length_reverse, WTape.words, clen_reverse, clen_append, c1]
      simp [clen]
      omega
  exact Runs.then s1 (Runs.seq (s2.mono (fun σ' h => tail σ' h.1 (by simpa using h.2)) le_rfl))

theorem runs_ssMain_end {N x y : ℕ} (hN : 0 < N) (hk : 2 ^ kOf N ∣ N) (hx : x < Fm N) (hy : y < Fm N)
    (σ : Fin 𝕋 → WTape) (hS : SSStart N x y σ) :
    Runs ssMain σ (SSEnd N (x * y % Fm N)) (ssCost N [x, y]) := by
  have h7 : σ 7 = emp := hS.2.2 7 (by decide) (by decide)
  have h49 : σ 49 = emp := hS.2.2 49 (by decide) (by decide)
  refine ((runs_ssMain_end0 hN hk hx hy σ hS).frame _ ssMain_touches).mono (fun σ' h => ?_) le_rfl
  exact ⟨h.1, by rw [h.2 7 (by simp), h7], by rw [h.2 49 (by simp), h49]⟩

/-! ### Clearing the bank -/

/-- Clear the registers and counters the multiplier leaves behind. -/
noncomputable def ssWipe : Cmd 0 𝕋 :=
  .seq (clear cW) <| .seq (clear cF) <| .seq (clear cN) <| .seq (clear c1) <| .seq (clear pN) <|
  .seq (clear tP) <| .seq (clear tCnt) <| .seq (clear tG) <| .seq (clear c2047) (clear fG)

/-- The multiplier followed by the wipe. -/
noncomputable def ssClean : Cmd 0 𝕋 := .seq ssMain ssWipe

/-- The product alone on `tIn`. -/
def SSDone (N v : ℕ) (σ : Fin 𝕋 → WTape) : Prop :=
  σ tIn = ⟨[], [rwd N v]⟩ ∧ ∀ i, i ≠ tIn → σ i = emp

theorem runs_ssWipe {N v : ℕ} (σ : Fin 𝕋 → WTape) (h : SSEnd N v σ) :
    Runs ssWipe σ (SSDone N v) (20 * N + 5000) := by
  obtain ⟨⟨⟨Na, hle, ⟨⟨hW, hF⟩, hN, h1, hX, hY, hO, hS1, hS2, hS3, hbX, hbY⟩⟩, hi, hp, hIn, hP, hC, hG, h2047,
    hfG⟩, h7, h49⟩ := h
  have key : ∀ i : Fin 𝕋, i ≠ tIn → i ∉ [cW, cF, cN, c1, pN, tP, tCnt, tG, c2047, fG] → σ i = emp := by
    intro i hne hm
    have : i ∈ idle ∨ i ∈ [aX, aY, aO, aS1, aS2, aS3, bX, bY, 7, 49] := by revert i; decide
    rcases this with hm' | hm'
    · exact hi i hm'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
      rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  apply Runs.of_wp
  simp only [ssWipe, WP, wp_clear]
  refine ⟨⟨by tsimp [hIn], fun i hne => ?_⟩, ?_⟩
  · by_cases hm : i ∈ [cW, cF, cN, c1, pN, tP, tCnt, tG, c2047, fG]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tsimp [emp]
    · have hk := key i hne hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hm
      rw [Function.update_of_ne n10, Function.update_of_ne n9, Function.update_of_ne n8,
        Function.update_of_ne n7, Function.update_of_ne n6, Function.update_of_ne n5,
        Function.update_of_ne n4, Function.update_of_ne n3, Function.update_of_ne n2,
        Function.update_of_ne n1, hk]
  · have r : ∀ w : List Bool, clen (reg w).words = w.length + 1 := fun w => by simp [reg, WTape.words, clen]
    have e1 := r (ones (Na + 1)); have e2 := r (fword Na); have e3 := r (ones Na); have e4 := r [true]
    have e5 := r (ones N); have e6 := r (ones 2047)
    rw [← hW] at e1; rw [← hF] at e2; rw [← hN] at e3; rw [← h1] at e4; rw [← hp] at e5; rw [← h2047] at e6
    simp only [length_ones, fword, length_bits, List.length_singleton] at e1 e2 e3 e4 e5 e6
    tsimp [e1, e2, e3, e4, e5, e6]
    omega

theorem runs_ssClean {N x y : ℕ} (hN : 0 < N) (hk : 2 ^ kOf N ∣ N) (hx : x < Fm N) (hy : y < Fm N)
    (σ : Fin 𝕋 → WTape) (hS : SSStart N x y σ) :
    Runs ssClean σ (SSDone N (x * y % Fm N)) (ssCost N [x, y] + 1 + (20 * N + 5000)) :=
  Runs.seq ((runs_ssMain_end hN hk hx hy σ hS).mono (fun σ' h => runs_ssWipe σ' h) le_rfl)

end IntegerMultBounds.Schoenhage
