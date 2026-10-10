import IntegerMultBounds.Schoenhage.Driver

/-! The level driver's up-sweep on word tapes: the base case below `N0`, then
one level per saved size, popped from the size stack. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-! ### Popping a size -/

/-- Read the size below the head of `tP` into `pN` and move the head before it. -/
noncomputable def popN : Cmd 0 𝕋 :=
  .seq (back tP) <| .seq (clear pN) <| .seq (op0 Rules.copy false tP pN (by decide)) <| .seq (rewind pN) (back tP)

theorem runs_popN {N : ℕ} (σ : Fin 𝕋 → WTape) {Pl R : List (List Bool)} (hP : σ tP = ⟨ones N :: Pl, R⟩) :
    Runs popN σ (· = Function.update (Function.update σ tP ⟨Pl, ones N :: R⟩) pN (reg (ones N)))
      (2 * clen (σ pN).words + 6 * N + 30) := by
  apply Runs.of_wp
  simp only [popN, WP, wp_op0, wp_rewind, wp_clear, wp_back]
  tsimp [hP, reg, Rules.output_copy]
  have t1 := time_le Rules.copy (ones N) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hP, reg]
  · simp [clen] at t1 ⊢; omega

/-! ### One level up -/

theorem up_arith (Ni Np k K M g Na r c Kr D1 D2 : ℕ) (hNp : Np ≤ Ni) (hM : M ≤ Np) (hk : k ≤ Np)
    (hK : 1 ≤ K) (hMK : M * K ≤ Ni) (hNa : Na ≤ Np) (hr : r ≤ 2 * K * (Np + 1 + 1)) (hc : c = K) (hKr : Kr ≤ K)
    (hD1 : D1 ≤ Np) (hD2 : D2 ≤ Np) :
    2 * (Np + 1) + 6 * Ni + 30 + 1 +
      (2000 * Ni + 1100 * K + 1000 * k + 30 * Na + (K + 1) * (12 * (M + Np + 1) + 100) + 200 * Np + 200 * M +
          10000 + 1 +
        (g * ((k + 4) * (5000 * (K + 1) * (Np + 2)) + 24 * M * K + 1000 * Ni + 6000) + 1 +
          (2 * (g * K * (Np + 2)) + g * (5 * Ni + 30) + 20 + 1 +
            (2 * (k + 1 + (M + 1) + (Np + 1) + c + (Kr + 1) + (D1 + 1) + (D2 + 1) + (Np + 2 + 1) + (Np + 1 + 1) +
              (r + 1)) + 40)))) ≤
    (g + 1) * ((k + 4) * (10000 * (K + 1) * (Np + 2)) + 30000 * Ni + 100000) := by
  rw [hc]
  have h2 : (K + 1) * (12 * (M + Np + 1) + 100) ≤ (K + 1) * (24 * Np + 112) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : g * (2 * K * (Np + 2)) ≤ g * ((k + 4) * (5000 * (K + 1) * (Np + 2))) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have h5 : g * (24 * M * K) ≤ g * (24 * Ni) := Nat.mul_le_mul_left _ (by nlinarith)
  have h4 : (K + 1) * (24 * Np + 112) + 2 * r + 1110 * K ≤ (k + 4) * (10000 * (K + 1) * (Np + 2)) := by
    nlinarith
  nlinarith


/-- During the up-sweep: the unit's modulus `Na`, the products `Q` modulo `2^N + 1` with `pN = ones N`,
the size stack `Pl` left of the head of `tP`. -/
def RestU (Na N : ℕ) (Q : List ℕ) (Pl R : List (List Bool)) (σ : Fin 𝕋 → WTape) : Prop :=
  AluReady Na σ ∧ (∀ i ∈ idle, σ i = emp) ∧ σ pN = reg (ones N) ∧ σ tIn = ⟨[], rwds N Q⟩ ∧ σ tP = ⟨Pl, R⟩

theorem length_upList (N K : ℕ) : ∀ (g : ℕ) (Q : List ℕ), (upList N K g Q).length = g
  | 0, _ => rfl
  | g + 1, Q => by simp [upList, length_upList N K g]

/-- A bound on one level of the up-sweep with `g` groups. -/
def upCost (N g : ℕ) : ℕ :=
  (g + 1) * ((kOf N + 4) * (10000 * (2 ^ kOf N + 1) * (nextN N + 2)) + 30000 * N + 100000)

/-- One level of the up-sweep. -/
noncomputable def upLevel : Cmd 0 𝕋 := .seq popN <| .seq mkLevel <| .seq upBatch <| .seq swapIO clearLevel

set_option maxHeartbeats 4000000 in
theorem runs_upLevel {Ni : ℕ} (hN : N0 ≤ Ni) (hk : 2 ^ kOf Ni ∣ Ni) {Na : ℕ} (hNa : Na ≤ nextN Ni)
    {g : ℕ} {Q : List ℕ} (hQ : Q.length = g * 2 ^ kOf Ni) (hQv : ∀ q ∈ Q, q < Fm (nextN Ni))
    {Pl R : List (List Bool)} (σ : Fin 𝕋 → WTape) (hR : RestU Na (nextN Ni) Q (ones Ni :: Pl) R σ) :
    Runs upLevel σ (· = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update σ
        cN (reg (ones (nextN Ni)))) cW (reg (ones (nextN Ni + 1)))) cF (reg (fword (nextN Ni))))
        pN (reg (ones Ni))) tIn ⟨[], rwds Ni (upList Ni (2 ^ kOf Ni) g Q)⟩) tP ⟨Pl, ones Ni :: R⟩)
      (upCost Ni g) := by
  obtain ⟨hr, hi, hp, hIn, hP⟩ := hR
  obtain ⟨hk1, hlo, h2N, hNlt⟩ := next_facts hN
  have f : ∀ i ∈ idle, σ i = emp := hi
  unfold upLevel
  have s0 := runs_popN σ hP
  set σ₀ := Function.update (Function.update σ tP ⟨Pl, ones Ni :: R⟩) pN (reg (ones Ni))
  have s1 := runs_mkLevel hN σ₀ (hr.update tP _ (by decide) |>.update pN _ (by decide)) (by tsimp [σ₀])
    (fun i hm => by
      have : i ≠ tP ∧ i ≠ pN := by revert hm; revert i; decide
      simp only [σ₀, Function.update_of_ne this.1, Function.update_of_ne this.2]
      exact f i (by simp only [idle, List.mem_append]; tauto))
  set σ₁ := Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update σ₀
          pK (reg (ones (kOf Ni)))) cM (reg (ones (pieceOf Ni)))) pNp (reg (ones (nextN Ni))))
          tK ⟨[], List.replicate (2 ^ kOf Ni) []⟩) pKh (reg (ones (2 ^ kOf Ni / 2))))
          pNK (reg (ones (nextN Ni - kOf Ni)))) cHN (reg (ones (nextN Ni / 2))))
          cWA (reg (ones (nextN Ni + 2)))) cH1 (reg (hword (nextN Ni))))
          cN (reg (ones (nextN Ni)))) cW (reg (ones (nextN Ni + 1)))) cF (reg (fword (nextN Ni))))
          cR (reg (Rules.ruler (pieceOf Ni) (nextN Ni + 1) (2 ^ kOf Ni)))
  have hq : Quiet σ₁ := by
    intro i hm
    have hne : i ≠ pK ∧ i ≠ cM ∧ i ≠ pNp ∧ i ≠ tK ∧ i ≠ pKh ∧ i ≠ pNK ∧ i ≠ cHN ∧ i ≠ cWA ∧ i ≠ cH1 ∧
        i ≠ cN ∧ i ≠ cW ∧ i ≠ cF ∧ i ≠ cR ∧ i ≠ tP ∧ i ≠ pN := by
      revert hm; revert i; decide
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15⟩ := hne
    simp only [σ₁, σ₀, Function.update_of_ne n1, Function.update_of_ne n2, Function.update_of_ne n3,
      Function.update_of_ne n4, Function.update_of_ne n5, Function.update_of_ne n6, Function.update_of_ne n7,
      Function.update_of_ne n8, Function.update_of_ne n9, Function.update_of_ne n10, Function.update_of_ne n11,
      Function.update_of_ne n12, Function.update_of_ne n13, Function.update_of_ne n14, Function.update_of_ne n15]
    exact f i (by simp only [idle, List.mem_append]; tauto)
  obtain ⟨-, -, hc1, hX, hY, hO, hS1, hS2, hS3, hbX, hbY⟩ := hr
  have hL₁ : LevelRegs Ni (nextN Ni) (kOf Ni) (pieceOf Ni) σ₁ :=
    ⟨⟨⟨by tsimp [σ₁], by tsimp [σ₁]⟩, by tsimp [σ₁], by tsimp [σ₁, σ₀, hc1], by tsimp [σ₁, σ₀, hX],
      by tsimp [σ₁, σ₀, hY], by tsimp [σ₁, σ₀, hO], by tsimp [σ₁, σ₀, hS1], by tsimp [σ₁, σ₀, hS2],
      by tsimp [σ₁, σ₀, hS3], by tsimp [σ₁, σ₀, hbX], by tsimp [σ₁, σ₀, hbY]⟩, hq, by tsimp [σ₁], by tsimp [σ₁],
      by tsimp [σ₁], by tsimp [σ₁], by tsimp [σ₁], by tsimp [σ₁], by tsimp [σ₁, σ₀], by tsimp [σ₁]⟩
  have fD := f tD (by decide); have fO := f tOut (by decide)
  have s2 := runs_upBatch hN hk g Q σ₁ [] [] hQ hQv hL₁ (by tsimp [σ₁]) (by tsimp [σ₁, σ₀, fD])
    (by tsimp [σ₁, σ₀, hIn]) (by tsimp [σ₁, σ₀, fO, emp])
  set U := upList Ni (2 ^ kOf Ni) g Q
  set σ₂ := Function.update (Function.update σ₁ tIn ⟨(rwds (nextN Ni) Q).reverse ++ [], []⟩)
    tOut ⟨(rwds Ni U).reverse ++ [], []⟩
  have s3 := runs_swapIO (N := Ni) σ₂ U (Il := (rwds (nextN Ni) Q).reverse ++ []) (by tsimp [σ₂]) (by tsimp [σ₂])
  set σ₃ := Function.update (Function.update σ₂ tIn ⟨[], rwds Ni U⟩) tOut emp
  have s4 := runs_clearLevel σ₃
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s3 s4)))).mono (fun σ' h => ?_) ?_
  · have fpK := f pK (by decide); have fcM := f cM (by decide); have fNp := f pNp (by decide)
    have ftK := f tK (by decide); have fKh := f pKh (by decide); have fNK := f pNK (by decide)
    have fHN := f cHN (by decide); have fWA := f cWA (by decide); have fH1 := f cH1 (by decide)
    have fcR := f cR (by decide)
    rw [h]; funext i; fin_cases i <;> tsimp [σ₃, σ₂, σ₁, σ₀, fpK, fcM, fNp, ftK, fKh, fNK, fHN, fWA,
      fH1, fcR, fO, emp]
  · have cQ : clen (rwds (nextN Ni) Q) = Q.length * (nextN Ni + 2) := clen_rwds _ _
    have hHl : (hword (nextN Ni)).length = nextN Ni + 1 := by simp [hword]
    have hU : U.length = g := length_upList _ _ _ _
    have hRl := length_ruler (M := pieceOf Ni) (W := nextN Ni + 1) (by omega) (2 ^ kOf Ni)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hKM, -, -, -, -, -, -, -, -, -⟩ := level_facts hN
    tsimp [σ₃, σ₂, σ₁, σ₀, hp, reg, WTape.words, clen_reverse, clen_append, cQ, hHl, upCost, hQ, hU]
    exact up_arith Ni (nextN Ni) (kOf Ni) (2 ^ kOf Ni) (pieceOf Ni) g Na _ _ _ _ _ (by omega) (by omega)
      (by omega) Nat.one_le_two_pow (by rw [mul_comm]; exact hKM) hNa hRl (by simp [clen])
      (Nat.div_le_self _ _) (Nat.sub_le _ _) (Nat.div_le_self _ _)

theorem RestU.of_update {Na N Na' N' : ℕ} {Q Q' : List ℕ} {Pl R Pl' R' : List (List Bool)}
    {σ : Fin 𝕋 → WTape} (h : RestU Na N Q Pl R σ) :
    RestU Na' N' Q' Pl' R' (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update σ cN (reg (ones Na'))) cW (reg (ones (Na' + 1)))) cF (reg (fword Na')))
      pN (reg (ones N'))) tIn ⟨[], rwds N' Q'⟩) tP ⟨Pl', R'⟩) := by
  obtain ⟨⟨-, -, hc1, hX, hY, hO, hS1, hS2, hS3, hbX, hbY⟩, hi, -, -, -⟩ := h
  refine ⟨⟨⟨by tsimp, by tsimp⟩, by tsimp, by tsimp [hc1], by tsimp [hX], by tsimp [hY], by tsimp [hO],
    by tsimp [hS1], by tsimp [hS2], by tsimp [hS3], by tsimp [hbX], by tsimp [hbY]⟩, ?_, by tsimp, by tsimp,
    by tsimp⟩
  intro i hm
  have hne : i ≠ cN ∧ i ≠ cW ∧ i ≠ cF ∧ i ≠ pN ∧ i ≠ tIn ∧ i ≠ tP := by revert hm; revert i; decide
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hne
  rw [Function.update_of_ne n6, Function.update_of_ne n5, Function.update_of_ne n4, Function.update_of_ne n3,
    Function.update_of_ne n2, Function.update_of_ne n1]
  exact hi i hm

theorem RestU.update_cnt {Na N : ℕ} {Q : List ℕ} {Pl R : List (List Bool)} {σ : Fin 𝕋 → WTape}
    (h : RestU Na N Q Pl R σ) (T : WTape) : RestU Na N Q Pl R (Function.update σ tCnt T) := by
  obtain ⟨⟨⟨hW, hF⟩, h2, hc1, hX, hY, hO, hS1, hS2, hS3, hbX, hbY⟩, hi, hp, hIn, hP⟩ := h
  refine ⟨⟨⟨by tsimp [hW], by tsimp [hF]⟩, by tsimp [h2], by tsimp [hc1], by tsimp [hX], by tsimp [hY],
    by tsimp [hO], by tsimp [hS1], by tsimp [hS2], by tsimp [hS3], by tsimp [hbX], by tsimp [hbY]⟩, ?_,
    by tsimp [hp], by tsimp [hIn], by tsimp [hP]⟩
  intro i hm
  have : i ≠ tCnt := by revert hm; revert i; decide
  rw [Function.update_of_ne this]; exact hi i hm

/-! ### The up-sweep over all levels -/

/-- The level outputs of the saved levels, deepest first. -/
noncomputable def upFold : List (ℕ × List ℕ) → List ℕ → List ℕ
  | [], Q => Q
  | (N, L) :: rs, Q => upFold rs (upList N (2 ^ kOf N) (L.length / 2) Q)

/-- The size after the saved levels. -/
def lastN : List (ℕ × List ℕ) → ℕ → ℕ
  | [], Nc => Nc
  | (N, _) :: rs, _ => lastN rs N

/-- The saved levels fit: each is a real level whose inner size is the current size and whose groups match. -/
def UpOK : List (ℕ × List ℕ) → ℕ → ℕ → Prop
  | [], _, _ => True
  | (N, L) :: rs, Nc, ql => N0 ≤ N ∧ 2 ^ kOf N ∣ N ∧ nextN N = Nc ∧ ql = L.length / 2 * 2 ^ kOf N ∧
      UpOK rs N (L.length / 2)

/-- The cost of the up-sweep over the saved levels. -/
def upFoldCost : List (ℕ × List ℕ) → ℕ
  | [] => 0
  | (N, L) :: rs => upCost N (L.length / 2) + 10 + upFoldCost rs

/-- One up level per tick of `tCnt`. -/
noncomputable def upLoop : Cmd 0 𝕋 := .loop tCnt (.seq upLevel (skp tCnt tJ (by decide)))

theorem runs_upLoop :
    ∀ (rs : List (ℕ × List ℕ)) (Na Nc : ℕ) (Q : List ℕ) (σ : Fin 𝕋 → WTape) (Pl R Cl : List (List Bool)),
      UpOK rs Nc Q.length → (∀ q ∈ Q, q < Fm Nc) → Na ≤ Nc →
      RestU Na Nc Q ((rs.map fun p => ones p.1) ++ Pl) R σ → σ tCnt = ⟨Cl, List.replicate rs.length []⟩ →
      Runs upLoop σ (fun σ' => ∃ Na', RestU Na' (lastN rs Nc) (upFold rs Q) Pl
          ((rs.map fun p => ones p.1).reverse ++ R) σ') (upFoldCost rs)
  | [], Na, Nc, Q, σ, Pl, R, Cl, _, _, _, hR, hC => by
    refine (Runs.loop_done (by simp [hC]) ⟨Na, by simpa [lastN, upFold] using hR⟩).mono (fun σ' h => h)
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
    have ih := runs_upLoop rs (nextN N) N U _ Pl (ones N :: R) ([] :: Cl)
      (by rw [length_upList]; exact hok') hUv (by have := (next_facts hN).2.2.2; omega)
      (hR₁.update_cnt ⟨[] :: Cl, List.replicate rs.length []⟩) (by tsimp)
    have e : Function.update σ₁ tCnt (σ₁ tCnt).next =
        Function.update σ₁ tCnt ⟨[] :: Cl, List.replicate rs.length []⟩ := by
      congr 1; tsimp [σ₁, hC, List.replicate_succ]
    refine (Runs.loop_step (by simp [hC]) ((Runs.then s1 s2).mono (fun σ' h' => by rw [h', e]; exact ih)
      le_rfl)).mono (fun σ' h => ?_) ?_
    · obtain ⟨Na', h'⟩ := h
      refine ⟨Na', ?_⟩
      simpa [lastN, upFold, U, List.reverse_cons, List.append_assoc] using h'
    · have hc : (σ₁ tCnt).cur.length = 0 := by tsimp [σ₁, hC, List.replicate_succ]
      simp [upFoldCost]; omega

end IntegerMultBounds.Schoenhage
