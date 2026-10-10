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

end IntegerMultBounds.Schoenhage
