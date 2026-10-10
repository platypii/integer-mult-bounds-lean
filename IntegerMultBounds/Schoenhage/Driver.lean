import IntegerMultBounds.Schoenhage.LevelMk

/-! The level driver on word tapes: bookkeeping fragments between levels. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

namespace Tp
abbrev fG : Fin 𝕋 := 59
abbrev tP : Fin 𝕋 := 60
abbrev tCnt : Fin 𝕋 := 61
abbrev tG : Fin 𝕋 := 62
abbrev c2047 : Fin 𝕋 := 63
end Tp

/-! ### Between levels -/

/-- Make the output batch the input batch. -/
noncomputable def swapIO : Cmd 0 𝕋 :=
  .seq (clear tIn) <| .seq (rewind tOut) <| .seq (appendAll tOut tIn (by decide)) <| .seq (rewind tIn) (clear tOut)

theorem runs_swapIO {N : ℕ} (σ : Fin 𝕋 → WTape) (L : List ℕ) {Il : List (List Bool)}
    (hIn : σ tIn = ⟨Il, []⟩) (hO : σ tOut = ⟨(rwds N L).reverse, []⟩) :
    Runs swapIO σ (· = Function.update (Function.update σ tIn ⟨[], rwds N L⟩) tOut emp)
      (2 * clen Il + L.length * (5 * N + 30) + 20) := by
  unfold swapIO
  refine (Runs.then (runs_clear tIn σ) <| Runs.then (runs_rewind tOut _) <|
    Runs.then (runs_appendAll (a := 0) (s := tOut) (d := tIn) (by decide) (N + 1) (rwds N L) _ [] []
      (by tsimp [hO]) (by tsimp) (rwds_length_le N L)) <|
    Runs.then (runs_rewind tIn _) (runs_clear tOut _)).mono (fun σ' h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> tsimp [emp]
  · tsimp [hIn, hO, WTape.words, clen_reverse, clen_rwds, length_rwds]
    nlinarith

/-- Push `pN` on the size stack and a tick on the level count. -/
noncomputable def pushN : Cmd 0 𝕋 :=
  .seq (op0 Rules.copy false pN tP (by decide)) <| .seq (rewind pN) (emit [[]] tCnt)

theorem runs_pushN {N : ℕ} (σ : Fin 𝕋 → WTape) (hp : σ pN = reg (ones N)) {P C : List (List Bool)}
    (hP : σ tP = ⟨P, []⟩) (hC : σ tCnt = ⟨C, []⟩) :
    Runs pushN σ (· = Function.update (Function.update σ tP ⟨ones N :: P, []⟩) tCnt ⟨[] :: C, []⟩)
      (3 * N + 20) := by
  apply Runs.of_wp
  simp only [pushN, WP, wp_op0, wp_rewind, wp_emit]
  tsimp [hp, hP, hC, reg, Rules.output_copy]
  have t1 := time_le Rules.copy (ones N) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hp, hP, hC, reg]
  · simp at t1 ⊢; omega

/-- Make the inner size the outer size. -/
noncomputable def nextPN : Cmd 0 𝕋 :=
  .seq (clear pN) <| .seq (op0 Rules.copy false pNp pN (by decide)) <| .seq (rewind pNp) (rewind pN)

theorem runs_nextPN {N Np : ℕ} (σ : Fin 𝕋 → WTape) (hp : σ pN = reg (ones N)) (hNp : σ pNp = reg (ones Np)) :
    Runs nextPN σ (· = Function.update σ pN (reg (ones Np))) (2 * N + 3 * Np + 30) := by
  apply Runs.of_wp
  simp only [nextPN, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hp, hNp, reg, Rules.output_copy]
  have t1 := time_le Rules.copy (ones Np) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hp, hNp, reg]
  · simp [clen, WTape.words] at t1 ⊢; omega

/-- Drop a level's registers. -/
noncomputable def clearLevel : Cmd 0 𝕋 :=
  .seq (clear pK) <| .seq (clear cM) <| .seq (clear pNp) <| .seq (clear tK) <| .seq (clear pKh) <|
  .seq (clear pNK) <| .seq (clear cHN) <| .seq (clear cWA) <| .seq (clear cH1) (clear cR)

theorem runs_clearLevel (σ : Fin 𝕋 → WTape) :
    Runs clearLevel σ (· = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update σ pK emp) cM emp) pNp emp) tK emp) pKh emp) pNK emp) cHN emp) cWA emp) cH1 emp) cR emp)
      (2 * (clen (σ pK).words + clen (σ cM).words + clen (σ pNp).words + clen (σ tK).words +
        clen (σ pKh).words + clen (σ pNK).words + clen (σ cHN).words + clen (σ cWA).words +
        clen (σ cH1).words + clen (σ cR).words) + 40) := by
  apply Runs.of_wp
  simp only [clearLevel, WP, wp_clear]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [emp]
  · tsimp; omega

/-- The level test: `fG = ones (size N - 2047)`, which starts with a one iff `N0 ≤ N`. -/
noncomputable def testG : Cmd 0 𝕋 :=
  .seq (clear fG) <| .seq sizeSetupN <| .seq (.seq sizeLoop (.seq (clear qR) (clear qT))) <|
  .seq (op1 Rules.drop false qB c2047 fG (by decide) (by decide) (by decide)) <| .seq (rewind qB) <|
  .seq (rewind c2047) <| .seq (rewind fG) (clear qB)

theorem runs_testG {N : ℕ} (σ : Fin 𝕋 → WTape) (hp : σ pN = reg (ones N)) (h1 : σ c1 = reg [true])
    (hc : σ c2047 = reg (ones 2047)) (hR : σ qR = emp) (hT : σ qT = emp) (hB : σ qB = emp) (hS : σ qS = emp)
    (hJ : σ tJ = emp) :
    Runs testG σ (· = Function.update σ fG (reg (ones (Nat.size N - 2047))))
      (2 * clen (σ fG).words + 200 * N + 20000) := by
  unfold testG
  have s0 := runs_clear (a := 0) fG σ
  set σ₀ := Function.update σ fG ⟨[], []⟩
  have s1 := runs_sizeSetupN (n := N) σ₀ (by tsimp [σ₀, hp]) (by tsimp [σ₀, hR]) (by tsimp [σ₀, hT])
    (by tsimp [σ₀, hB])
  set σ₁ := Function.update (Function.update (Function.update σ₀ qR (reg (ones N)))
        qT ⟨[], List.replicate N []⟩) qB (reg (ones 0))
  have s2 := runs_sizeOf (n := N) σ₁ (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁, σ₀, h1])
    (by tsimp [σ₁, σ₀, hS]) (by tsimp [σ₁, σ₀, hJ])
  set σ₂ := Function.update (Function.update (Function.update σ₁ qR emp) qB (reg (ones (Nat.size N)))) qT emp
  have s3 : Runs (a := 0) (.seq (op1 Rules.drop false qB c2047 fG (by decide) (by decide) (by decide)) <|
      .seq (rewind qB) <| .seq (rewind c2047) <| .seq (rewind fG) (clear qB)) σ₂
      (· = Function.update σ fG (reg (ones (Nat.size N - 2047)))) (6 * N + 10000) := by
    apply Runs.of_wp
    simp only [WP, wp_op1, wp_rewind, wp_clear]
    tsimp [σ₂, σ₁, σ₀, hc, reg, Rules.output_drop]
    have t1 := time_le Rules.drop (ones (Nat.size N)) (fun _ => ones 2047) 2047 (fun _ => by simp)
    have hs := size_le_self N
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [σ₂, σ₁, σ₀, hc, hR, hT, hB, reg, emp]
    · simp [clen, WTape.words] at t1 ⊢; omega
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 s3))).mono (fun σ' h => h) (by omega)

theorem startsOne_test {N : ℕ} : StartsOne (reg (ones (Nat.size N - 2047))) ↔ N0 ≤ N := by
  have key : 2047 < Nat.size N ↔ N0 ≤ N := by
    have e : S0 - 1 = 2047 := by rw [S0_eq]
    constructor
    · intro h; rw [N0_eq]; exact Nat.lt_size.mp (by rw [e]; exact h)
    · intro h; rw [← e]; exact Nat.lt_size.mpr (by rw [← N0_eq]; exact h)
  constructor
  · intro h
    by_contra hlt
    have : Nat.size N - 2047 = 0 := by have := mt key.mp hlt; omega
    rw [this] at h
    exact not_startsOne_reg_nil h
  · intro h
    apply startsOne_reg_ones
    have := key.mpr h
    omega

/-! ### The resting state between levels -/

/-- Tapes empty between levels. -/
def idle : List (Fin 𝕋) := quiet ++ mkFree ++ [tD, tX, tY, tOut]

/-- Between levels: outer size `N` (also the unit's modulus), batch `L`, size stack `P`, level count `C`. -/
def Rest (N : ℕ) (L : List ℕ) (P C : List (List Bool)) (σ : Fin 𝕋 → WTape) : Prop :=
  AluReady N σ ∧ (∀ i ∈ idle, σ i = emp) ∧ σ pN = reg (ones N) ∧ σ tIn = ⟨[], rwds N L⟩ ∧
    σ tP = ⟨P, []⟩ ∧ σ tCnt = ⟨C, []⟩ ∧ σ c2047 = reg (ones 2047) ∧ σ fG = reg (ones (Nat.size N - 2047))

/-- A rest state rebuilt from a rest state by updates of the driver's own tapes. -/
theorem Rest.of_update {N N' : ℕ} {L L' : List ℕ} {P P' C C' : List (List Bool)} {σ : Fin 𝕋 → WTape}
    (h : Rest N L P C σ) :
    Rest N' L' P' C' (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update σ cN (reg (ones N'))) cW (reg (ones (N' + 1))))
      cF (reg (fword N'))) pN (reg (ones N'))) tIn ⟨[], rwds N' L'⟩) tP ⟨P', []⟩) tCnt ⟨C', []⟩)
      fG (reg (ones (Nat.size N' - 2047)))) := by
  obtain ⟨⟨-, -, hc1, hX, hY, hO, hS1, hS2, hS3, hbX, hbY⟩, hi, -, -, -, -, hc, -⟩ := h
  refine ⟨⟨⟨by tsimp, by tsimp⟩, by tsimp, by tsimp [hc1], by tsimp [hX], by tsimp [hY], by tsimp [hO],
    by tsimp [hS1], by tsimp [hS2], by tsimp [hS3], by tsimp [hbX], by tsimp [hbY]⟩, ?_, by tsimp, by tsimp,
    by tsimp, by tsimp, by tsimp [hc], by tsimp⟩
  intro i hm
  have hne : i ≠ cN ∧ i ≠ cW ∧ i ≠ cF ∧ i ≠ pN ∧ i ≠ tIn ∧ i ≠ tP ∧ i ≠ tCnt ∧ i ≠ fG := by
    revert hm; revert i; decide
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := hne
  rw [Function.update_of_ne n8, Function.update_of_ne n7, Function.update_of_ne n6, Function.update_of_ne n5,
    Function.update_of_ne n4, Function.update_of_ne n3, Function.update_of_ne n2, Function.update_of_ne n1]
  exact hi i hm

/-! ### One level down -/

theorem down_arith (N Np k K M l nb r F c Kr D1 D2 : ℕ) (hNp : Np ≤ N) (hM : M ≤ Np) (hk : k ≤ Np)
    (hK : 1 ≤ K) (hnb : nb ≤ l * K) (hr : r ≤ 2 * K * (Np + 1 + 1)) (hF : F ≤ N) (hc : c = K) (hKr : Kr ≤ K)
    (hD1 : D1 ≤ Np) (hD2 : D2 ≤ Np) :
    2000 * N + 1100 * K + 1000 * k + 30 * N + (K + 1) * (12 * (M + Np + 1) + 100) + 200 * Np + 200 * M +
      10000 + 1 +
    (l * ((k + 2) * (5000 * (K + 1) * (Np + 2)) + 10 * N + K * (20 * Np + 100) + 200) + 1 +
      (2 * (l * (N + 2)) + nb * (5 * Np + 30) + 20 + 1 +
        (3 * N + 20 + 1 + (2 * N + 3 * Np + 30 + 1 +
          (2 * (k + 1 + (M + 1) + (Np + 1) + c + (Kr + 1) + (D1 + 1) + (D2 + 1) + (Np + 2 + 1) + (Np + 1 + 1) +
            (r + 1)) + 40 + 1 + (2 * F + 200 * Np + 20000)))))) ≤
    (l + 1) * ((k + 2) * (10000 * (K + 1) * (Np + 2)) + 20000 * N + 100000) := by
  rw [hc]
  have h1 : nb * (5 * Np + 30) ≤ l * K * (5 * Np + 30) := Nat.mul_le_mul_right _ hnb
  have h2 : (K + 1) * (12 * (M + Np + 1) + 100) ≤ (K + 1) * (24 * Np + 112) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : l * (K * (20 * Np + 100)) + l * K * (5 * Np + 30) ≤ l * ((k + 2) * (5000 * (K + 1) * (Np + 2))) := by
    rw [← Nat.mul_assoc l K, ← Nat.mul_add, Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith
  have h4 : (K + 1) * (24 * Np + 112) + 2 * r + 1110 * K ≤ (k + 2) * (10000 * (K + 1) * (Np + 2)) := by
    nlinarith
  nlinarith


theorem length_nextBatch_le (Np k M : ℕ) : ∀ (L : List ℕ),
    (∀ x, (tpieces Np k M x).length = 2 ^ k) → (nextBatch Np k M L).length ≤ L.length * 2 ^ k
  | [], _ => by simp [nextBatch]
  | [_], _ => by simp [nextBatch]
  | x :: y :: L, h => by
    have ih := length_nextBatch_le Np k M L h
    simp only [nextBatch, List.length_append, List.length_cons]
    rw [length_zipFlat _ _ (by rw [h, h]), h]
    nlinarith

/-- A bound on one level of the down-sweep with a batch of `l` residues. -/
def downCost (N l : ℕ) : ℕ :=
  (l + 1) * ((kOf N + 2) * (10000 * (2 ^ kOf N + 1) * (nextN N + 2)) + 20000 * N + 100000)

/-- One level of the down-sweep. -/
noncomputable def downLevel : Cmd 0 𝕋 :=
  .seq mkLevel <| .seq downBatch <| .seq swapIO <| .seq pushN <| .seq nextPN <| .seq clearLevel testG

set_option maxHeartbeats 4000000 in
theorem runs_downLevel {N : ℕ} (hN : N0 ≤ N) (hk : 2 ^ kOf N ∣ N) {L : List ℕ} {P C : List (List Bool)} (σ : Fin 𝕋 → WTape)
    (hR : Rest N L P C σ) (he : Even L.length) (hv : ∀ x ∈ L, x < 2 ^ N + 1) :
    Runs downLevel σ (· = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update σ
        cN (reg (ones (nextN N)))) cW (reg (ones (nextN N + 1)))) cF (reg (fword (nextN N))))
        pN (reg (ones (nextN N)))) tIn ⟨[], rwds (nextN N) (nextBatch (nextN N) (kOf N) (pieceOf N) L)⟩)
        tP ⟨ones N :: P, []⟩) tCnt ⟨[] :: C, []⟩) fG (reg (ones (Nat.size (nextN N) - 2047))))
      (downCost N L.length) := by
  obtain ⟨hr, hi, hp, hIn, hP, hC, hc, hG⟩ := hR
  obtain ⟨hk1, hlo, h2N, hNlt⟩ := next_facts hN
  have hsp := split_exact hk
  have f : ∀ i ∈ idle, σ i = emp := hi
  unfold downLevel
  have s1 := runs_mkLevel hN σ hr hp (fun i hm => f i (by simp only [idle, List.mem_append]; tauto))
  set σ₁ := Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update σ
          pK (reg (ones (kOf N)))) cM (reg (ones (pieceOf N)))) pNp (reg (ones (nextN N))))
          tK ⟨[], List.replicate (2 ^ kOf N) []⟩) pKh (reg (ones (2 ^ kOf N / 2))))
          pNK (reg (ones (nextN N - kOf N)))) cHN (reg (ones (nextN N / 2))))
          cWA (reg (ones (nextN N + 2)))) cH1 (reg (hword (nextN N))))
          cN (reg (ones (nextN N)))) cW (reg (ones (nextN N + 1)))) cF (reg (fword (nextN N))))
          cR (reg (Rules.ruler (pieceOf N) (nextN N + 1) (2 ^ kOf N)))
  have hq : Quiet σ₁ := by
    intro i hm
    have hne : i ≠ pK ∧ i ≠ cM ∧ i ≠ pNp ∧ i ≠ tK ∧ i ≠ pKh ∧ i ≠ pNK ∧ i ≠ cHN ∧ i ≠ cWA ∧ i ≠ cH1 ∧
        i ≠ cN ∧ i ≠ cW ∧ i ≠ cF ∧ i ≠ cR := by
      revert hm; revert i; decide
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := hne
    simp only [σ₁, Function.update_of_ne n1, Function.update_of_ne n2, Function.update_of_ne n3,
      Function.update_of_ne n4, Function.update_of_ne n5, Function.update_of_ne n6, Function.update_of_ne n7,
      Function.update_of_ne n8, Function.update_of_ne n9, Function.update_of_ne n10, Function.update_of_ne n11,
      Function.update_of_ne n12, Function.update_of_ne n13]
    exact f i (by simp only [idle, List.mem_append]; tauto)
  obtain ⟨-, -, hc1, hX, hY, hO, hS1, hS2, hS3, hbX, hbY⟩ := hr
  have hL₁ : LevelRegs N (nextN N) (kOf N) (pieceOf N) σ₁ :=
    ⟨⟨⟨by tsimp [σ₁], by tsimp [σ₁]⟩, by tsimp [σ₁], by tsimp [σ₁, hc1], by tsimp [σ₁, hX], by tsimp [σ₁, hY],
      by tsimp [σ₁, hO], by tsimp [σ₁, hS1], by tsimp [σ₁, hS2], by tsimp [σ₁, hS3], by tsimp [σ₁, hbX],
      by tsimp [σ₁, hbY]⟩, hq, by tsimp [σ₁], by tsimp [σ₁], by tsimp [σ₁], by tsimp [σ₁], by tsimp [σ₁],
      by tsimp [σ₁], by tsimp [σ₁, hp], by tsimp [σ₁]⟩
  have fX := f tX (by decide); have fY := f tY (by decide); have fD := f tD (by decide)
  have fO := f tOut (by decide)
  have s2 := runs_downBatch (N := N) (by omega) (by conv_lhs => rw [hsp]; rw [mul_comm]) (by omega) L σ₁ [] [] he hv hL₁
    (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁, fX]) (by tsimp [σ₁, fY]) (by tsimp [σ₁, fD])
    (by tsimp [σ₁, hIn]) (by tsimp [σ₁, fO, emp])
  set NB := nextBatch (nextN N) (kOf N) (pieceOf N) L
  set σ₂ := Function.update (Function.update σ₁ tIn ⟨(rwds N L).reverse ++ [], []⟩)
    tOut ⟨(rwds (nextN N) NB).reverse ++ [], []⟩
  have s3 := runs_swapIO (N := nextN N) σ₂ NB (Il := (rwds N L).reverse ++ []) (by tsimp [σ₂]) (by tsimp [σ₂])
  set σ₃ := Function.update (Function.update σ₂ tIn ⟨[], rwds (nextN N) NB⟩) tOut emp
  have s4 := runs_pushN (N := N) (P := P) (C := C) σ₃ (by tsimp [σ₃, σ₂, σ₁, hp]) (by tsimp [σ₃, σ₂, σ₁, hP])
    (by tsimp [σ₃, σ₂, σ₁, hC])
  set σ₄ := Function.update (Function.update σ₃ tP ⟨ones N :: P, []⟩) tCnt ⟨[] :: C, []⟩
  have s5 := runs_nextPN (N := N) (Np := nextN N) σ₄ (by tsimp [σ₄, σ₃, σ₂, σ₁, hp]) (by tsimp [σ₄, σ₃, σ₂, σ₁])
  set σ₅ := Function.update σ₄ pN (reg (ones (nextN N)))
  have s6 := runs_clearLevel σ₅
  set σ₆ := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update σ₅ pK emp) cM emp) pNp emp) tK emp) pKh emp) pNK emp) cHN emp) cWA emp) cH1 emp) cR emp
  have fqR := f qR (by decide); have fqT := f qT (by decide); have fqB := f qB (by decide)
  have fqS := f qS (by decide); have ftJ := f tJ (by decide)
  have s7 := runs_testG (N := nextN N) σ₆ (by tsimp [σ₆, σ₅]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hc1])
    (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hc]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, fqR])
    (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, fqT]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, fqB])
    (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, fqS]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, ftJ])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 s7)))))).mono
    (fun σ' h => ?_) ?_
  · have fpK := f pK (by decide); have fcM := f cM (by decide); have fNp := f pNp (by decide)
    have ftK := f tK (by decide); have fKh := f pKh (by decide); have fNK := f pNK (by decide)
    have fHN := f cHN (by decide); have fWA := f cWA (by decide); have fH1 := f cH1 (by decide)
    have fcR := f cR (by decide)
    rw [h]; funext i; fin_cases i <;> tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, fpK, fcM, fNp, ftK, fKh, fNK, fHN, fWA,
      fH1, fcR, fO, emp]
  · have hNB : NB.length ≤ L.length * 2 ^ kOf N := length_nextBatch_le _ _ _ _ (fun x => by
      rw [tpieces, fwdIter_length _ _ _ _ _ rfl (by simp [length_pieces]), length_pieces])
    have hRl := length_ruler (M := pieceOf N) (W := nextN N + 1) (by omega) (2 ^ kOf N)
    have hHl : (hword (nextN N)).length = nextN N + 1 := by simp [hword]
    have hfG : clen (σ₆ fG).left + clen (σ₆ fG).right ≤ N := by
      tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hG, reg, WTape.words, clen]
      have := size_le_self N; omega
    have cL : clen (rwds N L) = L.length * (N + 2) := clen_rwds N L
    tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, reg, WTape.words, clen_reverse, clen_append, cL, hHl, downCost]
    exact down_arith N (nextN N) (kOf N) (2 ^ kOf N) (pieceOf N) L.length NB.length _ _ _ _ _ _
      (by omega) (by omega) (by omega) Nat.one_le_two_pow hNB hRl hfG (by simp [clen])
      (Nat.div_le_self _ _) (Nat.sub_le _ _) (Nat.div_le_self _ _)

end IntegerMultBounds.Schoenhage
