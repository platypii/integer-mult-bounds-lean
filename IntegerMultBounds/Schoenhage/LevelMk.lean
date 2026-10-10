import IntegerMultBounds.Schoenhage.LevelParams

/-! A whole level's registers on word tapes from `pN = ones N`. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-- Drop the ruler's drivers. -/
noncomputable def rulerClean : Cmd 0 𝕋 :=
  .seq (clear tU) <| .seq (clear tV) <| .seq (clear tO1) <| .seq (clear tO2) <| .seq (clear tC) (clear qT)

/-- All of a level's registers from `pN`. -/
noncomputable def mkLevel : Cmd 0 𝕋 :=
  .seq mkK <| .seq mkMK <| .seq mkTicks <| .seq mkSizes <| .seq mkHword <| .seq toInner <|
  .seq rulerPrepA <| .seq rulerPrepB <| .seq rulerBuild rulerClean

/-- The scratch and parameter tapes `mkLevel` needs empty. -/
def mkFree : List (Fin 𝕋) :=
  [qR, qT, qB, qS, tJ, tU, tV, tO1, tO2, tC, sT1, sT2, sA, sO, cU, pK, cM, pNp, tK, pKh, pNK, cHN, cWA, cH1, cR]

set_option maxHeartbeats 1000000 in
theorem runs_mkLevel {N N1 : ℕ} (hN : N0 ≤ N) (σ : Fin 𝕋 → WTape) (hr : AluReady N1 σ)
    (hp : σ pN = reg (ones N)) (hf : ∀ i ∈ mkFree, σ i = emp) :
    Runs mkLevel σ (· = Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update σ
          pK (reg (ones (kOf N)))) cM (reg (ones (pieceOf N)))) pNp (reg (ones (nextN N))))
          tK ⟨[], List.replicate (2 ^ kOf N) []⟩) pKh (reg (ones (2 ^ kOf N / 2))))
          pNK (reg (ones (nextN N - kOf N)))) cHN (reg (ones (nextN N / 2))))
          cWA (reg (ones (nextN N + 2)))) cH1 (reg (hword (nextN N))))
          cN (reg (ones (nextN N)))) cW (reg (ones (nextN N + 1)))) cF (reg (fword (nextN N))))
          cR (reg (Rules.ruler (pieceOf N) (nextN N + 1) (2 ^ kOf N))))
      (2000 * N + 1100 * 2 ^ kOf N + 1000 * kOf N + 30 * N1 +
        (2 ^ kOf N + 1) * (12 * (pieceOf N + nextN N + 1) + 100) + 200 * nextN N + 200 * pieceOf N + 10000) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hk4, hKM, -, hlo, -, -, -, -, -, -, hNp0⟩ := level_facts hN
  have hNp2 : 2 ≤ (nextN N) := by omega
  have hMNp : (pieceOf N) + 1 ≤ (nextN N) := by omega
  have hK1 : 1 ≤ (2 ^ kOf N) := Nat.one_le_two_pow
  have f : ∀ i ∈ mkFree, σ i = emp := hf
  have fqR := f qR (by decide); have fqT := f qT (by decide); have fqB := f qB (by decide)
  have fqS := f qS (by decide); have ftJ := f tJ (by decide); have ftU := f tU (by decide)
  have ftV := f tV (by decide); have fO1 := f tO1 (by decide); have fO2 := f tO2 (by decide)
  have ftC := f tC (by decide); have fT1 := f sT1 (by decide); have fT2 := f sT2 (by decide)
  have fsA := f sA (by decide); have fsO := f sO (by decide); have fcU := f cU (by decide)
  have fpK := f pK (by decide); have fcM := f cM (by decide); have fNp := f pNp (by decide)
  have ftK := f tK (by decide); have fKh := f pKh (by decide); have fNK := f pNK (by decide)
  have fHN := f cHN (by decide); have fWA := f cWA (by decide); have fH1 := f cH1 (by decide)
  have fcR := f cR (by decide)
  have h1 : σ c1 = reg [true] := hr.2.2.1
  unfold mkLevel
  have s1 := runs_mkK σ hp h1 fqR fqT fqB fqS ftJ ftU ftV fpK
  set σ₁ := Function.update σ pK (reg (ones (kOf N)))
  have s2 := runs_mkMK (N := N) σ₁ (by tsimp [σ₁, hp]) (by tsimp [σ₁, h1]) (by tsimp [σ₁]) (by tsimp [σ₁, fqR])
    (by tsimp [σ₁, fqT]) (by tsimp [σ₁, fqS]) (by tsimp [σ₁, ftJ]) (by tsimp [σ₁, ftU]) (by tsimp [σ₁, fcM])
    (by tsimp [σ₁, fNp])
  set σ₂ := Function.update (Function.update (Function.update σ₁
        cM (reg (ones (pieceOf N)))) tU (reg (ones (2 ^ kOf N)))) pNp (reg (ones (nextN N)))
  have s3 := runs_mkTicks (K := 2 ^ kOf N) σ₂ (by tsimp [σ₂]) (by tsimp [σ₂, σ₁, h1]) (by tsimp [σ₂, σ₁, ftK])
    (by tsimp [σ₂, σ₁, fKh]) (by tsimp [σ₂, σ₁, fO1])
  set σ₃ := Function.update (Function.update (Function.update σ₂
        tK ⟨[], List.replicate (2 ^ kOf N) []⟩) pKh (reg (ones ((2 ^ kOf N) / 2)))) tO1 (reg (ones 2))
  have s4 := runs_mkSizes (Np := nextN N) (k := kOf N) σ₃ (by tsimp [σ₃, σ₂]) (by tsimp [σ₃, σ₂, σ₁]) (by tsimp [σ₃])
    (by tsimp [σ₃, σ₂, σ₁, fNK]) (by tsimp [σ₃, σ₂, σ₁, fHN]) (by tsimp [σ₃, σ₂, σ₁, fWA])
  set σ₄ := Function.update (Function.update (Function.update σ₃
        pNK (reg (ones ((nextN N) - (kOf N))))) cHN (reg (ones ((nextN N) / 2)))) cWA (reg (ones ((nextN N) + 2)))
  have s5 := runs_mkHword hNp2 σ₄ (by tsimp [σ₄, σ₃, σ₂]) (by tsimp [σ₄, σ₃]) (by tsimp [σ₄, σ₃, σ₂, σ₁, h1])
    (by tsimp [σ₄, σ₃, σ₂, σ₁, fT2]) (by tsimp [σ₄, σ₃, σ₂, σ₁, fH1])
  set σ₅ := Function.update σ₄ cH1 (reg (hword (nextN N)))
  have hr₅ : AluReady N1 σ₅ := by
    exact hr.update pK _ (by decide) |>.update cM _ (by decide) |>.update tU _ (by decide)
      |>.update pNp _ (by decide) |>.update tK _ (by decide) |>.update pKh _ (by decide)
      |>.update tO1 _ (by decide) |>.update pNK _ (by decide) |>.update cHN _ (by decide)
      |>.update cWA _ (by decide) |>.update cH1 _ (by decide)
  have s6 := runs_toInner (by omega) σ₅ hr₅ (by tsimp [σ₅, σ₄, σ₃, σ₂]) (by tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, fcU])
    (by tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, fT1])
  set σ₆ := Function.update (Function.update (Function.update σ₅
        cN (reg (ones (nextN N)))) cW (reg (ones (nextN N + 1)))) cF (reg (fword (nextN N)))
  have s7 := runs_rulerPrepA (K := 2 ^ kOf N) (M := pieceOf N) σ₆ (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂])
    (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, h1]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂]) (by tsimp [σ₆, σ₅, σ₄, σ₃])
    (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, fT2]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, fqT])
    (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, fO2])
  set σ₇ := Function.update (Function.update (Function.update σ₆
        qT ⟨[], List.replicate (2 ^ kOf N - 1) []⟩) tU (reg (ones (2 * pieceOf N))))
        tO2 (reg (ones (2 * (pieceOf N + 1))))
  have s8 := runs_rulerPrepB (Np := nextN N) (M := pieceOf N) σ₇ (by tsimp [σ₇, σ₆])
    (by tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂]) (by tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂])
    (by tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, fsA]) (by tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, fsO])
    (by tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, ftV]) (by tsimp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, ftC])
  set σ₈ := Function.update (Function.update σ₇
        tV (reg (ones (2 * (nextN N + 1 - pieceOf N))))) tC (reg (ones (2 * (nextN N - pieceOf N))))
  have eW : nextN N + 1 - (pieceOf N + 1) = nextN N - pieceOf N := by omega
  have s9 := runs_rulerBuild (M := pieceOf N) (W := nextN N + 1) (K := 2 ^ kOf N - 1) σ₈
    (by tsimp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, fcR]) (by tsimp [σ₈, σ₇]) (by tsimp [σ₈])
    (by tsimp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃]) (by tsimp [σ₈, σ₇]) (by tsimp [σ₈, eW])
    (by tsimp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, ftJ]) (by tsimp [σ₈, σ₇])
  rw [Nat.sub_add_cancel hK1] at s9
  set σ₉ := Function.update (Function.update σ₈ cR (reg (Rules.ruler (pieceOf N) (nextN N + 1) (2 ^ kOf N))))
        qT ⟨List.replicate (2 ^ kOf N - 1) [], []⟩
  have s10 := runs_clear (a := 0) tU σ₉ |>.then (runs_clear tV _ |>.then (runs_clear tO1 _ |>.then
    (runs_clear tO2 _ |>.then (runs_clear tC _ |>.then (runs_clear qT _)))))
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 s10))))))))).mono (fun σ' h => ?_) ?_
  · rw [h]
    funext i; fin_cases i <;> tsimp [σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, ftU, ftV, fO1, fO2, ftC, fqT, emp]
  · tsimp [σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, reg, WTape.words, clen]
    have e : 2 ^ kOf N - 1 + 2 = 2 ^ kOf N + 1 := by omega
    rw [e, show pieceOf N + (nextN N + 1) = pieceOf N + nextN N + 1 by ring]
    have f1 : 2 ^ kOf N - 1 ≤ 2 ^ kOf N := Nat.sub_le _ _
    omega

end IntegerMultBounds.Schoenhage
