import IntegerMultBounds.Schoenhage.LevelTape

/-! The up-sweep of one group on word tapes: the inverse transform of the
group's `K` products, the coefficient split, the two shifted sums and their
reductions modulo `2^N + 1`, and the final difference. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

namespace Tp
abbrev pN : Fin 𝕋 := 43
abbrev pNp : Fin 𝕋 := 44
abbrev pK : Fin 𝕋 := 45
abbrev pNK : Fin 𝕋 := 46
abbrev tOut : Fin 𝕋 := 47
abbrev sRA : Fin 𝕋 := 48
abbrev tIn : Fin 𝕋 := 50
abbrev tX : Fin 𝕋 := 51
abbrev tY : Fin 𝕋 := 52
end Tp

/-! ### Quiet scratch tapes -/

/-- The scratch tapes that are empty between operations. -/
def quiet : List (Fin 𝕋) :=
  [cT, tU, tV, tO1, tO2, tJ, tD, tD2, tE, tE2, tH, cH, cH2, tL, tS, cS, tT, sX, tC, sA, sO, sT1, sT2, tC2,
    cU, sRA]

/-- All scratch tapes are empty. -/
def Quiet (σ : Fin 𝕋 → WTape) : Prop := ∀ i ∈ quiet, σ i = emp

theorem Quiet.update {σ : Fin 𝕋 → WTape} (h : Quiet σ) (j : Fin 𝕋) (T : WTape) (hj : j ∉ quiet) :
    Quiet (Function.update σ j T) := by
  intro i hi
  have : i ≠ j := by rintro rfl; exact hj hi
  rw [Function.update_of_ne this]; exact h i hi

theorem Quiet.update_emp {σ : Fin 𝕋 → WTape} (h : Quiet σ) (j : Fin 𝕋) :
    Quiet (Function.update σ j emp) := by
  intro i hi
  by_cases e : i = j
  · subst e; simp
  · rw [Function.update_of_ne e]; exact h i hi

/-! ### The inverse transform and the coefficient split -/

/-- Depth registers for the inverse transform: `cS = ones k`, `k` ticks on `tL`, `cH = ones 1`, one tick on `tH`. -/
noncomputable def invSetup : Cmd 0 𝕋 :=
  .seq (op0 Rules.copy false pK cS (by decide)) <| .seq (rewind pK) <| .seq (rewind cS) <|
  .seq (op0 Rules.ticks false pK tL (by decide)) <| .seq (rewind pK) <| .seq (rewind tL) <|
  .seq (op0 Rules.copy false c1 cH (by decide)) <| .seq (rewind c1) <| .seq (rewind cH) <|
  .seq (op0 Rules.ticks false c1 tH (by decide)) <| .seq (rewind c1) (rewind tH)

theorem runs_invSetup {k : ℕ} (σ : Fin 𝕋 → WTape) (hK : σ pK = reg (ones k)) (h1 : σ c1 = reg [true])
    (hS : σ cS = emp) (hL : σ tL = emp) (hH : σ cH = emp) (htH : σ tH = emp) :
    Runs invSetup σ (· = Function.update (Function.update (Function.update (Function.update σ
        cS (reg (ones k))) tL ⟨[], List.replicate k []⟩) cH (reg (ones 1))) tH ⟨[], List.replicate 1 []⟩)
      (10 * k + 80) := by
  apply Runs.of_wp
  simp only [invSetup, WP, wp_op0, wp_rewind]
  tsimp [hK, h1, hS, hL, hH, htH, emp, reg, Rules.output_copy, Rules.output_ticks]
  have t1 := time_le Rules.copy (ones k) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.ticks (ones k) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t3 := time_le Rules.copy [true] (fun j => j.elim0) 0 (fun j => j.elim0)
  have t4 := time_le Rules.ticks [true] (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hK, h1, hS, hL, hH, htH, emp, reg, ones]
  · simp [clen] at t1 t2 t3 t4 ⊢; omega

/-- Drop the depth registers and load `cT = ones (N' - k)`. -/
noncomputable def invClean : Cmd 0 𝕋 :=
  .seq (clear cS) <| .seq (clear cH) <| .seq (clear tH) <| .seq (clear tL) <|
  .seq (op0 Rules.copy false pNK cT (by decide)) <| .seq (rewind pNK) (rewind cT)

/-- Drop the consumed data and the shift; rewind both coefficient streams. -/
noncomputable def coefClean : Cmd 0 𝕋 :=
  .seq (clear tD) <| .seq (clear cT) <| .seq (rewind tC) (rewind tC2)

/-- Inverse transform of the group on `tD`, then the coefficient split onto `tC` and `tC2`. -/
noncomputable def upA : Cmd 0 𝕋 := .seq invSetup <| .seq invLoop <| .seq invClean <| .seq coefLoop coefClean

/-- The descaled coefficients of a group. -/
def coefs (N k : ℕ) (P : List ℕ) : List ℕ := (invIter N k k P).map (descale N k)

theorem runs_upA {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) (P : List ℕ) (hP : P.length = 2 ^ k)
    (hPv : ∀ p ∈ P, p < 2 ^ N + 1) (σ : Fin 𝕋 → WTape) (hr : AluReady N σ) (hq : Quiet σ)
    (hHN : σ cHN = reg (ones (N / 2))) (hK : σ pK = reg (ones k)) (hNK : σ pNK = reg (ones (N - k)))
    (hH1 : σ cH1 = reg (hword N)) (hD : σ tD = ⟨[], rwds N P⟩) :
    Runs upA σ (· = Function.update (Function.update (Function.update σ tD emp)
        tC ⟨[], rwds N ((coefs N k P).map (posPart N))⟩)
        tC2 ⟨[], rwds N ((coefs N k P).map (negPart N))⟩)
      ((k + 2) * (5000 * (2 ^ k + 1) * (N + 2))) := by
  have q : ∀ i ∈ quiet, σ i = emp := hq
  have qcT := q cT (by decide); have qtU := q tU (by decide); have qtV := q tV (by decide)
  have qO1 := q tO1 (by decide); have qO2 := q tO2 (by decide); have qtJ := q tJ (by decide)
  have qD2 := q tD2 (by decide); have qtE := q tE (by decide); have qE2 := q tE2 (by decide)
  have qtH := q tH (by decide); have qcH := q cH (by decide); have qH2 := q cH2 (by decide)
  have qtL := q tL (by decide); have qtS := q tS (by decide); have qcS := q cS (by decide)
  have qtT := q tT (by decide); have qT1 := q sT1 (by decide); have qtC := q tC (by decide)
  have qC2 := q tC2 (by decide)
  unfold upA
  have s1 := runs_invSetup (k := k) σ hK hr.2.2.1 qcS qtL qcH qtH
  set σ₁ := Function.update (Function.update (Function.update (Function.update σ
        cS (reg (ones k))) tL ⟨[], List.replicate k []⟩) cH (reg (ones 1))) tH ⟨[], List.replicate 1 []⟩
  have hr₁ : AluReady N σ₁ :=
    (((hr.update cS _ (by decide)).update tL _ (by decide)).update cH _ (by decide)).update tH _ (by decide)
  have s2 := runs_invLoop (N := N) (k := k) hN k 1 P σ₁ [] le_rfl (by simp) hP hPv hr₁
    (by tsimp [σ₁, qcT]) (by tsimp [σ₁, qtT]) (by tsimp [σ₁, qtS]) (by tsimp [σ₁]) (by tsimp [σ₁])
    (by tsimp [σ₁, hD]) (by tsimp [σ₁, qtE]) (by tsimp [σ₁, qD2]) (by tsimp [σ₁, qE2]) (by tsimp [σ₁, hHN])
    (by tsimp [σ₁, qtU]) (by tsimp [σ₁, qtV]) (by tsimp [σ₁, qO1]) (by tsimp [σ₁, qO2]) (by tsimp [σ₁, qtJ])
    (by tsimp [σ₁]) (by tsimp [σ₁, qH2]) (by tsimp [σ₁])
  set ws := invIter N k k P with hwsd
  set σ₂ := Function.update (Function.update (Function.update (Function.update
          (Function.update σ₁ tD ⟨[], rwds N ws⟩) cS (reg (ones 0)))
          cH (reg (ones (1 * 2 ^ k)))) tH ⟨[], List.replicate (1 * 2 ^ k) []⟩)
          tL ⟨List.replicate k [] ++ [], []⟩
  have s3 : Runs invClean σ₂ (· = Function.update (Function.update σ tD ⟨[], rwds N ws⟩) cT
      (reg (ones (N - k)))) (6 * 2 ^ k + 2 * k + 4 * N + 40) := by
    apply Runs.of_wp
    simp only [invClean, WP, wp_op0, wp_rewind, wp_clear]
    tsimp [σ₂, σ₁, hNK, qcT, emp, reg, Rules.output_copy]
    have t1 := time_le Rules.copy (ones (N - k)) (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [σ₂, σ₁, hNK, qcT, qcS, qcH, qtH, qtL, emp, reg]
    · simp [clen, WTape.words] at t1 ⊢; omega
  set σ₃ := Function.update (Function.update σ tD ⟨[], rwds N ws⟩) cT (reg (ones (N - k)))
  have hws : ∀ w ∈ ws, w < 2 ^ N + 1 := invIter_lt N k k P hPv
  have s4 := runs_coefLoop (k := k) hN ws σ₃ [] [] [] hws (hr.update tD _ (by decide) |>.update cT _ (by decide))
    (by tsimp [σ₃]) (by tsimp [σ₃, hH1]) (by tsimp [σ₃, qT1]) (by tsimp [σ₃]) (by tsimp [σ₃, qtC, emp])
    (by tsimp [σ₃, qC2, emp])
  set σ₄ := Function.update (Function.update (Function.update σ₃
          tD ⟨(rwds N ws).reverse ++ [], []⟩)
          tC ⟨(rwds N ((ws.map (descale N k)).map (posPart N))).reverse ++ [], []⟩)
          tC2 ⟨(rwds N ((ws.map (descale N k)).map (negPart N))).reverse ++ [], []⟩
  have hwl : ws.length = 2 ^ k := invIter_length N k k P le_rfl hP
  have s5 : Runs coefClean σ₄ (· = Function.update (Function.update (Function.update σ tD emp)
        tC ⟨[], rwds N ((coefs N k P).map (posPart N))⟩)
        tC2 ⟨[], rwds N ((coefs N k P).map (negPart N))⟩) (8 * 2 ^ k * (N + 2) + 4 * N + 20) := by
    apply Runs.of_wp
    simp only [coefClean, WP, wp_rewind, wp_clear]
    tsimp [σ₄, σ₃]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [σ₄, σ₃, qcT, emp, coefs, hwsd]
    · simp only [WTape.words, reg, List.reverse_nil, List.nil_append, List.reverse_reverse, List.append_nil,
        clen_reverse, clen_rwds, List.length_map, hwl, clen_cons, clen_nil, length_ones]
      have : N - k ≤ N := Nat.sub_le N k
      have e : 8 * 2 ^ k * (N + 2) = 8 * (2 ^ k * (N + 2)) := by ring
      rw [e]
      generalize 2 ^ k * (N + 2) = X
      omega
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun σ' h => h) ?_
  simp only [hwl, hP]
  generalize 2 ^ k = K
  nlinarith [Nat.zero_le (k * K), Nat.zero_le (k * N), Nat.zero_le (K * N), Nat.zero_le (k * K * N)]

/-! ### Sum and reduce -/

/-- Load `cU` from `pN`. -/
noncomputable def loadN : Cmd 0 𝕋 := .seq (op0 Rules.copy false pN cU (by decide)) <| .seq (rewind pN) (rewind cU)

/-- Load `cU` from `pNp`. -/
noncomputable def loadNp : Cmd 0 𝕋 := .seq (op0 Rules.copy false pNp cU (by decide)) <| .seq (rewind pNp) (rewind cU)

theorem runs_loadN {N : ℕ} (σ : Fin 𝕋 → WTape) (hp : σ pN = reg (ones N)) (hU : σ cU = emp) :
    Runs loadN σ (· = Function.update σ cU (reg (ones N))) (3 * N + 20) := by
  apply Runs.of_wp
  simp only [loadN, WP, wp_op0, wp_rewind]
  tsimp [hp, hU, emp, reg, Rules.output_copy]
  have t1 := time_le Rules.copy (ones N) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hp, hU, emp, reg]
  · simp at t1 ⊢; omega

theorem runs_loadNp {N : ℕ} (σ : Fin 𝕋 → WTape) (hp : σ pNp = reg (ones N)) (hU : σ cU = emp) :
    Runs loadNp σ (· = Function.update σ cU (reg (ones N))) (3 * N + 20) := by
  apply Runs.of_wp
  simp only [loadNp, WP, wp_op0, wp_rewind]
  tsimp [hp, hU, emp, reg, Rules.output_copy]
  have t1 := time_le Rules.copy (ones N) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hp, hU, emp, reg]
  · simp at t1 ⊢; omega

/-- The unit's constants for the outer modulus `pN`. -/
noncomputable def toOuter : Cmd 0 𝕋 := .seq loadN <| .seq aluSet (clear cU)

/-- The unit's constants for the inner modulus `pNp`. -/
noncomputable def toInner : Cmd 0 𝕋 := .seq loadNp <| .seq aluSet (clear cU)

theorem AluReady.reset {N N1 : ℕ} {σ : Fin 𝕋 → WTape} (h : AluReady N1 σ) :
    AluReady N (Function.update (Function.update (Function.update σ
        cN (reg (ones N))) cW (reg (ones (N + 1)))) cF (reg (fword N))) := by
  obtain ⟨-, -, hc1, hX, hY, hO, hS1, hS2, hS3, hbX, hbY⟩ := h
  exact ⟨⟨by tsimp, by tsimp⟩, by tsimp, by tsimp [hc1], by tsimp [hX], by tsimp [hY], by tsimp [hO],
    by tsimp [hS1], by tsimp [hS2], by tsimp [hS3], by tsimp [hbX], by tsimp [hbY]⟩

theorem runs_toOuter {N N1 : ℕ} (hN : 0 < N) (σ : Fin 𝕋 → WTape) (hr : AluReady N1 σ)
    (hp : σ pN = reg (ones N)) (hU : σ cU = emp) (hT : σ sT1 = emp) :
    Runs toOuter σ (· = Function.update (Function.update (Function.update σ
        cN (reg (ones N))) cW (reg (ones (N + 1)))) cF (reg (fword N))) (40 * N + 30 * N1 + 300) := by
  obtain ⟨⟨hW, hF⟩, hcN, hc1, -⟩ := hr
  unfold toOuter
  have s1 := runs_loadN σ hp hU
  have s2 := runs_aluSet hN (Function.update σ cU (reg (ones N))) (by tsimp) (by tsimp [hc1]) (by tsimp [hT])
  refine (Runs.then s1 (Runs.then s2 (runs_clear cU _))).mono (fun σ' h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> tsimp [hU, emp]
  · tsimp [hW, hF, hcN, reg, WTape.words, clen, fword]
    omega

theorem runs_toInner {N N1 : ℕ} (hN : 0 < N) (σ : Fin 𝕋 → WTape) (hr : AluReady N1 σ)
    (hp : σ pNp = reg (ones N)) (hU : σ cU = emp) (hT : σ sT1 = emp) :
    Runs toInner σ (· = Function.update (Function.update (Function.update σ
        cN (reg (ones N))) cW (reg (ones (N + 1)))) cF (reg (fword N))) (40 * N + 30 * N1 + 300) := by
  obtain ⟨⟨hW, hF⟩, hcN, hc1, -⟩ := hr
  unfold toInner
  have s1 := runs_loadNp σ hp hU
  have s2 := runs_aluSet hN (Function.update σ cU (reg (ones N))) (by tsimp) (by tsimp [hc1]) (by tsimp [hT])
  refine (Runs.then s1 (Runs.then s2 (runs_clear cU _))).mono (fun σ' h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> tsimp [hU, emp]
  · tsimp [hW, hF, hcN, reg, WTape.words, clen, fword]
    omega

/-- The shifted sum of the words on `tC`, reduced modulo the outer `2^N + 1`, into `aO`. -/
noncomputable def sumRed : Cmd 0 𝕋 := .seq winSum <| .seq (clear tC) <| .seq toOuter redOp

theorem runs_sumRed {N N1 Np M : ℕ} (hN : 0 < N) (hM : 1 ≤ M) (hMW : M ≤ Np + 2) (cs : List ℕ)
    (hcs : ∀ c ∈ cs, c < 2 ^ (Np + 1)) (hA : wsum M cs < 2 ^ (2 * N)) (σ : Fin 𝕋 → WTape)
    (hr : AluReady N1 σ) (hC : σ tC = ⟨[], rwds Np cs⟩) (hsA : σ sA = emp) (hsO : σ sO = emp)
    (h1 : σ sT1 = emp) (h2 : σ sT2 = emp) (hU : σ cU = emp) (hMr : σ cM = reg (ones M))
    (hW : σ cWA = reg (ones (Np + 2))) (hp : σ pN = reg (ones N)) :
    Runs sumRed σ (· = Function.update (Function.update (Function.update (Function.update
        (Function.update σ tC emp) cN (reg (ones N))) cW (reg (ones (N + 1)))) cF (reg (fword N)))
        aO (reg (rwd N (red N (wsum M cs)))))
      ((cs.length + 1) * (60 * Np + 200) + 12 * M * cs.length + 200 * N + 30 * N1 + 1000) := by
  unfold sumRed
  obtain ⟨z, hz, hzl, s1⟩ := runs_winSum (Wc := Np + 1) hM le_rfl hMW cs hcs σ hsA (by rw [hC]; rfl)
    hsO h1 h2 hMr hW
  set σ₁ := Function.update (Function.update σ tC ⟨(cs.map (bits (Np + 1))).reverse ++ [], []⟩) sO ⟨[z], []⟩
  have s2 := runs_clear (a := 0) tC σ₁
  set σ₂ := Function.update σ₁ tC ⟨[], []⟩
  have hr₂ : AluReady N1 σ₂ := (hr.update tC _ (by decide) |>.update sO _ (by decide)).update tC _ (by decide)
  have s3 := runs_toOuter hN σ₂ hr₂ (by tsimp [σ₂, σ₁, hp]) (by tsimp [σ₂, σ₁, hU]) (by tsimp [σ₂, σ₁, h1])
  set σ₃ := Function.update (Function.update (Function.update σ₂
        cN (reg (ones N))) cW (reg (ones (N + 1)))) cF (reg (fword N))
  have s4 := runs_redOp hN σ₃ hr₂.reset (z := z) (by rw [hz]; exact hA) (by tsimp [σ₃, σ₂, σ₁])
    (by tsimp [σ₃, σ₂, σ₁, h1]) (by tsimp [σ₃, σ₂, σ₁, h2])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun σ' h => ?_) ?_
  · rw [h, hz]
    funext i; fin_cases i <;> tsimp [σ₃, σ₂, σ₁, hsO, emp]
  · tsimp [σ₁, WTape.words, clen_reverse, hzl]
    have cl : clen (cs.map (bits (Np + 1))) = cs.length * (Np + 2) := by
      exact clen_rwds Np cs
    rw [cl]
    nlinarith [Nat.zero_le cs.length, Nat.zero_le Np, Nat.zero_le (M * cs.length)]

/-! ### One group -/

/-- Park the first reduction and make the negative stream current. -/
noncomputable def upMid : Cmd 0 𝕋 :=
  .seq (regMove aO sRA (by decide)) <| .seq (appendAll tC2 tC (by decide)) <| .seq (rewind tC) (clear tC2)

/-- The difference of the two reductions, appended to `tOut`; the unit back to the inner modulus. -/
noncomputable def upEnd : Cmd 0 𝕋 :=
  .seq (regMove aO aY (by decide)) <| .seq (regMove sRA aX (by decide)) <| .seq subMod <|
  .seq (regOut aO tOut (by decide)) toInner

/-- The up-sweep of one group. -/
noncomputable def upGroup : Cmd 0 𝕋 := .seq upA <| .seq sumRed <| .seq upMid <| .seq sumRed upEnd

/-- The registers of a level with outer size `N`, inner size `Np`, `2^k` pieces of `M` bits. -/
def LevelRegs (N Np k M : ℕ) (σ : Fin 𝕋 → WTape) : Prop :=
  AluReady Np σ ∧ Quiet σ ∧ σ cHN = reg (ones (Np / 2)) ∧ σ pK = reg (ones k) ∧
    σ pNK = reg (ones (Np - k)) ∧ σ cH1 = reg (hword Np) ∧ σ cM = reg (ones M) ∧
    σ cWA = reg (ones (Np + 2)) ∧ σ pN = reg (ones N) ∧ σ pNp = reg (ones Np)

theorem runs_upGroup {N Np k M : ℕ} (hN : 0 < N) (hNp : 0 < Np) (hk : k ≤ Np) (hM : 1 ≤ M)
    (hMW : M ≤ Np + 2) (P : List ℕ) (hP : P.length = 2 ^ k) (hPv : ∀ p ∈ P, p < 2 ^ Np + 1)
    (hA : wsum M ((coefs Np k P).map (posPart Np)) < 2 ^ (2 * N))
    (hB : wsum M ((coefs Np k P).map (negPart Np)) < 2 ^ (2 * N))
    (σ : Fin 𝕋 → WTape) (hL : LevelRegs N Np k M σ) (hD : σ tD = ⟨[], rwds Np P⟩)
    {O : List (List Bool)} (hO : σ tOut = ⟨O, []⟩) :
    Runs upGroup σ (· = Function.update (Function.update σ tD emp) tOut
        ⟨rwd N ((red N (wsum M ((coefs Np k P).map (posPart Np))) + (2 ^ N + 1) -
          red N (wsum M ((coefs Np k P).map (negPart Np)))) % (2 ^ N + 1)) :: O, []⟩)
      ((k + 3) * (5000 * (2 ^ k + 1) * (Np + 2)) + 24 * M * 2 ^ k + 1000 * N + 5000) := by
  obtain ⟨hr, hq, hHN, hK, hNK, hH1, hMr, hW, hpN, hpNp⟩ := hL
  have q : ∀ i ∈ quiet, σ i = emp := hq
  have qsA := q sA (by decide); have qsO := q sO (by decide); have qT1 := q sT1 (by decide)
  have qT2 := q sT2 (by decide); have qcU := q cU (by decide); have qRA := q sRA (by decide)
  have qtC := q tC (by decide); have qC2 := q tC2 (by decide)
  unfold upGroup
  set cP := (coefs Np k P).map (posPart Np)
  set cN' := (coefs Np k P).map (negPart Np)
  have hcl : (coefs Np k P).length = 2 ^ k := by
    simp [coefs, invIter_length Np k k P le_rfl hP]
  have hPl : ∀ c ∈ cP, c < 2 ^ (Np + 1) := fun c hc => by
    simp only [cP, List.mem_map] at hc; obtain ⟨d, -, rfl⟩ := hc
    exact (posPart_lt hNp).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hNl : ∀ c ∈ cN', c < 2 ^ (Np + 1) := fun c hc => by
    simp only [cN', List.mem_map] at hc; obtain ⟨d, -, rfl⟩ := hc
    exact (negPart_lt hNp).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have s1 := runs_upA hNp hk P hP hPv σ hr hq hHN hK hNK hH1 hD
  set σ₁ := Function.update (Function.update (Function.update σ tD emp) tC ⟨[], rwds Np cP⟩)
    tC2 ⟨[], rwds Np cN'⟩
  have hr₁ : AluReady Np σ₁ :=
    ((hr.update tD _ (by decide)).update tC _ (by decide)).update tC2 _ (by decide)
  have s2 := runs_sumRed hN hM hMW cP hPl hA σ₁ hr₁ (by tsimp [σ₁]) (by tsimp [σ₁, qsA]) (by tsimp [σ₁, qsO])
    (by tsimp [σ₁, qT1]) (by tsimp [σ₁, qT2]) (by tsimp [σ₁, qcU]) (by tsimp [σ₁, hMr]) (by tsimp [σ₁, hW])
    (by tsimp [σ₁, hpN])
  set σ₂ := Function.update (Function.update (Function.update (Function.update
        (Function.update σ₁ tC emp) cN (reg (ones N))) cW (reg (ones (N + 1)))) cF (reg (fword N)))
        aO (reg (rwd N (red N (wsum M cP))))
  have s3 : Runs upMid σ₂ (· = Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update σ tD emp) tC2 emp) cN (reg (ones N)))
        cW (reg (ones (N + 1)))) cF (reg (fword N))) sRA (reg (rwd N (red N (wsum M cP)))))
        tC ⟨[], rwds Np cN'⟩) (2 ^ k * (4 * Np + 20) + 4 * N + 40) := by
    unfold upMid
    have m1 := runs_regMove (a := 0) (r := aO) (r' := sRA) (by decide) σ₂ (w := rwd N (red N (wsum M cP)))
      (by tsimp [σ₂]) (by tsimp [σ₂, σ₁, qRA])
    have m2 := runs_appendAll (a := 0) (s := tC2) (d := tC) (by decide) (Np + 1) (rwds Np cN')
      (Function.update (Function.update σ₂ aO emp) sRA (reg (rwd N (red N (wsum M cP))))) [] []
      (by tsimp [σ₂, σ₁]) (by tsimp [σ₂, σ₁, emp]) (rwds_length_le Np cN')
    refine (Runs.then m1 (Runs.then m2 (Runs.then (runs_rewind tC _) (runs_clear tC2 _)))).mono
      (fun σ' h => ?_) ?_
    · rw [h]; funext i; fin_cases i <;> tsimp [σ₂, σ₁, hr.2.2.2.2.2.1, emp]
    · tsimp [WTape.words, clen_reverse, clen_rwds, length_rwds, rwd_length, cN']
      rw [hcl]; nlinarith
  set σ₃ := Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update σ tD emp) tC2 emp) cN (reg (ones N)))
        cW (reg (ones (N + 1)))) cF (reg (fword N))) sRA (reg (rwd N (red N (wsum M cP)))))
        tC ⟨[], rwds Np cN'⟩
  obtain ⟨⟨hrW, hrF⟩, hrN, hc1, hX, hY, hAO, hS1, hS2, hS3, hbX, hbY⟩ := hr
  have hr₃ : AluReady N σ₃ := ⟨⟨by tsimp [σ₃], by tsimp [σ₃]⟩, by tsimp [σ₃], by tsimp [σ₃, hc1],
    by tsimp [σ₃, hX], by tsimp [σ₃, hY], by tsimp [σ₃, hAO], by tsimp [σ₃, hS1], by tsimp [σ₃, hS2],
    by tsimp [σ₃, hS3], by tsimp [σ₃, hbX], by tsimp [σ₃, hbY]⟩
  have s4 := runs_sumRed hN hM hMW cN' hNl hB σ₃ hr₃ (by tsimp [σ₃]) (by tsimp [σ₃, qsA]) (by tsimp [σ₃, qsO])
    (by tsimp [σ₃, qT1]) (by tsimp [σ₃, qT2]) (by tsimp [σ₃, qcU]) (by tsimp [σ₃, hMr]) (by tsimp [σ₃, hW])
    (by tsimp [σ₃, hpN])
  set σ₄ := Function.update (Function.update (Function.update (Function.update
        (Function.update σ₃ tC emp) cN (reg (ones N))) cW (reg (ones (N + 1)))) cF (reg (fword N)))
        aO (reg (rwd N (red N (wsum M cN'))))
  have hlt : ∀ Z, red N Z < 2 ^ N + 1 := fun Z => Nat.mod_lt _ (Fm_pos N)
  have s5 : Runs upEnd σ₄ (· = Function.update (Function.update σ tD emp) tOut
        ⟨rwd N ((red N (wsum M cP) + (2 ^ N + 1) - red N (wsum M cN')) % (2 ^ N + 1)) :: O, []⟩)
      (300 * N + 50 * Np + 1000) := by
    unfold upEnd
    have e1 := runs_regMove (a := 0) (r := aO) (r' := aY) (by decide) σ₄ (w := rwd N (red N (wsum M cN')))
      (by tsimp [σ₄]) (by tsimp [σ₄, σ₃, hY])
    set τ₁ := Function.update (Function.update σ₄ aO emp) aY (reg (rwd N (red N (wsum M cN'))))
    have e2 := runs_regMove (a := 0) (r := sRA) (r' := aX) (by decide) τ₁ (w := rwd N (red N (wsum M cP)))
      (by tsimp [τ₁, σ₄, σ₃]) (by tsimp [τ₁, σ₄, σ₃, hX])
    set τ₂ := Function.update (Function.update τ₁ sRA emp) aX (reg (rwd N (red N (wsum M cP))))
    have e3 := runs_subMod hN τ₂ ⟨by tsimp [τ₂, τ₁, σ₄], by tsimp [τ₂, τ₁, σ₄]⟩
      (x := rwd N (red N (wsum M cP))) (y := rwd N (red N (wsum M cN'))) (by tsimp [τ₂])
      (by tsimp [τ₂, τ₁]) (rwd_length _ _) (rwd_length _ _) (by rw [bval_rwd (hlt _)]; exact hlt _)
      (by rw [bval_rwd (hlt _)]; exact hlt _) (by tsimp [τ₂, τ₁, σ₄]) (by tsimp [τ₂, τ₁, σ₄, σ₃, hS1])
      (by tsimp [τ₂, τ₁, σ₄, σ₃, hS2])
    set τ₃ := Function.update (Function.update (Function.update τ₂ aX emp) aY emp) aO
      (reg (subRes N (rwd N (red N (wsum M cP))) (rwd N (red N (wsum M cN')))))
    have e4 := runs_regOut (a := 0) (r := aO) (d := tOut) (by decide) τ₃ (M := O)
      (w := subRes N (rwd N (red N (wsum M cP))) (rwd N (red N (wsum M cN')))) (by tsimp [τ₃])
      (by tsimp [τ₃, τ₂, τ₁, σ₄, σ₃, σ₂, σ₁, hO])
    set τ₄ := Function.update (Function.update τ₃ aO emp) tOut
      ⟨subRes N (rwd N (red N (wsum M cP))) (rwd N (red N (wsum M cN'))) :: O, []⟩
    have hr₄ : AluReady N τ₄ := ⟨⟨by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄], by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄]⟩,
      by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄], by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄, σ₃, hc1], by tsimp [τ₄, τ₃],
      by tsimp [τ₄, τ₃], by tsimp [τ₄], by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄, σ₃, hS1],
      by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄, σ₃, hS2], by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄, σ₃, hS3],
      by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄, σ₃, hbX], by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄, σ₃, hbY]⟩
    have e5 := runs_toInner hNp τ₄ hr₄ (by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄, σ₃, hpNp])
      (by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄, σ₃, qcU]) (by tsimp [τ₄, τ₃, τ₂, τ₁, σ₄, σ₃, qT1])
    refine (Runs.then e1 (Runs.then e2 (Runs.then e3 (Runs.then e4 e5)))).mono (fun σ' h => ?_) ?_
    · rw [h]
      have ev : subRes N (rwd N (red N (wsum M cP))) (rwd N (red N (wsum M cN'))) =
          rwd N ((red N (wsum M cP) + (2 ^ N + 1) - red N (wsum M cN')) % (2 ^ N + 1)) := by
        rw [subRes, bval_rwd (hlt _), bval_rwd (hlt _)]; rfl
      funext i; fin_cases i <;> tsimp [τ₄, τ₃, τ₂, τ₁, σ₄, σ₃, σ₂, σ₁, ev, hrW, hrF, hrN, hX, hY, hAO, qRA,
        qtC, qC2, qcU, emp]
    · simp only [rwd_length, subRes, length_bits]; omega
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun σ' h => h) ?_
  have l1 : cP.length = 2 ^ k := by simp [cP, hcl]
  have l2 : cN'.length = 2 ^ k := by simp [cN', hcl]
  rw [l1, l2]
  have e : (k + 3) * (5000 * (2 ^ k + 1) * (Np + 2)) =
      (k + 2) * (5000 * (2 ^ k + 1) * (Np + 2)) + 5000 * (2 ^ k + 1) * (Np + 2) := by ring
  rw [e]
  generalize (k + 2) * (5000 * (2 ^ k + 1) * (Np + 2)) = X
  generalize 2 ^ k = K
  nlinarith [Nat.zero_le (K * Np), Nat.zero_le (M * K)]

theorem pieceOf_pos {N : ℕ} (hN : N0 ≤ N) (hk : 2 ^ kOf N ∣ N) : 1 ≤ pieceOf N := by
  have hs := Schedule.split_exact hk
  rcases Nat.eq_zero_or_pos (pieceOf N) with h | h
  · rw [h, mul_zero] at hs
    have : 0 < N := lt_of_lt_of_le (by rw [Schedule.N0_eq]; exact Nat.two_pow_pos _) hN
    omega
  · exact h

/-- The group up-sweep computes the level's output. -/
theorem runs_upGroup_level {N : ℕ} (hN0 : N0 ≤ N) (hk : 2 ^ kOf N ∣ N) (P : List ℕ)
    (hP : P.length = 2 ^ kOf N) (hPv : ∀ p ∈ P, p < Fm (nextN N)) (σ : Fin 𝕋 → WTape)
    (hL : LevelRegs N (nextN N) (kOf N) (pieceOf N) σ) (hD : σ tD = ⟨[], rwds (nextN N) P⟩)
    {O : List (List Bool)} (hO : σ tOut = ⟨O, []⟩) :
    Runs upGroup σ (· = Function.update (Function.update σ tD emp) tOut ⟨rwd N (levelOut N P) :: O, []⟩)
      ((kOf N + 3) * (5000 * (2 ^ kOf N + 1) * (nextN N + 2)) + 24 * pieceOf N * 2 ^ kOf N +
        1000 * N + 5000) := by
  have hnf := Schedule.next_facts hN0
  have hN : 0 < N := by omega
  have hM := pieceOf_pos hN0 hk
  have hws := invIter_length (nextN N) (kOf N) (kOf N) P le_rfl hP
  have hdl : (coefs (nextN N) (kOf N) P).length = 2 ^ kOf N := by simp [coefs, hws]
  have hA := wsum_parts_lt hN0 _ hdl (posPart (nextN N)) (fun _ => posPart_lt (by omega)) hk
  have hB := wsum_parts_lt hN0 _ hdl (negPart (nextN N)) (fun _ => negPart_lt (by omega)) hk
  have r := runs_upGroup hN (by omega) (by omega) hM (by omega) P hP hPv hA hB σ hL hD hO
  refine r.mono (fun σ' h => ?_) le_rfl
  rw [h]
  have e := levelTape_eq hN0 hk (invIter (nextN N) (kOf N) (kOf N) P) hws
  unfold levelTape at e
  simp only at e
  have e2 : levelOut N P = recomb N (pieceOf N)
      (((invIter (nextN N) (kOf N) (kOf N) P).map (descale (nextN N) (kOf N))).map (liftN (nextN N))) := by
    rw [levelOut, List.map_map]; rfl
  rw [e2, ← e]
  rfl

end IntegerMultBounds.Schoenhage
