import IntegerMultBounds.Schoenhage.Butterfly
import IntegerMultBounds.Schoenhage.IterCorrect

/-! Transform layers on word tapes. The pair loop runs the butterfly over the
two half-block tapes; the block loop splits the data into blocks, runs the
pair loop with the block's shift, collects sums then differences, and writes
the children's shifts; the layer replaces the data and shift tapes by the new
ones. The words are canonical residues `rwd N r`, and the results are the
layer functions of `Iter.lean`. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp

namespace Tp
abbrev tJ : Fin 𝕋 := 18
abbrev tD : Fin 𝕋 := 19
abbrev tD2 : Fin 𝕋 := 20
abbrev tE : Fin 𝕋 := 21
abbrev tE2 : Fin 𝕋 := 22
abbrev tH : Fin 𝕋 := 23
abbrev cH : Fin 𝕋 := 24
abbrev cHN : Fin 𝕋 := 25
abbrev cH2 : Fin 𝕋 := 26
abbrev tL : Fin 𝕋 := 27
end Tp

/-- Residue words. -/
def rwds (N : ℕ) (l : List ℕ) : List (List Bool) := l.map (rwd N)

theorem AluReady.update {N : ℕ} {σ : Fin 𝕋 → WTape} (h : AluReady N σ) (i : Fin 𝕋) (T : WTape)
    (hi : i ∉ [cW, cF, cN, c1, aX, aY, aO, aS1, aS2, aS3, bX, bY]) :
    AluReady N (Function.update σ i T) := by
  obtain ⟨⟨hW, hF⟩, hcN, hc1, hX, hY, hO, hS1, hS2, hS3, hbX, hbY⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hi
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Function.update_apply, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5,
      Ne.symm n6, Ne.symm n7, Ne.symm n8, Ne.symm n9, Ne.symm n10, Ne.symm n11, Ne.symm n12, *]

/-! ### The forward pair loop -/

/-- Butterflies over the half-block tapes. -/
noncomputable def pairF : Cmd 0 𝕋 := .loop tU bflyF

set_option maxHeartbeats 1000000 in
theorem runs_pairF {N t : ℕ} (hN : 0 < N) (htN : t ≤ N) :
    ∀ (U V : List ℕ) (σ : Fin 𝕋 → WTape) (LU LV RV M1 M2 : List (List Bool)),
      AluReady N σ → σ cT = reg (ones t) → U.length = V.length →
      (∀ u ∈ U, u < 2 ^ N + 1) → (∀ v ∈ V, v < 2 ^ N + 1) →
      σ tU = ⟨LU, rwds N U⟩ → σ tV = ⟨LV, rwds N V ++ RV⟩ → σ tO1 = ⟨M1, []⟩ → σ tO2 = ⟨M2, []⟩ →
      Runs pairF σ (· = Function.update (Function.update (Function.update (Function.update σ
          tU ⟨(rwds N U).reverse ++ LU, []⟩) tV ⟨(rwds N V).reverse ++ LV, RV⟩)
          tO1 ⟨(rwds N (bfS N t U V)).reverse ++ M1, []⟩)
          tO2 ⟨(rwds N (bfD N t U V)).reverse ++ M2, []⟩)
        (U.length * (1000 * N + 2002))
  | [], V, σ, LU, LV, RV, M1, M2, hr, hcT, hl, _, _, hU, hV, h1, h2 => by
    have : V = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    subst this
    refine (Runs.loop_done (by simp [hU, rwds]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hU, hV, h1, h2, rwds, bfS, bfD]
  | u :: U, v :: V, σ, LU, LV, RV, M1, M2, hr, hcT, hl, hUv, hVv, hU, hV, h1, h2 => by
    have hu := hUv u (by simp)
    have hv := hVv v (by simp)
    have b := runs_bflyF hN htN σ hr hcT hu hv (LU := LU) (RU := rwds N U) (LV := LV)
      (RV := rwds N V ++ RV) (M1 := M1) (M2 := M2) (by simpa [rwds] using hU)
      (by simpa [rwds] using hV) h1 h2
    set σ₁ := Function.update (Function.update (Function.update (Function.update σ
        tU ⟨rwd N u :: LU, rwds N U⟩) tV ⟨rwd N v :: LV, rwds N V ++ RV⟩)
        tO1 ⟨rwd N ((u + 2 ^ t * v % (2 ^ N + 1)) % (2 ^ N + 1)) :: M1, []⟩)
        tO2 ⟨rwd N ((u + (2 ^ N + 1) - 2 ^ t * v % (2 ^ N + 1)) % (2 ^ N + 1)) :: M2, []⟩ with hσ₁
    have hr₁ : AluReady N σ₁ :=
      (((hr.update tU _ (by decide)).update tV _ (by decide)).update tO1 _ (by decide)).update
        tO2 _ (by decide)
    have ih := runs_pairF hN htN U V σ₁ (rwd N u :: LU) (rwd N v :: LV) RV
      (rwd N ((u + 2 ^ t * v % (2 ^ N + 1)) % (2 ^ N + 1)) :: M1)
      (rwd N ((u + (2 ^ N + 1) - 2 ^ t * v % (2 ^ N + 1)) % (2 ^ N + 1)) :: M2)
      hr₁ (by tsimp [σ₁, hcT]) (by simpa using hl)
      (fun x hx => hUv x (by simp [hx])) (fun x hx => hVv x (by simp [hx]))
      (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁])
    refine (Runs.loop_step (by simp [hU, rwds]) (b.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      funext i; fin_cases i <;> tsimp [σ₁, rwds, bfS, bfD, Fm]
    · simp only [List.length_cons]; nlinarith
  | u :: U, [], σ, _, _, _, _, _, _, _, hl, _, _, _, _, _, _ => by simp at hl

/-! ### Block fragments -/

theorem ones_append (m n : ℕ) : ones m ++ ones n = ones (m + n) := by
  unfold ones; rw [List.replicate_add]

/-- Split the current block of `tD` into the half-block tapes. -/
noncomputable def splitBlock : Cmd 0 𝕋 :=
  .seq (moveN tH tD tU tJ (by decide) (by decide)) <| .seq (rewind tH) <|
  .seq (moveN tH tD tV tJ (by decide) (by decide)) <| .seq (rewind tH) <|
  .seq (rewind tU) (rewind tV)

theorem runs_splitBlock (σ : Fin 𝕋 → WTape) (W : ℕ) {Tk U V Dl Dr : List (List Bool)}
    (hTk : ∀ w ∈ Tk, w.length ≤ W) (hU : ∀ w ∈ U, w.length ≤ W) (hV : ∀ w ∈ V, w.length ≤ W)
    (hl1 : U.length = Tk.length) (hl2 : V.length = Tk.length)
    (hH : σ tH = ⟨[], Tk⟩) (hD : σ tD = ⟨Dl, U ++ V ++ Dr⟩) (htU : σ tU = emp) (htV : σ tV = emp)
    (hJ : σ tJ = emp) :
    Runs splitBlock σ (· = Function.update (Function.update (Function.update σ
        tD ⟨V.reverse ++ U.reverse ++ Dl, Dr⟩) tU ⟨[], U⟩) tV ⟨[], V⟩)
      (Tk.length * (6 * W + 40) + 4 * clen Tk + 10 * W + 50) := by
  unfold splitBlock
  refine (Runs.then (runs_moveN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      W Tk σ [] Dl U (V ++ Dr) [] hH (by rw [hD, List.append_assoc]) hl1 (by simpa [emp] using htU)
      (by simp [hJ, emp]) hU hTk) <|
    Runs.then (runs_rewind tH _) <|
    Runs.then (runs_moveN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      W Tk _ [] (U.reverse ++ Dl) V Dr [] (by tsimp) (by tsimp) hl2 (by tsimp [htV, emp])
      (by tsimp [hJ, emp]) hV hTk) <|
    Runs.then (runs_rewind tH _) <| Runs.then (runs_rewind tU _) (runs_rewind tV _)).mono ?_ ?_
  · intro σ' h; rw [h]
    funext i; fin_cases i <;> tsimp [hH, emp]
  · tsimp [clen_reverse]
    have h1 : clen U ≤ Tk.length * (W + 1) := by
      rw [← hl1]; unfold clen
      calc (U.map fun w => w.length + 1).sum ≤ (U.map fun _ => W + 1).sum :=
            List.sum_le_sum (fun w hw => by simpa using hU w hw)
        _ = U.length * (W + 1) := by simp
    have h2 : clen V ≤ Tk.length * (W + 1) := by
      rw [← hl2]; unfold clen
      calc (V.map fun w => w.length + 1).sum ≤ (V.map fun _ => W + 1).sum :=
            List.sum_le_sum (fun w hw => by simpa using hV w hw)
        _ = V.length * (W + 1) := by simp
    nlinarith

/-- Append the sums and then the differences to `tD2`; empty the block tapes. -/
noncomputable def collect : Cmd 0 𝕋 :=
  .seq (rewind tO1) <| .seq (appendAll tO1 tD2 (by decide)) <|
  .seq (rewind tO2) <| .seq (appendAll tO2 tD2 (by decide)) <|
  .seq (clear tO1) <| .seq (clear tO2) <| .seq (clear tU) (clear tV)

theorem clen_le {L : List (List Bool)} {W : ℕ} (h : ∀ w ∈ L, w.length ≤ W) : clen L ≤ L.length * (W + 1) := by
  unfold clen
  calc (L.map fun w => w.length + 1).sum ≤ (L.map fun _ => W + 1).sum :=
        List.sum_le_sum (fun w hw => by simpa using h w hw)
    _ = L.length * (W + 1) := by simp

theorem runs_collect (σ : Fin 𝕋 → WTape) (W : ℕ) {S Df M LU LV : List (List Bool)}
    (hS : ∀ w ∈ S, w.length ≤ W) (hDf : ∀ w ∈ Df, w.length ≤ W)
    (hLU : ∀ w ∈ LU, w.length ≤ W) (hLV : ∀ w ∈ LV, w.length ≤ W)
    (h1 : σ tO1 = ⟨S.reverse, []⟩) (h2 : σ tO2 = ⟨Df.reverse, []⟩) (hd : σ tD2 = ⟨M, []⟩)
    (hU : σ tU = ⟨LU, []⟩) (hV : σ tV = ⟨LV, []⟩) :
    Runs collect σ (· = Function.update (Function.update (Function.update (Function.update
        (Function.update σ tD2 ⟨Df.reverse ++ S.reverse ++ M, []⟩) tO1 emp) tO2 emp) tU emp) tV emp)
      ((S.length + Df.length + LU.length + LV.length + 5) * (4 * W + 20)) := by
  unfold collect
  refine (Runs.then (runs_rewind tO1 _) <|
    Runs.then (runs_appendAll (s := tO1) (d := tD2) (by decide) W S _ [] M (by tsimp [h1])
      (by tsimp [hd]) hS) <|
    Runs.then (runs_rewind tO2 _) <|
    Runs.then (runs_appendAll (s := tO2) (d := tD2) (by decide) W Df _ [] (S.reverse ++ M)
      (by tsimp [h2]) (by tsimp) hDf) <|
    Runs.then (runs_clear tO1 _) <| Runs.then (runs_clear tO2 _) <|
    Runs.then (runs_clear tU _) (runs_clear tV _)).mono ?_ ?_
  · intro σ' h; rw [h]
    funext i; fin_cases i <;> tsimp [emp]
  · have c1 := clen_le hS
    have c2 := clen_le hDf
    have c3 := clen_le hLU
    have c4 := clen_le hLV
    tsimp [h1, h2, hU, hV, WTape.words, clen_reverse, clen_append]
    nlinarith

/-- The children's shifts `t / 2` and `t / 2 + N / 2` from the register `cT`. -/
noncomputable def kidsShift : Cmd 0 𝕋 :=
  .seq (op0 Rules.half false cT tE2 (by decide)) <| .seq (rewind cT) <|
  .seq (op0 Rules.half false cT tE2 (by decide)) <|
  .seq (op0 Rules.copy true cHN tE2 (by decide)) <|
  .seq (rewind cT) <| .seq (rewind cHN) (clear cT)

theorem runs_kidsShift {N t : ℕ} (σ : Fin 𝕋 → WTape) {ME : List (List Bool)}
    (hT : σ cT = reg (ones t)) (hN : σ cHN = reg (ones (N / 2))) (hE : σ tE2 = ⟨ME, []⟩) :
    Runs kidsShift σ (· = Function.update (Function.update σ tE2
        ⟨ones (t / 2 + N / 2) :: ones (t / 2) :: ME, []⟩) cT emp) (6 * t + 2 * N + 60) := by
  apply Runs.of_wp
  simp only [kidsShift, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hT, hN, hE, emp, reg, Rules.output_half_ones, Rules.output_copy]
  have t1 := time_le Rules.half (ones t) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.copy (ones (N / 2)) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hT, hN, hE, emp, reg, ones_append]
  · simp [clen, WTape.words] at t1 t2 ⊢; omega

/-- One block of a forward layer. -/
noncomputable def blockF : Cmd 0 𝕋 :=
  .seq splitBlock <| .seq (regIn tE cT (by decide)) <| .seq pairF <| .seq collect kidsShift

theorem rwds_length_le (N : ℕ) (l : List ℕ) : ∀ w ∈ rwds N l, w.length ≤ N + 1 := by
  intro w hw; simp only [rwds, List.mem_map] at hw; obtain ⟨r, -, rfl⟩ := hw; simp [rwd_length]

theorem length_rwds (N : ℕ) (l : List ℕ) : (rwds N l).length = l.length := by simp [rwds]

theorem bfS_length (N t : ℕ) (U V : List ℕ) (h : U.length = V.length) : (bfS N t U V).length = U.length := by
  simp [bfS, h]

theorem bfD_length (N t : ℕ) (U V : List ℕ) (h : U.length = V.length) : (bfD N t U V).length = U.length := by
  simp [bfD, h]

theorem runs_blockF {N t : ℕ} (hN : 0 < N) (htN : t ≤ N) (σ : Fin 𝕋 → WTape) (hr : AluReady N σ)
    (hcT : σ cT = emp) {Tk : List (List Bool)} (hTk : ∀ w ∈ Tk, w.length ≤ N + 1)
    {U V : List ℕ} (hlU : U.length = Tk.length) (hlV : V.length = Tk.length)
    (hUv : ∀ u ∈ U, u < 2 ^ N + 1) (hVv : ∀ v ∈ V, v < 2 ^ N + 1)
    {Dl Dr El Er M ME : List (List Bool)}
    (hH : σ tH = ⟨[], Tk⟩) (hD : σ tD = ⟨Dl, rwds N U ++ rwds N V ++ Dr⟩)
    (hE : σ tE = ⟨El, ones t :: Er⟩) (hD2 : σ tD2 = ⟨M, []⟩) (hE2 : σ tE2 = ⟨ME, []⟩)
    (hHN : σ cHN = reg (ones (N / 2))) (htU : σ tU = emp) (htV : σ tV = emp)
    (h1 : σ tO1 = emp) (h2 : σ tO2 = emp) (hJ : σ tJ = emp) :
    Runs blockF σ (· = Function.update (Function.update (Function.update (Function.update σ
        tD ⟨(rwds N V).reverse ++ (rwds N U).reverse ++ Dl, Dr⟩) tE ⟨ones t :: El, Er⟩)
        tD2 ⟨(rwds N (bfD N t U V)).reverse ++ (rwds N (bfS N t U V)).reverse ++ M, []⟩)
        tE2 ⟨ones (t / 2 + N / 2) :: ones (t / 2) :: ME, []⟩)
      ((Tk.length + 1) * (1100 * N + 3000)) := by
  unfold blockF
  have hWU := rwds_length_le N U
  have hWV := rwds_length_le N V
  refine (Runs.then (runs_splitBlock σ (N + 1) hTk hWU hWV (by rw [length_rwds, hlU])
      (by rw [length_rwds, hlV]) hH hD htU htV hJ) <|
    Runs.then (runs_regIn (s := tE) (r := cT) (by decide) _ (L := El) (R := Er) (w := ones t)
      (by tsimp [hE]) (by tsimp [hcT])) <|
    Runs.then (runs_pairF hN htN U V _ [] [] [] [] []
      (((((hr.update tD _ (by decide)).update tU _ (by decide)).update tV _ (by decide)).update
        tE _ (by decide)).update cT _ (by decide)) (by tsimp) (by rw [hlU, hlV]) hUv hVv
      (by tsimp) (by tsimp) (by tsimp [h1, emp]) (by tsimp [h2, emp])) <|
    Runs.then (runs_collect _ (N + 1) (S := rwds N (bfS N t U V)) (Df := rwds N (bfD N t U V)) (M := M)
      (rwds_length_le N _) (rwds_length_le N _)
      (LU := (rwds N U).reverse) (LV := (rwds N V).reverse)
      (fun w hw => hWU w (by simpa using hw)) (fun w hw => hWV w (by simpa using hw))
      (by tsimp) (by tsimp) (by tsimp [hD2]) (by tsimp) (by tsimp)) <|
    runs_kidsShift (N := N) (t := t) (ME := ME) _ (by tsimp) (by tsimp [hHN]) (by tsimp [hE2])).mono ?_ ?_
  · intro σ' h; rw [h]
    funext i; fin_cases i <;> tsimp [hcT, htU, htV, h1, h2, emp]
  · have c1 := clen_le hTk
    simp only [length_rwds, bfS_length _ _ _ _ (hlU.trans hlV.symm), bfD_length _ _ _ _ (hlU.trans hlV.symm),
      List.length_reverse, hlU, hlV, List.length_nil, add_zero, length_ones]
    nlinarith [c1, htN, Nat.zero_le Tk.length, Nat.zero_le N]

/-! ### The block loop -/

/-- All blocks of one forward layer. -/
noncomputable def blocksF : Cmd 0 𝕋 := .loop tE blockF

theorem rwds_append (N : ℕ) (l m : List ℕ) : rwds N (l ++ m) = rwds N l ++ rwds N m := by simp [rwds]

theorem runs_blocksF {N H : ℕ} (hN : 0 < N) (hH0 : 0 < H) :
    ∀ (E D : List ℕ) (σ : Fin 𝕋 → WTape) (Dl Dr El M ME : List (List Bool)),
      AluReady N σ → σ cT = emp → D.length = E.length * (2 * H) →
      (∀ t ∈ E, t ≤ N) → (∀ d ∈ D, d < 2 ^ N + 1) →
      σ tH = ⟨[], List.replicate H []⟩ → σ tD = ⟨Dl, rwds N D ++ Dr⟩ → σ tE = ⟨El, E.map ones⟩ →
      σ tD2 = ⟨M, []⟩ → σ tE2 = ⟨ME, []⟩ → σ cHN = reg (ones (N / 2)) →
      σ tU = emp → σ tV = emp → σ tO1 = emp → σ tO2 = emp → σ tJ = emp →
      Runs blocksF σ (· = Function.update (Function.update (Function.update (Function.update σ
          tD ⟨(rwds N D).reverse ++ Dl, Dr⟩) tE ⟨(E.map ones).reverse ++ El, []⟩)
          tD2 ⟨(rwds N (layerF N H E D)).reverse ++ M, []⟩)
          tE2 ⟨((kids N E).map ones).reverse ++ ME, []⟩)
        (E.length * ((H + 1) * (1100 * N + 3000) + 2))
  | [], D, σ, Dl, Dr, El, M, ME, hr, hcT, hl, _, _, hH, hD, hE, hD2, hE2, _, _, _, _, _, _ => by
    have : D = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst this
    refine (Runs.loop_done (by simp [hE]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hD, hE, hD2, hE2, rwds, layerF, kids]
  | t :: E, D, σ, Dl, Dr, El, M, ME, hr, hcT, hl, hEt, hDv, hH, hD, hE, hD2, hE2, hHN, hU, hV, h1, h2,
      hJ => by
    obtain ⟨U, V, D', rfl, hlU, hlV⟩ : ∃ U V D', D = U ++ V ++ D' ∧ U.length = H ∧ V.length = H := by
      have h2H : 2 * H ≤ D.length := by rw [hl]; simp; nlinarith
      refine ⟨D.take H, (D.drop H).take H, D.drop (2 * H), ?_, ?_, ?_⟩
      · have e : D.drop (2 * H) = (D.drop H).drop H := by rw [List.drop_drop]; congr 1; omega
        rw [e, List.append_assoc, List.take_append_drop, List.take_append_drop]
      · simp only [List.length_take]; omega
      · simp only [List.length_take, List.length_drop]; omega
    have hb := runs_blockF hN (hEt t (by simp)) σ hr hcT (Tk := List.replicate H []) (U := U) (V := V)
      (by simp) (by simp [hlU]) (by simp [hlV]) (fun u hu => hDv u (by simp [hu]))
      (fun v hv => hDv v (by simp [hv])) (Dl := Dl) (Dr := rwds N D' ++ Dr) (El := El)
      (Er := E.map ones) (M := M) (ME := ME) hH (by rw [hD]; simp [rwds_append])
      (by rw [hE]; rfl) hD2 hE2 hHN hU hV h1 h2 hJ
    set σ₁ := Function.update (Function.update (Function.update (Function.update σ
        tD ⟨(rwds N V).reverse ++ (rwds N U).reverse ++ Dl, rwds N D' ++ Dr⟩) tE ⟨ones t :: El, E.map ones⟩)
        tD2 ⟨(rwds N (bfD N t U V)).reverse ++ (rwds N (bfS N t U V)).reverse ++ M, []⟩)
        tE2 ⟨ones (t / 2 + N / 2) :: ones (t / 2) :: ME, []⟩ with hσ₁
    have hr₁ : AluReady N σ₁ :=
      (((hr.update tD _ (by decide)).update tE _ (by decide)).update tD2 _ (by decide)).update
        tE2 _ (by decide)
    have ih := runs_blocksF hN hH0 E D' σ₁ ((rwds N V).reverse ++ (rwds N U).reverse ++ Dl) Dr
      (ones t :: El) ((rwds N (bfD N t U V)).reverse ++ (rwds N (bfS N t U V)).reverse ++ M)
      (ones (t / 2 + N / 2) :: ones (t / 2) :: ME) hr₁ (by tsimp [σ₁, hcT])
      (by simp at hl; nlinarith) (fun x hx => hEt x (by simp [hx]))
      (fun x hx => hDv x (by simp [hx])) (by tsimp [σ₁, hH]) (by tsimp [σ₁]) (by tsimp [σ₁])
      (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁, hHN]) (by tsimp [σ₁, hU]) (by tsimp [σ₁, hV])
      (by tsimp [σ₁, h1]) (by tsimp [σ₁, h2]) (by tsimp [σ₁, hJ])
    refine (Runs.loop_step (by simp [hE]) (hb.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      have hlay : layerF N H (t :: E) (U ++ V ++ D') = bfS N t U V ++ bfD N t U V ++ layerF N H E D' := by
        simp only [layerF]
        have e1 : (U ++ V ++ D').take H = U := by rw [List.append_assoc, List.take_left' hlU]
        have e2 : ((U ++ V ++ D').drop H).take H = V := by
          rw [List.append_assoc, List.drop_left' hlU, List.take_left' hlV]
        have e3 : (U ++ V ++ D').drop (2 * H) = D' := by
          rw [two_mul, ← List.drop_drop, List.append_assoc, List.drop_left' hlU, List.drop_left' hlV]
        rw [e1, e2, e3]
      rw [hlay]
      funext i; fin_cases i <;> tsimp [σ₁, rwds_append, kids]
    · simp only [List.length_cons, List.length_replicate]; nlinarith

/-! ### Swapping layers -/

/-- Make the new data and shifts current. -/
noncomputable def swapData : Cmd 0 𝕋 :=
  .seq (clear tD) <| .seq (rewind tD2) <| .seq (appendAll tD2 tD (by decide)) <|
  .seq (clear tD2) <| .seq (rewind tD) <|
  .seq (clear tE) <| .seq (rewind tE2) <| .seq (appendAll tE2 tE (by decide)) <|
  .seq (clear tE2) (rewind tE)

theorem runs_swapData (σ : Fin 𝕋 → WTape) (W : ℕ) {LD LE : List (List Bool)}
    (hLD : ∀ w ∈ LD, w.length ≤ W) (hLE : ∀ w ∈ LE, w.length ≤ W)
    (hD2 : σ tD2 = ⟨LD, []⟩) (hE2 : σ tE2 = ⟨LE, []⟩) :
    Runs swapData σ (· = Function.update (Function.update (Function.update (Function.update σ
        tD ⟨[], LD.reverse⟩) tD2 emp) tE ⟨[], LE.reverse⟩) tE2 emp)
      (2 * clen (σ tD).words + 2 * clen (σ tE).words + (LD.length + LE.length + 4) * (6 * W + 30)) := by
  unfold swapData
  have hLD' : ∀ w ∈ LD.reverse, w.length ≤ W := fun w hw => hLD w (by simpa using hw)
  have hLE' : ∀ w ∈ LE.reverse, w.length ≤ W := fun w hw => hLE w (by simpa using hw)
  refine (Runs.then (runs_clear tD σ) <| Runs.then (runs_rewind tD2 _) <|
    Runs.then (runs_appendAll (s := tD2) (d := tD) (by decide) W LD.reverse _ [] [] (by tsimp [hD2])
      (by tsimp) hLD') <|
    Runs.then (runs_clear tD2 _) <| Runs.then (runs_rewind tD _) <|
    Runs.then (runs_clear tE _) <| Runs.then (runs_rewind tE2 _) <|
    Runs.then (runs_appendAll (s := tE2) (d := tE) (by decide) W LE.reverse _ [] [] (by tsimp [hE2])
      (by tsimp) hLE') <|
    Runs.then (runs_clear tE2 _) (runs_rewind tE _)).mono ?_ ?_
  · intro σ' h; rw [h]
    funext i; fin_cases i <;> tsimp [emp]
  · have c1 := clen_le hLD
    have c2 := clen_le hLE
    tsimp [hD2, hE2, WTape.words, clen_reverse]
    nlinarith

/-- Halve the half-block size and regenerate its ticks. -/
noncomputable def swapH : Cmd 0 𝕋 :=
  .seq (op0 Rules.half false cH cH2 (by decide)) <| .seq (clear cH) <| .seq (rewind cH2) <|
  .seq (regMove cH2 cH (by decide)) <|
  .seq (clear tH) <| .seq (op0 Rules.ticks false cH tH (by decide)) <| .seq (rewind tH) (rewind cH)

theorem runs_swapH (σ : Fin 𝕋 → WTape) (H : ℕ) (hcH : σ cH = reg (ones H)) (hcH2 : σ cH2 = emp) :
    Runs swapH σ (· = Function.update (Function.update σ cH (reg (ones (H / 2))))
        tH ⟨[], List.replicate (H / 2) []⟩) (2 * clen (σ tH).words + 20 * H + 100) := by
  apply Runs.of_wp
  simp only [swapH, regMove, regIn, cpy, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hcH, hcH2, emp, reg, Rules.output_half_ones, Rules.output_ticks, Rules.output_copy]
  have t1 := time_le Rules.half (ones H) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.copy (ones (H / 2)) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t3 := time_le Rules.ticks (ones (H / 2)) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hcH, hcH2, emp, reg]
  · simp [clen, WTape.words] at t1 t2 t3 ⊢; omega

/-! ### The forward transform -/

theorem clen_rwds (N : ℕ) (l : List ℕ) : clen (rwds N l) = l.length * (N + 2) := by
  induction l with
  | nil => simp [rwds]
  | cons x l ih =>
    simp only [rwds, List.map_cons, clen_cons, rwd_length, List.length_cons] at ih ⊢
    rw [ih]; ring

theorem clen_map_ones_le (N : ℕ) (E : List ℕ) (h : ∀ t ∈ E, t ≤ N) :
    clen (E.map ones) ≤ E.length * (N + 1) := by
  have := clen_le (L := E.map ones) (W := N) (fun w hw => by
    simp only [List.mem_map] at hw; obtain ⟨t, ht, rfl⟩ := hw; simpa using h t ht)
  simpa using this

theorem replicate_append_cons {α : Type*} (a : α) (L : List α) :
    ∀ n, List.replicate n a ++ a :: L = a :: (List.replicate n a ++ L)
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, replicate_append_cons a L n]

/-- One forward layer. -/
noncomputable def layerFwd : Cmd 0 𝕋 := .seq blocksF <| .seq swapData swapH

/-- Forward layers, one per tick of `tL`. -/
noncomputable def fwdLoop : Cmd 0 𝕋 := .loop tL (.seq layerFwd (skp tL tJ (by decide)))

theorem kids_le (N : ℕ) (E : List ℕ) (h : ∀ t ∈ E, t ≤ N) : ∀ t ∈ kids N E, t ≤ N := by
  intro t ht
  simp only [kids, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ht
  obtain ⟨s, hs, rfl | rfl⟩ := ht
  · have := h s hs; omega
  · have := h s hs; omega

theorem kidsIter_le (N : ℕ) : ∀ (n : ℕ) (E : List ℕ), (∀ t ∈ E, t ≤ N) → ∀ t ∈ (kids N)^[n] E, t ≤ N
  | 0, E, h => h
  | n + 1, E, h => by
    rw [Function.iterate_succ_apply]
    exact kidsIter_le N n _ (kids_le N E h)

theorem runs_fwdLoop {N : ℕ} (hN : 0 < N) :
    ∀ (n H : ℕ) (E D : List ℕ) (σ : Fin 𝕋 → WTape) (TLl : List (List Bool)),
      H = 2 ^ n / 2 → D.length = E.length * 2 ^ n → E ≠ [] → (∀ t ∈ E, t ≤ N) →
      (∀ d ∈ D, d < 2 ^ N + 1) →
      AluReady N σ → σ cT = emp → σ tH = ⟨[], List.replicate H []⟩ → σ tD = ⟨[], rwds N D⟩ →
      σ tE = ⟨[], E.map ones⟩ → σ tD2 = emp → σ tE2 = emp → σ cHN = reg (ones (N / 2)) →
      σ tU = emp → σ tV = emp → σ tO1 = emp → σ tO2 = emp → σ tJ = emp →
      σ cH = reg (ones H) → σ cH2 = emp → σ tL = ⟨TLl, List.replicate n []⟩ →
      Runs fwdLoop σ (· = Function.update (Function.update (Function.update (Function.update
          (Function.update σ tD ⟨[], rwds N (fwdIter N n H E D)⟩) tE ⟨[], ((kids N)^[n] E).map ones⟩)
          cH (reg (ones (H / 2 ^ n)))) tH ⟨[], List.replicate (H / 2 ^ n) []⟩)
          tL ⟨List.replicate n [] ++ TLl, []⟩)
        (n * (4000 * (D.length + 1) * (N + 2)))
  | 0, H, E, D, σ, TLl, hH, hl, _, hEt, hDv, hr, hcT, htH, hD, hE, hD2, hE2, hHN, hU, hV, h1, h2, hJ,
      hcH, hcH2, htL => by
    show Runs (Cmd.loop tL _) _ _ _
    refine (Runs.loop_done (by simp [htL]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    have : H = 0 := by simpa using hH
    subst this
    funext i; fin_cases i <;> tsimp [hD, hE, hcH, htH, htL, fwdIter]
  | n + 1, H, E, D, σ, TLl, hH, hl, hE0, hEt, hDv, hr, hcT, htH, hD, hE, hD2, hE2, hHN, hU, hV, h1, h2, hJ,
      hcH, hcH2, htL => by
    show Runs (Cmd.loop tL _) _ _ _
    have hH' : H = 2 ^ n := by rw [hH, pow_succ]; simp
    have hH0 : 0 < H := by rw [hH']; exact Nat.two_pow_pos n
    have hl' : D.length = E.length * (2 * H) := by rw [hl, hH', pow_succ]; ring
    have hb := runs_blocksF hN hH0 E D σ [] [] [] [] [] hr hcT hl' hEt hDv htH (by simp [hD])
      (by simp [hE]) (by simpa [emp] using hD2) (by simpa [emp] using hE2) hHN hU hV h1 h2 hJ
    set L := layerF N H E D
    have hLl : L.length = (kids N E).length * 2 ^ n := by
      rw [layerF_length N H E D hl', length_kids, hH']; ring
    have hLv : ∀ x ∈ L, x < 2 ^ N + 1 := layerF_lt N H E D
    set σ₁ := Function.update (Function.update (Function.update (Function.update σ
          tD ⟨(rwds N D).reverse ++ [], []⟩) tE ⟨(E.map ones).reverse ++ [], []⟩)
          tD2 ⟨(rwds N L).reverse ++ [], []⟩)
          tE2 ⟨((kids N E).map ones).reverse ++ [], []⟩ with hσ₁
    have hs1 := runs_swapData σ₁ (N + 1) (LD := (rwds N L).reverse ++ [])
      (LE := ((kids N E).map ones).reverse ++ [])
      (fun w hw => rwds_length_le N L w (by simpa using hw))
      (fun w hw => by
        simp only [List.append_nil, List.mem_reverse, List.mem_map] at hw
        obtain ⟨t, ht, rfl⟩ := hw; simp; exact kids_le N E hEt t ht |>.trans (Nat.le_succ N))
      (by tsimp [σ₁]) (by tsimp [σ₁])
    set σ₂ := Function.update (Function.update (Function.update (Function.update σ₁
        tD ⟨[], ((rwds N L).reverse ++ []).reverse⟩) tD2 emp)
        tE ⟨[], (((kids N E).map ones).reverse ++ []).reverse⟩) tE2 emp with hσ₂
    have hs2 := runs_swapH σ₂ H (by tsimp [σ₂, σ₁, hcH]) (by tsimp [σ₂, σ₁, hcH2])
    set σ₃ := Function.update (Function.update σ₂ cH (reg (ones (H / 2))))
        tH ⟨[], List.replicate (H / 2) []⟩ with hσ₃
    have hs3 := runs_skp (a := 0) (s := tL) (j := tJ) (by decide) σ₃ (by tsimp [σ₃, σ₂, σ₁, htL])
      (by tsimp [σ₃, σ₂, σ₁, hJ, emp])
    set σ₄ := Function.update σ₃ tL (σ₃ tL).next with hσ₄
    have hr₄ : AluReady N σ₄ := by
      refine ((((((((((hr.update tD _ (by decide)).update tE _ (by decide)).update tD2 _ (by decide)).update
        tE2 _ (by decide)).update tD _ (by decide)).update tD2 _ (by decide)).update tE _ (by decide)).update
        tE2 _ (by decide)).update cH _ (by decide)).update tH _ (by decide)).update tL _ (by decide)
    have hk0 : kids N E ≠ [] := by
      rw [← List.length_pos_iff, length_kids]
      have := List.length_pos_iff.mpr hE0
      omega
    have ih := runs_fwdLoop hN n (H / 2) (kids N E) L σ₄ ([] :: TLl) (by rw [hH']; try simp [pow_succ])
      hLl hk0 (kids_le N E hEt) hLv hr₄ (by tsimp [σ₄, σ₃, σ₂, σ₁, hcT]) (by tsimp [σ₄, σ₃, σ₂, σ₁])
      (by tsimp [σ₄, σ₃, σ₂, σ₁]) (by tsimp [σ₄, σ₃, σ₂, σ₁]) (by tsimp [σ₄, σ₃, σ₂, σ₁])
      (by tsimp [σ₄, σ₃, σ₂, σ₁]) (by tsimp [σ₄, σ₃, σ₂, σ₁, hHN]) (by tsimp [σ₄, σ₃, σ₂, σ₁, hU])
      (by tsimp [σ₄, σ₃, σ₂, σ₁, hV]) (by tsimp [σ₄, σ₃, σ₂, σ₁, h1]) (by tsimp [σ₄, σ₃, σ₂, σ₁, h2])
      (by tsimp [σ₄, σ₃, σ₂, σ₁, hJ]) (by tsimp [σ₄, σ₃, σ₂, σ₁]) (by tsimp [σ₄, σ₃, σ₂, σ₁, hcH2])
      (by tsimp [σ₄, σ₃, σ₂, σ₁, htL, List.replicate_succ])
    refine (Runs.loop_step (by simp [htL])
      (Runs.then (Runs.then hb (Runs.then hs1 hs2))
        (hs3.mono (fun σ' h' => by rw [h']; exact ih) le_rfl))).mono (fun σ' h' => ?_) ?_
    · rw [h']
      have e1 : H / 2 / 2 ^ n = H / 2 ^ (n + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
      funext i; fin_cases i <;> tsimp [σ₄, σ₃, σ₂, σ₁, L, fwdIter, Function.iterate_succ_apply, e1,
        htL, List.replicate_succ, hD2, hE2, hcH2, hcT, hU, hV, h1, h2, replicate_append_cons]
    · have hE2H : E.length * (H + 1) ≤ D.length := by rw [hl']; nlinarith
      have hkl := length_kids N E
      have cD := clen_rwds N D
      have cE := clen_map_ones_le N E hEt
      have hE1 : 1 ≤ E.length := List.length_pos_iff.mpr hE0
      have hHD : H ≤ D.length := by rw [hl']; nlinarith [Nat.zero_le E.length, hH0]
      have hED : 2 * E.length ≤ D.length := by rw [hl']; nlinarith
      have cH : clen (List.replicate H ([] : List Bool)) = H := by simp [clen]
      tsimp [σ₃, σ₂, σ₁, htH, WTape.words, clen_reverse, clen_append, length_rwds, hLl, hkl, cH,
        replicate_append_cons, htL]
      have hDE : 2 * E.length * 2 ^ n = D.length := by rw [hl, pow_succ]; ring
      simp only [List.replicate_succ, List.head?_cons, Option.getD_some, List.length_nil, hDE, cD] at *
      nlinarith [Nat.zero_le N, Nat.zero_le D.length, Nat.zero_le n, cE, hE2H, hHD, hED]

end IntegerMultBounds.Schoenhage

