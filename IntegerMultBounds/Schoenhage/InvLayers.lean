import IntegerMultBounds.Schoenhage.Layers

/-! Inverse transform layers on word tapes. The inverse pair loop runs the
inverse butterfly over the half-block tapes; an inverse block loads the
block's complementary shift `N - t`; a layer at depth `s` first recomputes the
shift list `shiftsAt N s` from the root by `s` rounds of `kids`. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp

namespace Tp
abbrev tS : Fin 𝕋 := 28
abbrev cS : Fin 𝕋 := 29
abbrev tT : Fin 𝕋 := 30
end Tp

/-! ### The inverse pair loop -/

/-- Inverse butterflies over the half-block tapes. -/
noncomputable def pairI : Cmd 0 𝕋 := .loop tU bflyI

set_option maxHeartbeats 1000000 in
theorem runs_pairI {N s : ℕ} (hN : 0 < N) (hsN : s ≤ N) :
    ∀ (P Q : List ℕ) (σ : Fin 𝕋 → WTape) (LU LV RV M1 M2 : List (List Bool)),
      AluReady N σ → σ cT = reg (ones s) → P.length = Q.length →
      (∀ p ∈ P, p < 2 ^ N + 1) → (∀ q ∈ Q, q < 2 ^ N + 1) →
      σ tU = ⟨LU, rwds N P⟩ → σ tV = ⟨LV, rwds N Q ++ RV⟩ → σ tO1 = ⟨M1, []⟩ → σ tO2 = ⟨M2, []⟩ →
      Runs pairI σ (· = Function.update (Function.update (Function.update (Function.update σ
          tU ⟨(rwds N P).reverse ++ LU, []⟩) tV ⟨(rwds N Q).reverse ++ LV, RV⟩)
          tO1 ⟨(rwds N (ibS N P Q)).reverse ++ M1, []⟩)
          tO2 ⟨(rwds N (ibD N (N - s) P Q)).reverse ++ M2, []⟩)
        (P.length * (2000 * N + 4002))
  | [], Q, σ, LU, LV, RV, M1, M2, hr, hcT, hl, _, _, hU, hV, h1, h2 => by
    have : Q = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    subst this
    refine (Runs.loop_done (by simp [hU, rwds]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hU, hV, h1, h2, rwds, ibS, ibD]
  | p :: P, q :: Q, σ, LU, LV, RV, M1, M2, hr, hcT, hl, hPv, hQv, hU, hV, h1, h2 => by
    have hp := hPv p (by simp)
    have hq := hQv q (by simp)
    have b := runs_bflyI hN hsN σ hr hcT hp hq (LU := LU) (RU := rwds N P) (LV := LV)
      (RV := rwds N Q ++ RV) (M1 := M1) (M2 := M2) (by simpa [rwds] using hU)
      (by simpa [rwds] using hV) h1 h2
    set σ₁ := Function.update (Function.update (Function.update (Function.update σ
        tU ⟨rwd N p :: LU, rwds N P⟩) tV ⟨rwd N q :: LV, rwds N Q ++ RV⟩)
        tO1 ⟨rwd N ((p + q) % (2 ^ N + 1)) :: M1, []⟩)
        tO2 ⟨rwd N ((2 ^ N + 1 - 2 ^ s * ((p + (2 ^ N + 1) - q) % (2 ^ N + 1)) % (2 ^ N + 1)) %
          (2 ^ N + 1)) :: M2, []⟩ with hσ₁
    have hr₁ : AluReady N σ₁ :=
      (((hr.update tU _ (by decide)).update tV _ (by decide)).update tO1 _ (by decide)).update
        tO2 _ (by decide)
    have ih := runs_pairI hN hsN P Q σ₁ (rwd N p :: LU) (rwd N q :: LV) RV
      (rwd N ((p + q) % (2 ^ N + 1)) :: M1)
      (rwd N ((2 ^ N + 1 - 2 ^ s * ((p + (2 ^ N + 1) - q) % (2 ^ N + 1)) % (2 ^ N + 1)) %
        (2 ^ N + 1)) :: M2)
      hr₁ (by tsimp [σ₁, hcT]) (by simpa using hl)
      (fun x hx => hPv x (by simp [hx])) (fun x hx => hQv x (by simp [hx]))
      (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁]) (by tsimp [σ₁])
    refine (Runs.loop_step (by simp [hU, rwds]) (b.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      have hs : N - (N - s) = s := by omega
      funext i; fin_cases i <;> tsimp [σ₁, rwds, ibS, ibD, Fm, hs]
    · simp only [List.length_cons]; nlinarith
  | p :: P, [], σ, _, _, _, _, _, _, _, hl, _, _, _, _, _, _ => by simp at hl

/-! ### Inverse blocks -/

/-- Load `ones (N - t)` into `cT` from the current shift `ones t` of `tE`. -/
noncomputable def compShift : Cmd 0 𝕋 :=
  .seq (regIn tE tT (by decide)) <| .seq (op1 Rules.drop false cN tT cT (by decide) (by decide) (by decide)) <|
  .seq (rewind cT) <| .seq (rewind cN) (clear tT)

theorem runs_compShift {N t : ℕ} (σ : Fin 𝕋 → WTape) {El Er : List (List Bool)}
    (hE : σ tE = ⟨El, ones t :: Er⟩) (hN : σ cN = reg (ones N)) (hT : σ tT = emp) (hcT : σ cT = emp) :
    Runs compShift σ (· = Function.update (Function.update σ tE ⟨ones t :: El, Er⟩) cT
        (reg (ones (N - t)))) (5 * t + 3 * N + 50) := by
  unfold compShift
  have tail : Runs (a := 0) (.seq (op1 Rules.drop false cN tT cT (by decide) (by decide) (by decide)) <|
      .seq (rewind cT) <| .seq (rewind cN) (clear tT))
      (Function.update (Function.update σ tE ⟨ones t :: El, Er⟩) tT (reg (ones t)))
      (· = Function.update (Function.update σ tE ⟨ones t :: El, Er⟩) cT (reg (ones (N - t))))
      (3 * t + 3 * N + 30) := by
    apply Runs.of_wp
    simp only [WP, wp_op1, wp_rewind, wp_clear]
    tsimp [hN, hcT, emp, reg, Rules.output_drop]
    have t1 := time_le Rules.drop (ones N) (fun _ => ones t) t (fun _ => by simp)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [hN, hcT, hT, emp, reg]
    · simp [clen, WTape.words] at t1 ⊢; omega
  exact (Runs.then (runs_regIn (s := tE) (r := tT) (by decide) σ hE hT) tail).mono (fun σ' h => h)
    (by simp; omega)

/-- One block of an inverse layer. -/
noncomputable def blockI : Cmd 0 𝕋 :=
  .seq splitBlock <| .seq compShift <| .seq pairI <| .seq collect (clear cT)

theorem ibS_length (N : ℕ) (U V : List ℕ) (h : U.length = V.length) : (ibS N U V).length = U.length := by
  simp [ibS, h]

theorem ibD_length (N t : ℕ) (U V : List ℕ) (h : U.length = V.length) : (ibD N t U V).length = U.length := by
  simp [ibD, h]

theorem runs_blockI {N t : ℕ} (hN : 0 < N) (htN : t ≤ N) (σ : Fin 𝕋 → WTape) (hr : AluReady N σ)
    (hcT : σ cT = emp) (htT : σ tT = emp) {Tk : List (List Bool)} (hTk : ∀ w ∈ Tk, w.length ≤ N + 1)
    {U V : List ℕ} (hlU : U.length = Tk.length) (hlV : V.length = Tk.length)
    (hUv : ∀ u ∈ U, u < 2 ^ N + 1) (hVv : ∀ v ∈ V, v < 2 ^ N + 1)
    {Dl Dr El Er M : List (List Bool)}
    (hH : σ tH = ⟨[], Tk⟩) (hD : σ tD = ⟨Dl, rwds N U ++ rwds N V ++ Dr⟩)
    (hE : σ tE = ⟨El, ones t :: Er⟩) (hD2 : σ tD2 = ⟨M, []⟩)
    (htU : σ tU = emp) (htV : σ tV = emp)
    (h1 : σ tO1 = emp) (h2 : σ tO2 = emp) (hJ : σ tJ = emp) :
    Runs blockI σ (· = Function.update (Function.update (Function.update σ
        tD ⟨(rwds N V).reverse ++ (rwds N U).reverse ++ Dl, Dr⟩) tE ⟨ones t :: El, Er⟩)
        tD2 ⟨(rwds N (ibD N t U V)).reverse ++ (rwds N (ibS N U V)).reverse ++ M, []⟩)
      ((Tk.length + 1) * (2100 * N + 5000)) := by
  unfold blockI
  have hWU := rwds_length_le N U
  have hWV := rwds_length_le N V
  have hs : N - (N - t) = t := by omega
  have hP := runs_pairI (s := N - t) hN (Nat.sub_le N t) U V
  rw [hs] at hP
  refine (Runs.then (runs_splitBlock σ (N + 1) hTk hWU hWV (by rw [length_rwds, hlU])
      (by rw [length_rwds, hlV]) hH hD htU htV hJ) <|
    Runs.then (runs_compShift (N := N) (t := t) (El := El) (Er := Er) _ (by tsimp [hE])
      (by tsimp [hr.2.1]) (by tsimp [htT]) (by tsimp [hcT])) <|
    Runs.then (hP _ [] [] [] [] []
      (((((hr.update tD _ (by decide)).update tU _ (by decide)).update tV _ (by decide)).update
        tE _ (by decide)).update cT _ (by decide)) (by tsimp) (by rw [hlU, hlV]) hUv hVv
      (by tsimp) (by tsimp) (by tsimp [h1, emp]) (by tsimp [h2, emp])) <|
    Runs.then (runs_collect _ (N + 1) (S := rwds N (ibS N U V)) (Df := rwds N (ibD N t U V)) (M := M)
      (rwds_length_le N _) (rwds_length_le N _)
      (LU := (rwds N U).reverse) (LV := (rwds N V).reverse)
      (fun w hw => hWU w (by simpa using hw)) (fun w hw => hWV w (by simpa using hw))
      (by tsimp) (by tsimp) (by tsimp [hD2]) (by tsimp) (by tsimp)) <|
    runs_clear cT _).mono ?_ ?_
  · intro σ' h; rw [h]
    funext i; fin_cases i <;> tsimp [hcT, htU, htV, h1, h2, emp]
  · have c1 := clen_le hTk
    tsimp [reg, WTape.words, clen] at c1 ⊢
    simp only [length_rwds, ibS_length _ _ _ (hlU.trans hlV.symm), ibD_length _ _ _ _ (hlU.trans hlV.symm),
      hlU, hlV] at c1 ⊢
    have : N - t ≤ N := Nat.sub_le N t
    nlinarith [c1, htN, Nat.zero_le Tk.length, Nat.zero_le N]

/-- All blocks of one inverse layer. -/
noncomputable def blocksI : Cmd 0 𝕋 := .loop tE blockI

theorem runs_blocksI {N H : ℕ} (hN : 0 < N) (hH0 : 0 < H) :
    ∀ (E D : List ℕ) (σ : Fin 𝕋 → WTape) (Dl Dr El M : List (List Bool)),
      AluReady N σ → σ cT = emp → σ tT = emp → D.length = E.length * (2 * H) →
      (∀ t ∈ E, t ≤ N) → (∀ d ∈ D, d < 2 ^ N + 1) →
      σ tH = ⟨[], List.replicate H []⟩ → σ tD = ⟨Dl, rwds N D ++ Dr⟩ → σ tE = ⟨El, E.map ones⟩ →
      σ tD2 = ⟨M, []⟩ → σ tU = emp → σ tV = emp → σ tO1 = emp → σ tO2 = emp → σ tJ = emp →
      Runs blocksI σ (· = Function.update (Function.update (Function.update σ
          tD ⟨(rwds N D).reverse ++ Dl, Dr⟩) tE ⟨(E.map ones).reverse ++ El, []⟩)
          tD2 ⟨(rwds N (layerI N H E D)).reverse ++ M, []⟩)
        (E.length * ((H + 1) * (2100 * N + 5000) + 2))
  | [], D, σ, Dl, Dr, El, M, hr, hcT, _, hl, _, _, hH, hD, hE, hD2, _, _, _, _, _ => by
    have : D = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst this
    refine (Runs.loop_done (by simp [hE]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hD, hE, hD2, rwds, layerI]
  | t :: E, D, σ, Dl, Dr, El, M, hr, hcT, htT, hl, hEt, hDv, hH, hD, hE, hD2, hU, hV, h1, h2, hJ => by
    obtain ⟨U, V, D', rfl, hlU, hlV⟩ : ∃ U V D', D = U ++ V ++ D' ∧ U.length = H ∧ V.length = H := by
      have h2H : 2 * H ≤ D.length := by rw [hl]; simp; nlinarith
      refine ⟨D.take H, (D.drop H).take H, D.drop (2 * H), ?_, ?_, ?_⟩
      · have e : D.drop (2 * H) = (D.drop H).drop H := by rw [List.drop_drop]; congr 1; omega
        rw [e, List.append_assoc, List.take_append_drop, List.take_append_drop]
      · simp only [List.length_take]; omega
      · simp only [List.length_take, List.length_drop]; omega
    have hb := runs_blockI hN (hEt t (by simp)) σ hr hcT htT (Tk := List.replicate H []) (U := U) (V := V)
      (by simp) (by simp [hlU]) (by simp [hlV]) (fun u hu => hDv u (by simp [hu]))
      (fun v hv => hDv v (by simp [hv])) (Dl := Dl) (Dr := rwds N D' ++ Dr) (El := El)
      (Er := E.map ones) (M := M) hH (by rw [hD]; simp [rwds_append])
      (by rw [hE]; rfl) hD2 hU hV h1 h2 hJ
    set σ₁ := Function.update (Function.update (Function.update σ
        tD ⟨(rwds N V).reverse ++ (rwds N U).reverse ++ Dl, rwds N D' ++ Dr⟩) tE ⟨ones t :: El, E.map ones⟩)
        tD2 ⟨(rwds N (ibD N t U V)).reverse ++ (rwds N (ibS N U V)).reverse ++ M, []⟩ with hσ₁
    have hr₁ : AluReady N σ₁ :=
      ((hr.update tD _ (by decide)).update tE _ (by decide)).update tD2 _ (by decide)
    have ih := runs_blocksI hN hH0 E D' σ₁ ((rwds N V).reverse ++ (rwds N U).reverse ++ Dl) Dr
      (ones t :: El) ((rwds N (ibD N t U V)).reverse ++ (rwds N (ibS N U V)).reverse ++ M)
      hr₁ (by tsimp [σ₁, hcT]) (by tsimp [σ₁, htT])
      (by simp at hl; nlinarith) (fun x hx => hEt x (by simp [hx]))
      (fun x hx => hDv x (by simp [hx])) (by tsimp [σ₁, hH]) (by tsimp [σ₁]) (by tsimp [σ₁])
      (by tsimp [σ₁]) (by tsimp [σ₁, hU]) (by tsimp [σ₁, hV])
      (by tsimp [σ₁, h1]) (by tsimp [σ₁, h2]) (by tsimp [σ₁, hJ])
    refine (Runs.loop_step (by simp [hE]) (hb.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      have hlay : layerI N H (t :: E) (U ++ V ++ D') = ibS N U V ++ ibD N t U V ++ layerI N H E D' := by
        simp only [layerI]
        have e1 : (U ++ V ++ D').take H = U := by rw [List.append_assoc, List.take_left' hlU]
        have e2 : ((U ++ V ++ D').drop H).take H = V := by
          rw [List.append_assoc, List.drop_left' hlU, List.take_left' hlV]
        have e3 : (U ++ V ++ D').drop (2 * H) = D' := by
          rw [two_mul, ← List.drop_drop, List.append_assoc, List.drop_left' hlU, List.drop_left' hlV]
        rw [e1, e2, e3]
      rw [hlay]
      funext i; fin_cases i <;> tsimp [σ₁, rwds_append]
    · simp only [List.length_cons, List.length_replicate]; nlinarith

/-! ### Recomputing the shifts -/

/-- The children's shifts of every shift on `tE`, appended to `tE2`. -/
noncomputable def kidsLoop : Cmd 0 𝕋 := .loop tE (.seq (regIn tE cT (by decide)) kidsShift)

theorem runs_kidsLoop {N : ℕ} :
    ∀ (E : List ℕ) (σ : Fin 𝕋 → WTape) (El ME : List (List Bool)),
      (∀ t ∈ E, t ≤ N) → σ cT = emp → σ cHN = reg (ones (N / 2)) →
      σ tE = ⟨El, E.map ones⟩ → σ tE2 = ⟨ME, []⟩ →
      Runs kidsLoop σ (· = Function.update (Function.update σ
          tE ⟨(E.map ones).reverse ++ El, []⟩) tE2 ⟨((kids N E).map ones).reverse ++ ME, []⟩)
        (E.length * (10 * N + 80))
  | [], σ, El, ME, _, _, _, hE, hE2 => by
    refine (Runs.loop_done (by simp [hE]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hE, hE2, kids]
  | t :: E, σ, El, ME, hEt, hcT, hHN, hE, hE2 => by
    have ht := hEt t (by simp)
    have h1 := runs_regIn (a := 0) (s := tE) (r := cT) (by decide) σ (L := El) (R := E.map ones)
      (w := ones t) (by simpa using hE) hcT
    have h2 := runs_kidsShift (N := N) (t := t) (ME := ME) (Function.update (Function.update σ
      tE ⟨ones t :: El, E.map ones⟩) cT (reg (ones t))) (by tsimp) (by tsimp [hHN]) (by tsimp [hE2])
    set σ₁ := Function.update (Function.update (Function.update (Function.update σ
      tE ⟨ones t :: El, E.map ones⟩) cT (reg (ones t))) tE2
        ⟨ones (t / 2 + N / 2) :: ones (t / 2) :: ME, []⟩) cT emp with hσ₁
    have ih := runs_kidsLoop E σ₁ (ones t :: El) (ones (t / 2 + N / 2) :: ones (t / 2) :: ME)
      (fun x hx => hEt x (by simp [hx])) (by tsimp [σ₁]) (by tsimp [σ₁, hHN]) (by tsimp [σ₁])
      (by tsimp [σ₁])
    refine (Runs.loop_step (by simp [hE]) ((Runs.then h1 h2).mono
      (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono (fun σ' h' => ?_) ?_
    · rw [h']
      funext i; fin_cases i <;> tsimp [σ₁, kids, hcT]
    · simp only [List.length_cons, length_ones]; nlinarith

/-- Make the children's shifts current. -/
noncomputable def swapE : Cmd 0 𝕋 :=
  .seq (clear tE) <| .seq (rewind tE2) <| .seq (appendAll tE2 tE (by decide)) <|
  .seq (clear tE2) (rewind tE)

theorem runs_swapE (σ : Fin 𝕋 → WTape) (W : ℕ) {LE : List (List Bool)}
    (hLE : ∀ w ∈ LE, w.length ≤ W) (hE2 : σ tE2 = ⟨LE, []⟩) :
    Runs swapE σ (· = Function.update (Function.update σ tE ⟨[], LE.reverse⟩) tE2 emp)
      (2 * clen (σ tE).words + (LE.length + 2) * (6 * W + 30)) := by
  unfold swapE
  have hLE' : ∀ w ∈ LE.reverse, w.length ≤ W := fun w hw => hLE w (by simpa using hw)
  refine (Runs.then (runs_clear tE σ) <| Runs.then (runs_rewind tE2 _) <|
    Runs.then (runs_appendAll (s := tE2) (d := tE) (by decide) W LE.reverse _ [] [] (by tsimp [hE2])
      (by tsimp) hLE') <|
    Runs.then (runs_clear tE2 _) (runs_rewind tE _)).mono ?_ ?_
  · intro σ' h; rw [h]
    funext i; fin_cases i <;> tsimp [emp]
  · have c2 := clen_le hLE
    tsimp [hE2, WTape.words, clen_reverse]
    nlinarith

/-- One round of children: the shifts one level deeper. -/
noncomputable def kidsRound : Cmd 0 𝕋 := .seq kidsLoop <| .seq swapE (skp tS tJ (by decide))

/-- One round per tick of `tS`. -/
noncomputable def kidsRounds : Cmd 0 𝕋 := .loop tS kidsRound

theorem runs_kidsRounds {N : ℕ} :
    ∀ (s : ℕ) (E : List ℕ) (σ : Fin 𝕋 → WTape) (TSl : List (List Bool)),
      E ≠ [] → (∀ t ∈ E, t ≤ N) → σ cT = emp → σ cHN = reg (ones (N / 2)) →
      σ tE = ⟨[], E.map ones⟩ → σ tE2 = emp → σ tJ = emp → σ tS = ⟨TSl, List.replicate s []⟩ →
      Runs kidsRounds σ (· = Function.update (Function.update σ
          tE ⟨[], ((kids N)^[s] E).map ones⟩) tS ⟨List.replicate s [] ++ TSl, []⟩)
        ((2 ^ (s + 1) - 1) * E.length * (50 * N + 300))
  | 0, E, σ, TSl, _, _, _, _, hE, _, _, hS => by
    show Runs (Cmd.loop tS _) _ _ _
    refine (Runs.loop_done (by simp [hS]) rfl).mono (fun σ' h' => ?_) (Nat.zero_le _)
    subst h'
    funext i; fin_cases i <;> tsimp [hE, hS]
  | s + 1, E, σ, TSl, hE0, hEt, hcT, hHN, hE, hE2, hJ, hS => by
    show Runs (Cmd.loop tS _) _ _ _
    have h1 := runs_kidsLoop (N := N) E σ [] [] hEt hcT hHN hE (by simpa [emp] using hE2)
    set σ₁ := Function.update (Function.update σ tE ⟨(E.map ones).reverse ++ [], []⟩)
      tE2 ⟨((kids N E).map ones).reverse ++ [], []⟩ with hσ₁
    have hK : ∀ w ∈ ((kids N E).map ones).reverse ++ [], w.length ≤ N := by
      intro w hw
      simp only [List.append_nil, List.mem_reverse, List.mem_map] at hw
      obtain ⟨t, ht, rfl⟩ := hw; simpa using kids_le N E hEt t ht
    have h2 := runs_swapE σ₁ N hK (by tsimp [σ₁])
    set σ₂ := Function.update (Function.update σ₁ tE ⟨[], (((kids N E).map ones).reverse ++ []).reverse⟩)
      tE2 emp with hσ₂
    have h3 := runs_skp (a := 0) (s := tS) (j := tJ) (by decide) σ₂ (by tsimp [σ₂, σ₁, hS])
      (by tsimp [σ₂, σ₁, hJ, emp])
    set σ₃ := Function.update σ₂ tS (σ₂ tS).next with hσ₃
    have hk0 : kids N E ≠ [] := by
      rw [← List.length_pos_iff, length_kids]
      have := List.length_pos_iff.mpr hE0
      omega
    have ih := runs_kidsRounds s (kids N E) σ₃ ([] :: TSl) hk0 (kids_le N E hEt)
      (by tsimp [σ₃, σ₂, σ₁, hcT]) (by tsimp [σ₃, σ₂, σ₁, hHN]) (by tsimp [σ₃, σ₂, σ₁])
      (by tsimp [σ₃, σ₂, σ₁]) (by tsimp [σ₃, σ₂, σ₁, hJ]) (by tsimp [σ₃, σ₂, σ₁, hS, List.replicate_succ])
    refine (Runs.loop_step (by simp [hS])
      (Runs.then h1 (Runs.then h2 (h3.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)))).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      funext i; fin_cases i <;> tsimp [σ₃, σ₂, σ₁, Function.iterate_succ_apply, hS, List.replicate_succ,
        hE2, replicate_append_cons]
    · have cE := clen_map_ones_le N E hEt
      have hE1 : 1 ≤ E.length := List.length_pos_iff.mpr hE0
      obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ (s + 1) = Q + 1 := ⟨2 ^ (s + 1) - 1, by have := Nat.one_le_two_pow (n := s + 1); omega⟩
      have hQ2 : 2 ^ (s + 1 + 1) - 1 = 2 * Q + 1 := by rw [pow_succ, hQ]; omega
      rw [hQ2, hQ, Nat.add_sub_cancel]
      tsimp [σ₂, σ₁, hE, hS, WTape.words, clen_reverse, length_kids]
      simp only [List.replicate_succ, List.head?_cons, Option.getD_some, List.length_nil] at *
      nlinarith [Nat.zero_le N, Nat.zero_le Q, cE, hE1]

/-- The root shift on `tE` and one tick per level on `tS`. -/
noncomputable def shiftRoot : Cmd 0 𝕋 :=
  .seq (op0 Rules.copy false cHN tE (by decide)) <| .seq (rewind tE) <| .seq (rewind cHN) <|
  .seq (op0 Rules.ticks false cS tS (by decide)) <| .seq (rewind tS) (rewind cS)

/-- The shifts at depth `s` (held in unary in `cS`) on `tE`. -/
noncomputable def mkShifts : Cmd 0 𝕋 := .seq shiftRoot <| .seq kidsRounds (clear tS)

theorem shiftsAt_eq (N : ℕ) : ∀ s, shiftsAt N s = (kids N)^[s] [N / 2]
  | 0 => rfl
  | s + 1 => by rw [shiftsAt, shiftsAt_eq N s, Function.iterate_succ_apply']

theorem shiftsAt_le (N s : ℕ) : ∀ t ∈ shiftsAt N s, t ≤ N := by
  rw [shiftsAt_eq]; exact kidsIter_le N s _ (by simp; omega)

theorem runs_mkShifts {N s : ℕ} (σ : Fin 𝕋 → WTape) (hcT : σ cT = emp) (hHN : σ cHN = reg (ones (N / 2)))
    (hE : σ tE = emp) (hE2 : σ tE2 = emp) (hJ : σ tJ = emp) (hS : σ tS = emp) (hcS : σ cS = reg (ones s)) :
    Runs mkShifts σ (· = Function.update σ tE ⟨[], (shiftsAt N s).map ones⟩)
      (2 ^ (s + 1) * (50 * N + 300) + 6 * s) := by
  unfold mkShifts
  have pre : Runs shiftRoot σ (· = Function.update (Function.update σ tE ⟨[], [ones (N / 2)]⟩) tS ⟨[], List.replicate s []⟩)
      (3 * N + 3 * s + 40) := by
    apply Runs.of_wp
    simp only [shiftRoot, WP, wp_op0, wp_rewind]
    tsimp [hHN, hE, hS, hcS, emp, reg, Rules.output_copy, Rules.output_ticks]
    have t1 := time_le Rules.copy (ones (N / 2)) (fun j => j.elim0) 0 (fun j => j.elim0)
    have t2 := time_le Rules.ticks (ones s) (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> tsimp [hHN, hE, hS, hcS, emp, reg]
    · simp [clen] at t1 t2 ⊢; omega
  set σ₁ := Function.update (Function.update σ tE ⟨[], [ones (N / 2)]⟩) tS ⟨[], List.replicate s []⟩
  have hk := runs_kidsRounds (N := N) s [N / 2] σ₁ [] (by simp) (by simp; omega) (by tsimp [σ₁, hcT])
    (by tsimp [σ₁, hHN]) (by tsimp [σ₁]) (by tsimp [σ₁, hE2]) (by tsimp [σ₁, hJ]) (by tsimp [σ₁])
  refine (Runs.then pre (Runs.then hk (runs_clear tS _))).mono ?_ ?_
  · intro σ' h; rw [h]
    funext i; fin_cases i <;> tsimp [σ₁, hS, emp, shiftsAt_eq]
  · obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ (s + 1) = Q + 1 :=
      ⟨2 ^ (s + 1) - 1, by have := Nat.one_le_two_pow (n := s + 1); omega⟩
    tsimp [σ₁, WTape.words, clen]
    rw [hQ, Nat.add_sub_cancel]
    nlinarith

/-! ### Layer bookkeeping -/

/-- Decrement the depth register `cS`. -/
noncomputable def decS : Cmd 0 𝕋 :=
  .seq (op1 Rules.drop false cS c1 cH2 (by decide) (by decide) (by decide)) <| .seq (rewind c1) <|
  .seq (clear cS) <| .seq (rewind cH2) (regMove cH2 cS (by decide))

theorem runs_decS {s : ℕ} (σ : Fin 𝕋 → WTape) (hcS : σ cS = reg (ones s)) (h1 : σ c1 = reg [true])
    (hcH2 : σ cH2 = emp) :
    Runs decS σ (· = Function.update σ cS (reg (ones (s - 1)))) (12 * s + 60) := by
  have htl : (ones s).tail = ones (s - 1) := by simp [ones, List.tail_replicate]
  apply Runs.of_wp
  simp only [decS, regMove, regIn, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hcS, h1, hcH2, emp, reg, Rules.output_drop, Rules.output_copy, htl]
  have t1 := time_le Rules.drop (ones s) (fun _ => [true]) 1 (fun _ => by simp)
  have t2 := time_le Rules.copy (ones (s - 1)) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hcS, h1, hcH2, emp, reg, htl]
  · simp [clen, WTape.words] at t1 t2 ⊢; omega

/-- Make the new data current and empty the shift tape. -/
noncomputable def swapDI : Cmd 0 𝕋 :=
  .seq (clear tD) <| .seq (rewind tD2) <| .seq (appendAll tD2 tD (by decide)) <|
  .seq (clear tD2) <| .seq (rewind tD) (clear tE)

theorem runs_swapDI (σ : Fin 𝕋 → WTape) (W : ℕ) {LD : List (List Bool)}
    (hLD : ∀ w ∈ LD, w.length ≤ W) (hD2 : σ tD2 = ⟨LD, []⟩) :
    Runs swapDI σ (· = Function.update (Function.update (Function.update σ
        tD ⟨[], LD.reverse⟩) tD2 emp) tE emp)
      (2 * clen (σ tD).words + 2 * clen (σ tE).words + (LD.length + 2) * (6 * W + 30)) := by
  unfold swapDI
  have hLD' : ∀ w ∈ LD.reverse, w.length ≤ W := fun w hw => hLD w (by simpa using hw)
  refine (Runs.then (runs_clear tD σ) <| Runs.then (runs_rewind tD2 _) <|
    Runs.then (runs_appendAll (s := tD2) (d := tD) (by decide) W LD.reverse _ [] [] (by tsimp [hD2])
      (by tsimp) hLD') <|
    Runs.then (runs_clear tD2 _) <| Runs.then (runs_rewind tD _) (runs_clear tE _)).mono ?_ ?_
  · intro σ' h; rw [h]
    funext i; fin_cases i <;> tsimp [emp]
  · have c1 := clen_le hLD
    tsimp [hD2, WTape.words, clen_reverse]
    nlinarith

/-- Double the half-block size and regenerate its ticks. -/
noncomputable def doubleH : Cmd 0 𝕋 :=
  .seq (op0 Rules.copy false cH cH2 (by decide)) <| .seq (rewind cH) <|
  .seq (op0 Rules.copy true cH cH2 (by decide)) <| .seq (clear cH) <| .seq (rewind cH2) <|
  .seq (regMove cH2 cH (by decide)) <|
  .seq (clear tH) <| .seq (op0 Rules.ticks false cH tH (by decide)) <| .seq (rewind tH) (rewind cH)

theorem runs_doubleH (σ : Fin 𝕋 → WTape) (H : ℕ) (hcH : σ cH = reg (ones H)) (hcH2 : σ cH2 = emp) :
    Runs doubleH σ (· = Function.update (Function.update σ cH (reg (ones (2 * H))))
        tH ⟨[], List.replicate (2 * H) []⟩) (2 * clen (σ tH).words + 40 * H + 100) := by
  apply Runs.of_wp
  simp only [doubleH, regMove, regIn, cpy, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hcH, hcH2, emp, reg, Rules.output_ticks, Rules.output_copy, ones_append]
  have t1 := time_le Rules.copy (ones H) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.copy (ones (H + H)) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t3 := time_le Rules.ticks (ones (H + H)) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hcH, hcH2, emp, reg, two_mul]
  · simp [clen, WTape.words] at t1 t2 t3 ⊢; omega

/-! ### The inverse transform -/

/-- One inverse layer. -/
noncomputable def layerInv : Cmd 0 𝕋 :=
  .seq decS <| .seq mkShifts <| .seq blocksI <| .seq swapDI doubleH

/-- Inverse layers, one per tick of `tL`, deepest first. -/
noncomputable def invLoop : Cmd 0 𝕋 := .loop tL (.seq layerInv (skp tL tJ (by decide)))

theorem invLayer_arith {n N H P P1 K c : ℕ} (hPH : P * (H + 1) ≤ K) (hPK : P ≤ K) (hP1 : P1 ≤ K)
    (hc : c ≤ P * (N + 1)) (hnK : n + 1 ≤ K) (hHK : H ≤ K) :
    12 * (n + 1) + 60 + 1 + (P1 * (50 * N + 300) + 6 * n + 1 +
      (P * ((H + 1) * (2100 * N + 5000) + 2) + 1 +
        (2 * (K * (N + 2)) + 2 * c + (K + 2) * (6 * (N + 1) + 30) + 1 + (2 * H + 40 * H + 100)))) +
      1 + (0 + 5) + 2 ≤ 4000 * (K + 1) * (N + 2) := by
  have m1 := Nat.mul_le_mul_right (2100 * N + 5000) hPH
  have m2 := Nat.mul_le_mul_right (50 * N + 300) hP1
  have m3 := Nat.mul_le_mul_right (N + 1) hPK
  nlinarith [Nat.zero_le N, Nat.zero_le K]

theorem runs_invLoop {N k : ℕ} (hN : 0 < N) :
    ∀ (n H : ℕ) (D : List ℕ) (σ : Fin 𝕋 → WTape) (TLl : List (List Bool)),
      n ≤ k → H = 2 ^ (k - n) → D.length = 2 ^ k → (∀ d ∈ D, d < 2 ^ N + 1) →
      AluReady N σ → σ cT = emp → σ tT = emp → σ tS = emp → σ cS = reg (ones n) →
      σ tH = ⟨[], List.replicate H []⟩ → σ tD = ⟨[], rwds N D⟩ →
      σ tE = emp → σ tD2 = emp → σ tE2 = emp → σ cHN = reg (ones (N / 2)) →
      σ tU = emp → σ tV = emp → σ tO1 = emp → σ tO2 = emp → σ tJ = emp →
      σ cH = reg (ones H) → σ cH2 = emp → σ tL = ⟨TLl, List.replicate n []⟩ →
      Runs invLoop σ (· = Function.update (Function.update (Function.update (Function.update
          (Function.update σ tD ⟨[], rwds N (invIter N n k D)⟩) cS (reg (ones 0)))
          cH (reg (ones (H * 2 ^ n)))) tH ⟨[], List.replicate (H * 2 ^ n) []⟩)
          tL ⟨List.replicate n [] ++ TLl, []⟩)
        (n * (4000 * (D.length + 1) * (N + 2)))
  | 0, H, D, σ, TLl, _, _, _, _, _, _, _, _, hcS, htH, hD, _, _, _, _, _, _, _, _, _, hcH, _, htL => by
    show Runs (Cmd.loop tL _) _ _ _
    refine (Runs.loop_done (by simp [htL]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hD, hcS, hcH, htH, htL, invIter]
  | n + 1, H, D, σ, TLl, hnk, hH, hl, hDv, hr, hcT, htT, htS, hcS, htH, hD, hE, hD2, hE2, hHN, hU, hV,
      h1, h2, hJ, hcH, hcH2, htL => by
    show Runs (Cmd.loop tL _) _ _ _
    have hP0 : 0 < 2 ^ n := Nat.two_pow_pos n
    have hH0 : 0 < H := by rw [hH]; exact Nat.two_pow_pos _
    have hKH : 2 ^ k = 2 ^ n * (2 * H) := by
      rw [hH, ← pow_succ', ← pow_add]; congr 1; omega
    have hHk : 2 ^ (k - 1 - n) = H := by rw [hH]; congr 1; omega
    set E := shiftsAt N n with hEdef
    have hEl : E.length = 2 ^ n := length_shiftsAt N n
    have hEt : ∀ t ∈ E, t ≤ N := shiftsAt_le N n
    have hl' : D.length = E.length * (2 * H) := by rw [hl, hEl, hKH]
    -- decrement the depth
    have s1 := runs_decS (s := n + 1) σ hcS hr.2.2.1 hcH2
    set σ₁ := Function.update σ cS (reg (ones (n + 1 - 1))) with hσ₁
    -- the shifts
    have s2 := runs_mkShifts (N := N) (s := n) σ₁ (by tsimp [σ₁, hcT]) (by tsimp [σ₁, hHN])
      (by tsimp [σ₁, hE]) (by tsimp [σ₁, hE2]) (by tsimp [σ₁, hJ]) (by tsimp [σ₁, htS]) (by tsimp [σ₁])
    set σ₂ := Function.update σ₁ tE ⟨[], E.map ones⟩ with hσ₂
    -- the blocks
    have hr₂ : AluReady N σ₂ := ((hr.update cS _ (by decide)).update tE _ (by decide))
    have s3 := runs_blocksI hN hH0 E D σ₂ [] [] [] [] hr₂ (by tsimp [σ₂, σ₁, hcT])
      (by tsimp [σ₂, σ₁, htT]) hl' hEt hDv (by tsimp [σ₂, σ₁, htH]) (by tsimp [σ₂, σ₁, hD])
      (by tsimp [σ₂, σ₁]) (by tsimp [σ₂, σ₁, hD2, emp]) (by tsimp [σ₂, σ₁, hU]) (by tsimp [σ₂, σ₁, hV])
      (by tsimp [σ₂, σ₁, h1]) (by tsimp [σ₂, σ₁, h2]) (by tsimp [σ₂, σ₁, hJ])
    set L := layerI N H E D with hLdef
    set σ₃ := Function.update (Function.update (Function.update σ₂
        tD ⟨(rwds N D).reverse ++ [], []⟩) tE ⟨(E.map ones).reverse ++ [], []⟩)
        tD2 ⟨(rwds N L).reverse ++ [], []⟩ with hσ₃
    -- swap the data
    have s4 := runs_swapDI σ₃ (N + 1) (LD := (rwds N L).reverse ++ [])
      (fun w hw => rwds_length_le N L w (by simpa using hw)) (by tsimp [σ₃])
    set σ₄ := Function.update (Function.update (Function.update σ₃
        tD ⟨[], ((rwds N L).reverse ++ []).reverse⟩) tD2 emp) tE emp with hσ₄
    -- double the half-block size
    have s5 := runs_doubleH σ₄ H (by tsimp [σ₄, σ₃, σ₂, σ₁, hcH]) (by tsimp [σ₄, σ₃, σ₂, σ₁, hcH2])
    set σ₅ := Function.update (Function.update σ₄ cH (reg (ones (2 * H))))
        tH ⟨[], List.replicate (2 * H) []⟩ with hσ₅
    have s6 := runs_skp (a := 0) (s := tL) (j := tJ) (by decide) σ₅ (by tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, htL])
      (by tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, hJ, emp])
    set σ₆ := Function.update σ₅ tL (σ₅ tL).next with hσ₆
    have hr₆ : AluReady N σ₆ := by
      refine ((((((((hr₂.update tD _ (by decide)).update tE _ (by decide)).update tD2 _ (by decide)).update
        tD _ (by decide)).update tD2 _ (by decide)).update tE _ (by decide)).update cH _ (by decide)).update
        tH _ (by decide)).update tL _ (by decide)
    have hLl : L.length = 2 ^ k := by rw [layerI_length N H E D hl', ← hl']; exact hl
    have ih := runs_invLoop hN n (2 * H) L σ₆ ([] :: TLl) (by omega)
      (by rw [hH, ← pow_succ']; congr 1; omega) hLl (layerI_lt N H E D) hr₆
      (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hcT]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htT])
      (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htS]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁])
      (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁])
      (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁])
      (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hE2]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hHN])
      (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hU]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hV])
      (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, h1]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, h2])
      (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hJ]) (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁])
      (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hcH2])
      (by tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL, List.replicate_succ])
    refine (Runs.loop_step (by simp [htL])
      (Runs.then (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5))))
        (s6.mono (fun σ' h' => by rw [h']; exact ih) le_rfl))).mono (fun σ' h' => ?_) ?_
    · rw [h']
      have e1 : 2 * H * 2 ^ n = H * 2 ^ (n + 1) := by rw [pow_succ]; ring
      have e2 : invIter N (n + 1) k D = invIter N n k L := by
        rw [invIter, hHk]
      funext i; fin_cases i <;> tsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, e1, e2,
        htL, List.replicate_succ, hE, hD2, hE2, hcH2, hcT, hU, hV, h1, h2, replicate_append_cons]
    · have cD := clen_rwds N D
      have cE := clen_map_ones_le N E hEt
      have hnK : n + 1 ≤ 2 ^ k := hnk.trans Nat.lt_two_pow_self.le
      have hP1 : 2 ^ (n + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hnk
      have hPH : 2 ^ n * (H + 1) ≤ 2 ^ k := by rw [hKH]; nlinarith
      have hHK : H ≤ 2 ^ k := by rw [hKH]; nlinarith
      tsimp [σ₅, σ₄, σ₃, σ₂, σ₁, htH, htL, WTape.words, clen_reverse, length_rwds, hLl, cD]
      simp only [List.replicate_succ, List.head?_cons, Option.getD_some, List.length_nil, hEl, hl]
      have cH : clen (List.replicate H ([] : List Bool)) = H := by simp [clen]
      rw [cH]
      have e4 : (n + 1) * (4000 * (2 ^ k + 1) * (N + 2)) =
          n * (4000 * (2 ^ k + 1) * (N + 2)) + 4000 * (2 ^ k + 1) * (N + 2) := by ring
      rw [e4]
      have := invLayer_arith hPH (by omega) hP1 (hEl ▸ cE) hnK hHK
      linarith

end IntegerMultBounds.Schoenhage
