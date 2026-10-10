import IntegerMultBounds.Schoenhage.RingMul

/-! The residue unit inside the ring product's bank. Switching it on builds the
constants for `2^N + 1` on the multiplier's tapes from `kN = ones N`
(`runs_aluOn`); switching it off clears them (`runs_aluOff`). While it is on, a
modular subtraction or addition reads two registers of the ring product's own
and writes the result to a third (`runs_aluSub`, `runs_aluAdd`). -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-- The multiplier's tapes holding the unit's constants for `2^N + 1`, all else empty. -/
def aluBank (N : ℕ) : Fin 𝕋 → WTape :=
  Function.update (Function.update (Function.update (Function.update (fun _ => emp)
    cN (reg (ones N))) cW (reg (ones (N + 1)))) cF (reg (fword N))) c1 (reg [true])

/-- Place the unit word and the size. -/
noncomputable def aluOnA : Cmd 0 𝕌 :=
  .seq (emit [[true]] (ι c1)) <| .seq (rewind (ι c1)) <| .seq (cpy kN (ι cU) (by decide)) <|
  .seq (rewind (ι cU)) (rewind kN)

/-- Switch the unit on. -/
noncomputable def aluOn : Cmd 0 𝕌 := .seq aluOnA <| .seq (up aluSet) (clear (ι cU))

/-- Switch the unit off. -/
noncomputable def aluOff : Cmd 0 𝕌 :=
  .seq (clear (ι cN)) <| .seq (clear (ι cW)) <| .seq (clear (ι cF)) (clear (ι c1))

theorem ext_congr {τ τ' : Fin 𝕌 → WTape} (σ : Fin 𝕋 → WTape) (h : ∀ x, 64 ≤ x.val → τ x = τ' x) :
    ext τ σ = ext τ' σ := by
  funext x
  unfold ext
  split_ifs with hx
  · rfl
  · exact h x (by omega)

theorem runs_aluOn {N : ℕ} (hN : 0 < N) (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hK : τ kN = reg (ones N)) :
    Runs aluOn τ (· = ext τ (aluBank N)) (40 * N + 300) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  have s1 : Runs aluOnA τ
      (· = Function.update (Function.update τ (ι c1) (reg [true])) (ι cU) (reg (ones N))) (3 * N + 30) := by
    have h1 := hz c1; have h2 := hz cU
    apply Runs.of_wp
    simp only [aluOnA, cpy, WP, wp_op0, wp_rewind, wp_emit]
    tsimp [h1, h2, hK, emp, reg, Rules.output_copy]
    have t1 := time_le Rules.copy (ones N) (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i
      by_cases e1 : i = ι c1
      · subst e1; tsimp [h1]
      by_cases e2 : i = ι cU
      · subst e2; tsimp [h2, reg]
      by_cases e3 : i = kN
      · subst e3; tsimp [hK, reg]
      · tsimp [e1, e2, e3]
    · simp [clen] at t1 ⊢; omega
  set τ₁ := Function.update (Function.update τ (ι c1) (reg [true])) (ι cU) (reg (ones N))
  have e₁ : τ₁ ∘ ι = Function.update (Function.update (fun _ => emp) c1 (reg [true])) cU (reg (ones N)) := by
    simp only [τ₁, comp_ι_update]; rw [hc]
  have s2 : Runs (up aluSet) τ₁ (· = Function.update (ext τ (aluBank N)) (ι cU) (reg (ones N)))
      (20 * N + 160) := by
    refine (runs_up' (runs_aluSet hN (τ₁ ∘ ι) (by rw [e₁]; tsimp) (by rw [e₁]; tsimp) (by rw [e₁]; tsimp)) ?_).mono
      (fun τ' h => h) ?_
    · rw [e₁, ext_update, ext_update, ext_update, ext_update, ext_update]
      simp only [τ₁, ext_update_ι, ext_clean hc]
      funext x
      by_cases ex : x = ι cU
      · subst ex; tsimp
      · rw [Function.update_of_ne ex]
        unfold aluBank
        rw [ext_update, ext_update, ext_update, ext_update, ext_clean hc]
        by_cases e1 : x = ι cF
        · subst e1; tsimp
        by_cases e2 : x = ι cW
        · subst e2; tsimp
        by_cases e3 : x = ι cN
        · subst e3; tsimp
        by_cases e4 : x = ι c1
        · subst e4; tsimp
        · tsimp [e1, e2, e3, e4, ex]
    · rw [e₁]; tsimp [emp, WTape.words]
  refine (Runs.then s1 (Runs.then s2 (runs_clear (ι cU) _))).mono (fun τ' h => ?_) ?_
  · rw [h, Function.update_idem]
    funext x
    by_cases ex : x = ι cU
    · subst ex
      unfold aluBank ext
      tsimp [emp]
    · rw [Function.update_of_ne ex]
  · tsimp [reg, WTape.words, clen]; omega

theorem runs_aluOff {N : ℕ} (τ : Fin 𝕌 → WTape) (hA : τ ∘ ι = aluBank N) :
    Runs aluOff τ (· = ext τ (fun _ => emp)) (8 * N + 30) := by
  have h : ∀ i, τ (ι i) = aluBank N i := fun i => congrFun hA i
  have hN := h cN; have hW := h cW; have hF := h cF; have h1 := h c1
  simp only [aluBank] at hN hW hF h1
  tsimp at hN hW hF h1
  apply Runs.of_wp
  simp only [aluOff, WP, wp_clear]
  refine ⟨eq_ext (fun i => ?_) (fun x hx => ?_), ?_⟩
  · simp only [Function.update_apply, ι_injective.eq_iff]
    rw [h]; simp only [aluBank, Function.update_apply]
    split_ifs <;> first | rfl | simp_all
  · have n : ∀ i : Fin 𝕋, x ≠ ι i := fun i q => by rw [q, ι_val] at hx; have := i.isLt; omega
    rw [Function.update_of_ne (n c1), Function.update_of_ne (n cF), Function.update_of_ne (n cW),
      Function.update_of_ne (n cN)]
  · tsimp [hN, hW, hF, h1, reg, WTape.words, clen, fword]; omega

/-- A two-operand operation of the unit on registers of the ring product's own. -/
noncomputable def aluOp (op : Cmd 0 𝕋) (s₁ s₂ d : Fin 𝕌) (o₁ : Own s₁) (o₂ : Own s₂) (od : Own d) :
    Cmd 0 𝕌 :=
  .seq (regDup s₁ (ι aX) (o₁.ne aX)) <| .seq (regDup s₂ (ι aY) (o₂.ne aY)) <|
  .seq (up op) (regMove (ι aO) d (od.ne' aO))

theorem runs_aluOp (op : Cmd 0 𝕋) {s₁ s₂ d : Fin 𝕌} (o₁ : Own s₁) (o₂ : Own s₂) (od : Own d)
    (h12 : s₁ ≠ s₂) (hd1 : d ≠ s₁) (hd2 : d ≠ s₂) {N B : ℕ} {x y z : List Bool}
    (hop : Runs op (Function.update (Function.update (aluBank N) aX (reg x)) aY (reg y))
      (· = Function.update (aluBank N) aO (reg z)) B)
    (τ : Fin 𝕌 → WTape) (hA : τ ∘ ι = aluBank N) (hx : τ s₁ = reg x) (hy : τ s₂ = reg y)
    (hd : τ d = emp) :
    Runs (aluOp op s₁ s₂ d o₁ o₂ od) τ (· = Function.update τ d (reg z))
      (3 * x.length + 3 * y.length + B + 4 * z.length + 70) := by
  have h : ∀ i, τ (ι i) = aluBank N i := fun i => congrFun hA i
  have hX : τ (ι aX) = emp := by rw [h]; tsimp [aluBank]
  have hY : τ (ι aY) = emp := by rw [h]; tsimp [aluBank]
  have hO : τ (ι aO) = emp := by rw [h]; tsimp [aluBank]
  have s1 := runs_regDup (a := 0) (o₁.ne aX) τ hx hX
  have s2 := runs_regDup (a := 0) (o₂.ne aY) (Function.update τ (ι aX) (reg x)) (w := y)
    (by rw [Function.update_of_ne (o₂.ne aX), hy]) (by tsimp [hY])
  set τ₂ := Function.update (Function.update τ (ι aX) (reg x)) (ι aY) (reg y)
  have e₂ : τ₂ ∘ ι = Function.update (Function.update (aluBank N) aX (reg x)) aY (reg y) := by
    simp only [τ₂, comp_ι_update, hA]
  have s3 : Runs (up op) τ₂ (· = Function.update τ (ι aO) (reg z)) B := by
    refine runs_up' (by rw [e₂]; exact hop) ?_
    rw [ext_update]
    have e : ext τ₂ (aluBank N) = τ := by
      rw [ext_congr (τ' := τ) _ (fun x hx => ?_), ← hA, ext_self]
      have n : ∀ i : Fin 𝕋, x ≠ ι i := fun i q => by rw [q, ι_val] at hx; have := i.isLt; omega
      simp only [τ₂]; rw [Function.update_of_ne (n aY), Function.update_of_ne (n aX)]
    rw [e]
  have s4 := runs_regMove (a := 0) (od.ne' aO) (Function.update τ (ι aO) (reg z)) (w := z) (by simp)
    (by rw [Function.update_of_ne (od.ne aO), hd])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun τ' e => ?_) (by omega)
  have e' : Function.update τ (ι aO) emp = τ := by rw [← hO]; exact Function.update_eq_self _ _
  rw [e, Function.update_idem, e']

theorem aluBank_sub {N : ℕ} (hN : 0 < N) {x y : List Bool} (hlx : x.length = N + 1) (hly : y.length = N + 1)
    (hxv : bval x < 2 ^ N + 1) (hyv : bval y < 2 ^ N + 1) :
    Runs subMod (Function.update (Function.update (aluBank N) aX (reg x)) aY (reg y))
      (· = Function.update (aluBank N) aO (reg (subRes N x y))) (80 * N + 200) := by
  refine (runs_subMod hN _ ⟨by tsimp [aluBank], by tsimp [aluBank]⟩ (by tsimp) (by tsimp) hlx hly hxv hyv
    (by tsimp [aluBank]) (by tsimp [aluBank]) (by tsimp [aluBank])).mono (fun σ h => ?_) le_rfl
  rw [h]; funext i; fin_cases i <;> tsimp [aluBank]

theorem aluBank_add {N : ℕ} (hN : 0 < N) {x y : List Bool} (hlx : x.length = N + 1) (hly : y.length = N + 1)
    (hxv : bval x < 2 ^ N + 1) (hyv : bval y < 2 ^ N + 1) :
    Runs addMod (Function.update (Function.update (aluBank N) aX (reg x)) aY (reg y))
      (· = Function.update (aluBank N) aO (reg (addRes N x y))) (80 * N + 200) := by
  refine (runs_addMod hN _ ⟨by tsimp [aluBank], by tsimp [aluBank]⟩ (by tsimp) (by tsimp) hlx hly hxv hyv
    (by tsimp [aluBank]) (by tsimp [aluBank]) (by tsimp [aluBank])).mono (fun σ h => ?_) le_rfl
  rw [h]; funext i; fin_cases i <;> tsimp [aluBank]

end IntegerMultBounds.Schoenhage
