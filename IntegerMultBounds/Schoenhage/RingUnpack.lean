import IntegerMultBounds.Schoenhage.RingPack
import IntegerMultBounds.Schoenhage.RingDigit

/-! Unpacking a residue into output coefficients. Each digit `e` of the offset
residue is compared with the half `H = 2^(W-1)`: the difference is the signed
coefficient in two's complement; a negative one gets `2^s - 1` added, so that
dropping `s` bits truncates toward zero; the first `w` bits are the output
word (`runs_digitStep`). -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-- Negative coefficient: add `2^s - 1` into `tV`. -/
noncomputable def negB : Cmd 0 𝕌 :=
  .seq (back (ι tU)) <| .seq (op1 Rules.add false (ι tU) kC (ι tV) (by decide) (by decide) (by decide)) <|
  .seq (rewind kC) (rewind (ι tV))

/-- Nonnegative coefficient: copy it into `tV`. -/
noncomputable def posB : Cmd 0 𝕌 :=
  .seq (back (ι tU)) <| .seq (op0 Rules.copy false (ι tU) (ι tV) (by decide)) (rewind (ι tV))

/-- The difference with the half and its borrow. -/
noncomputable def digitA : Cmd 0 𝕌 :=
  .seq (op1 Rules.sub false (ι tD) kH (ι tU) (by decide) (by decide) (by decide)) <| .seq (rewind kH) (back (ι tU))

/-- Drop `s` bits and write the first `w` to `L`. -/
noncomputable def digitC (L : Fin 𝕌) (oL : Own L) (hL : kw ≠ L) : Cmd 0 𝕌 :=
  .seq (clear (ι tU)) <|
  .seq (op1 Rules.drop false (ι tV) kS (ι tO1) (by decide) (by decide) (by decide)) <| .seq (rewind kS) <|
  .seq (rewind (ι tO1)) <| .seq (clear (ι tV)) <|
  .seq (op1 Rules.take false kw (ι tO1) L (by decide) hL (oL.ne' tO1)) <|
  .seq (rewind kw) (clear (ι tO1))

/-- One digit to one output word. -/
noncomputable def digitStep (L : Fin 𝕌) (oL : Own L) (hL : kw ≠ L) : Cmd 0 𝕌 :=
  .seq digitA <| .seq (.cond (ι tU) negB posB) (digitC L oL hL)

/-- The word a digit step leaves in `tV`. -/
def digitWord (x hw cw : List Bool) : List Bool :=
  if (Rules.subW false x hw).2 then Rules.addW false (Rules.subW false x hw).1 cw else (Rules.subW false x hw).1

theorem runs_digitA (τ : Fin 𝕌 → WTape) {Dl Dr : List (List Bool)} {x hw : List Bool}
    (hD : τ (ι tD) = ⟨Dl, x :: Dr⟩) (hH : τ kH = reg hw) (hU : τ (ι tU) = emp) :
    Runs digitA τ (· = Function.update (Function.update τ (ι tD) ⟨x :: Dl, Dr⟩) (ι tU)
      ⟨[(Rules.subW false x hw).1], [[(Rules.subW false x hw).2]]⟩) (2 * x.length + 2 * hw.length + 20) := by
  apply Runs.of_wp
  simp only [digitA, WP, wp_op1, wp_rewind, wp_back]
  tsimp [hD, hH, hU, emp, reg, Rules.output_sub]
  have t1 := time_le Rules.sub x (fun _ => hw) hw.length (fun _ => le_rfl)
  refine ⟨?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hD, hH, hU, emp, reg] at *
  · simp [clen, WTape.words] at t1 ⊢; omega

theorem runs_digitB (τ : Fin 𝕌 → WTape) {x hw cw : List Bool} (hU : τ (ι tU) = ⟨[(Rules.subW false x hw).1],
    [[(Rules.subW false x hw).2]]⟩) (hC : τ kC = reg cw) (hV : τ (ι tV) = emp) :
    Runs (.cond (ι tU) negB posB) τ (· = Function.update τ (ι tV) (reg (digitWord x hw cw)))
      (4 * x.length + 2 * cw.length + 30) := by
  have hl := Rules.length_subW false x hw
  unfold digitWord
  cases hb : (Rules.subW false x hw).2
  · refine Runs.le (Runs.cond_false (B := 4 * x.length + 2 * cw.length + 29) (by rw [hU, hb, startsOne_mk]; simp) ?_)
      (by omega)
    apply Runs.of_wp
    simp only [posB, WP, wp_op0, wp_rewind, wp_back]
    tsimp [hU, hV, hb, emp, reg, Rules.output_copy]
    have t1 := time_le Rules.copy (Rules.subW false x hw).1 (fun j => j.elim0) 0 (fun j => j.elim0)
    refine ⟨?_, ?_⟩
    · funext i
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [hU, hV, hb, emp, reg] at *
    · simp [clen, WTape.words, hl] at t1 ⊢; omega
  · refine Runs.le (Runs.cond_true (B := 4 * x.length + 2 * cw.length + 29) (by rw [hU, hb, startsOne_mk]) ?_)
      (by omega)
    apply Runs.of_wp
    simp only [negB, WP, wp_op1, wp_rewind, wp_back]
    tsimp [hU, hV, hC, hb, emp, reg, Rules.output_add]
    have t1 := time_le Rules.add (Rules.subW false x hw).1 (fun _ => cw) cw.length (fun _ => le_rfl)
    refine ⟨?_, ?_⟩
    · funext i
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [hU, hV, hC, hb, emp, reg] at *
    · simp [clen, WTape.words, hl, Rules.length_addW] at t1 ⊢; omega

theorem runs_digitC {L : Fin 𝕌} (oL : Own L) (hL : kw ≠ L) (τ : Fin 𝕌 → WTape) {d y : List Bool} {b : Bool}
    {s w : ℕ} {Ll : List (List Bool)} (hU : τ (ι tU) = ⟨[d], [[b]]⟩) (hV : τ (ι tV) = reg y)
    (hS : τ kS = reg (ones s)) (hw : τ kw = reg (ones w)) (hO : τ (ι tO1) = emp) (hLt : τ L = ⟨Ll, []⟩) :
    Runs (digitC L oL hL) τ (· = Function.update (Function.update (Function.update τ (ι tU) emp) (ι tV) emp) L
      ⟨Rules.fit w (y.drop s) :: Ll, []⟩) (2 * d.length + 8 * y.length + 3 * s + 4 * w + 60) := by
  have n1 := oL.ne' tU; have n2 := oL.ne' tV; have n3 := oL.ne' tO1
  have m1 : kS ≠ L := fun e => by rw [← e] at hLt; rw [hLt] at hS; cases hS
  apply Runs.of_wp
  simp only [digitC, WP, wp_op1, wp_rewind, wp_clear]
  tsimp [hU, hV, hS, hw, hO, hLt, emp, reg, Rules.output_drop, Rules.output_take, n1, n2, n3, hL, hL.symm,
    m1, m1.symm, oL.ne tU, oL.ne tV, oL.ne tO1]
  have t1 := time_le Rules.drop y (fun _ => ones s) s (fun _ => by simp)
  have t2 := time_le Rules.take (ones w) (fun _ => y.drop s) y.length (fun _ => by simp)
  refine ⟨?_, ?_⟩
  · funext i
    by_cases a1 : i = L
    · subst a1; tsimp [n1, n2, n3, n1.symm, n2.symm, n3.symm, hL.symm, m1.symm]
    · simp only [Function.update_apply, a1, ite_false]
      split_ifs <;> (try subst_vars) <;> tsimp [hU, hV, hS, hw, hO, emp, reg] at *
  · simp [clen, WTape.words] at t1 t2 ⊢; omega

theorem runs_digitStep {L : Fin 𝕌} (oL : Own L) (hL : kw ≠ L) (τ : Fin 𝕌 → WTape)
    {Dl Dr Ll : List (List Bool)} {x hw cw : List Bool} {s w : ℕ}
    (hD : τ (ι tD) = ⟨Dl, x :: Dr⟩) (hH : τ kH = reg hw) (hC : τ kC = reg cw) (hS : τ kS = reg (ones s))
    (hwr : τ kw = reg (ones w)) (hU : τ (ι tU) = emp) (hV : τ (ι tV) = emp) (hO : τ (ι tO1) = emp)
    (hLt : τ L = ⟨Ll, []⟩) :
    Runs (digitStep L oL hL) τ (· = Function.update (Function.update τ (ι tD) ⟨x :: Dl, Dr⟩) L
      ⟨Rules.fit w ((digitWord x hw cw).drop s) :: Ll, []⟩)
      (20 * x.length + 2 * hw.length + 4 * cw.length + 3 * s + 4 * w + 140) := by
  have n1 := oL.ne' tU; have n2 := oL.ne' tV; have n3 := oL.ne' tO1; have n4 := oL.ne' tD
  have m1 : kH ≠ L := fun e => by rw [← e] at hLt; rw [hLt] at hH; cases hH
  have m2 : kC ≠ L := fun e => by rw [← e] at hLt; rw [hLt] at hC; cases hC
  have m3 : kS ≠ L := fun e => by rw [← e] at hLt; rw [hLt] at hS; cases hS
  have s1 := runs_digitA τ hD hH hU
  set τ₁ := Function.update (Function.update τ (ι tD) ⟨x :: Dl, Dr⟩) (ι tU)
      ⟨[(Rules.subW false x hw).1], [[(Rules.subW false x hw).2]]⟩
  have s2 := runs_digitB τ₁ (x := x) (hw := hw) (cw := cw) (by simp [τ₁]) (by tsimp [τ₁, hC]) (by tsimp [τ₁, hV])
  set τ₂ := Function.update τ₁ (ι tV) (reg (digitWord x hw cw))
  have hdw : (digitWord x hw cw).length ≤ x.length + 1 := by
    unfold digitWord; split_ifs <;> simp [Rules.length_subW, Rules.length_addW]
  have s3 := runs_digitC oL hL τ₂ (d := (Rules.subW false x hw).1) (b := (Rules.subW false x hw).2)
    (y := digitWord x hw cw) (s := s) (w := w) (Ll := Ll) (by tsimp [τ₂, τ₁]) (by tsimp [τ₂])
    (by tsimp [τ₂, τ₁, hS, m3.symm]) (by tsimp [τ₂, τ₁, hwr, hL.symm]) (by tsimp [τ₂, τ₁, hO])
    (by tsimp [τ₂, τ₁, hLt, n1.symm, n2.symm, n4.symm])
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ' h => ?_) ?_
  · rw [h]
    funext i
    by_cases a1 : i = L
    · subst a1; tsimp [n1, n2, n3, n4, n1.symm, n2.symm, n3.symm, n4.symm]
    · simp only [τ₂, τ₁, Function.update_apply, a1, ite_false]
      split_ifs <;> (try subst_vars) <;> tsimp [hU, hV, emp] at *
  · simp [Rules.length_subW] at hdw ⊢; omega

/-! ### Values -/

theorem fit_len {n : ℕ} {x : List Bool} (h : x.length = n) : Rules.fit n x = x := h ▸ Rules.fit_of_length x

/-- The output word of a digit. -/
def outWord (Wd s w e : ℕ) : List Bool :=
  Rules.fit w ((digitWord (bits (Wd + 1) e) (bits (Wd + 1) (2 ^ (Wd - 1))) (bits (Wd + 1) (2 ^ s - 1))).drop s)

theorem bval_digitWord {Wd s e : ℕ} (hW : 1 ≤ Wd) (he : e < 2 ^ Wd) (hs : s ≤ Wd) :
    bval (digitWord (bits (Wd + 1) e) (bits (Wd + 1) (2 ^ (Wd - 1))) (bits (Wd + 1) (2 ^ s - 1))) =
      digitVal Wd s e := by
  have p1 : 2 ^ Wd = 2 * 2 ^ (Wd - 1) := by rw [← pow_succ']; congr 1; omega
  have p2 : 2 ^ (Wd + 1) = 2 * 2 ^ Wd := by rw [pow_succ]; ring
  have p3 : 2 ^ s ≤ 2 ^ Wd := Nat.pow_le_pow_right (by norm_num) hs
  have hx : bval (bits (Wd + 1) e) = e := by rw [bval_bits, Nat.mod_eq_of_lt (by omega)]
  have hh : bval (bits (Wd + 1) (2 ^ (Wd - 1))) = 2 ^ (Wd - 1) := by
    rw [bval_bits, Nat.mod_eq_of_lt (by omega)]
  have hc : bval (bits (Wd + 1) (2 ^ s - 1)) = 2 ^ s - 1 := by
    rw [bval_bits, Nat.mod_eq_of_lt (by have := Nat.two_pow_pos s; omega)]
  have key := Rules.bval_subW false (bits (Wd + 1) e) (bits (Wd + 1) (2 ^ (Wd - 1)))
  rw [length_bits, fit_len (by simp), hx, hh] at key
  have hb := subW_borrow (bits (Wd + 1) e) (bits (Wd + 1) (2 ^ (Wd - 1))) (by simp)
  rw [hx, hh] at hb
  have hl := bval_lt (Rules.subW false (bits (Wd + 1) e) (bits (Wd + 1) (2 ^ (Wd - 1)))).1
  rw [Rules.length_subW, length_bits] at hl
  generalize hD : (Rules.subW false (bits (Wd + 1) e) (bits (Wd + 1) (2 ^ (Wd - 1)))) = D at *
  have hd : bval D.1 + 2 ^ (Wd - 1) = e + 2 ^ (Wd + 1) * D.2.toNat := by
    have : ((bval D.1 + 2 ^ (Wd - 1) : ℕ) : ℤ) = ((e + 2 ^ (Wd + 1) * D.2.toNat : ℕ) : ℤ) := by
      simp only [Bool.toNat_false, Nat.cast_zero, sub_zero] at key; push_cast at key ⊢; linarith
    exact_mod_cast this
  unfold digitWord digitVal
  rw [hD]
  by_cases hle : 2 ^ (Wd - 1) ≤ e
  · have h2 : D.2 = false := by rw [hb]; simp; omega
    rw [h2] at hd ⊢
    simp only [Bool.false_eq_true, ite_false, hle, ite_true, Bool.toNat_false] at hd ⊢
    omega
  · have h2 : D.2 = true := by rw [hb]; simp; omega
    rw [h2] at hd ⊢
    simp only [ite_true, hle, ite_false, Bool.toNat_true] at hd ⊢
    rw [Rules.bval_addW, ← hD, Rules.length_subW, length_bits, fit_len (by simp), hc, hD]
    simp only [Bool.false_eq_true, ite_false, add_zero]
    omega

theorem outWord_eq {Wd s w e : ℕ} (hW : 1 ≤ Wd) (he : e < 2 ^ Wd) (hw : 1 ≤ w) (hws : w + s ≤ Wd + 1) :
    outWord Wd s w e = tw w (trunc0 s ((e : ℤ) - 2 ^ (Wd - 1))) := by
  rw [outWord, Rules.fit_eq_bits, Rules.bval_drop', bval_digitWord hW he (by omega), tw_digit hW he hws]

/-! ### All digits -/

/-- Every digit of `tD` to `L`. -/
noncomputable def digitLoop (L : Fin 𝕌) (oL : Own L) (hL : kw ≠ L) : Cmd 0 𝕌 := .loop (ι tD) (digitStep L oL hL)

theorem runs_digitLoop {L : Fin 𝕌} (oL : Own L) (hL : kw ≠ L) {Wd s w : ℕ} :
    ∀ (es : List ℕ) (τ : Fin 𝕌 → WTape) (Dl Ll : List (List Bool)),
      τ (ι tD) = ⟨Dl, es.map (bits (Wd + 1))⟩ → τ kH = reg (bits (Wd + 1) (2 ^ (Wd - 1))) →
      τ kC = reg (bits (Wd + 1) (2 ^ s - 1)) → τ kS = reg (ones s) → τ kw = reg (ones w) →
      τ (ι tU) = emp → τ (ι tV) = emp → τ (ι tO1) = emp → τ L = ⟨Ll, []⟩ →
      Runs (digitLoop L oL hL) τ (· = Function.update (Function.update τ (ι tD)
        ⟨(es.map (bits (Wd + 1))).reverse ++ Dl, []⟩) L ⟨(es.map (outWord Wd s w)).reverse ++ Ll, []⟩)
        (es.length * (26 * Wd + 3 * s + 4 * w + 170))
  | [], τ, Dl, Ll, hD, _, _, _, _, _, _, _, hLt => by
    refine (Runs.loop_done (by simp [hD]) rfl).mono (fun τ' h => ?_) (by simp)
    rw [← h]; funext x
    by_cases a1 : x = L <;> by_cases a2 : x = ι tD <;> simp_all [Function.update_apply]
  | e :: es, τ, Dl, Ll, hD, hH, hC, hS, hw, hU, hV, hO, hLt => by
    have n4 := oL.ne' tD
    have m1 : kH ≠ L := fun q => by rw [← q] at hLt; rw [hLt] at hH; cases hH
    have m2 : kC ≠ L := fun q => by rw [← q] at hLt; rw [hLt] at hC; cases hC
    have m3 : kS ≠ L := fun q => by rw [← q] at hLt; rw [hLt] at hS; cases hS
    have s1 := runs_digitStep oL hL τ (Dl := Dl) (Dr := es.map (bits (Wd + 1))) (Ll := Ll) (by simpa using hD)
      hH hC hS hw hU hV hO hLt
    set τ₁ := Function.update (Function.update τ (ι tD) ⟨bits (Wd + 1) e :: Dl, es.map (bits (Wd + 1))⟩) L
      ⟨Rules.fit w ((digitWord (bits (Wd + 1) e) (bits (Wd + 1) (2 ^ (Wd - 1))) (bits (Wd + 1) (2 ^ s - 1))).drop s)
        :: Ll, []⟩
    have ih := runs_digitLoop oL hL (Wd := Wd) (s := s) (w := w) es τ₁ (bits (Wd + 1) e :: Dl)
      (outWord Wd s w e :: Ll)
      (by simp [τ₁, n4]) (by tsimp [τ₁, hH, m1, m1.symm]) (by tsimp [τ₁, hC, m2, m2.symm])
      (by tsimp [τ₁, hS, m3, m3.symm]) (by tsimp [τ₁, hw, hL, hL.symm])
      (by tsimp [τ₁, hU, oL.ne tU, oL.ne' tU]) (by tsimp [τ₁, hV, oL.ne tV, oL.ne' tV])
      (by tsimp [τ₁, hO, oL.ne tO1, oL.ne' tO1]) (by simp [τ₁, outWord])
    refine (Runs.loop_step (by simp [hD]) ((s1.mono (fun τ' h => by rw [h]; exact ih) le_rfl))).mono
      (fun τ' h => ?_) ?_
    · rw [h]; funext x
      by_cases a1 : x = L <;> by_cases a2 : x = ι tD <;> simp_all [τ₁, Function.update_apply]
    · simp only [List.length_cons, length_bits]; nlinarith

/-- A residue register to output words on `L`. -/
noncomputable def unpack (src L : Fin 𝕌) (os : Own src) (oL : Own L) (hL : kw ≠ L) : Cmd 0 𝕌 :=
  .seq (regDup src (ι sX) (os.ne sX)) <| .seq (regDup kR (ι cR) (by decide)) <| .seq (up splitOp) <|
  .seq (clear (ι cR)) <| .seq (rewind (ι tD)) <| .seq (digitLoop L oL hL) (clear (ι tD))

set_option maxHeartbeats 1000000 in
theorem runs_unpack {src L : Fin 𝕌} (os : Own src) (oL : Own L) (hL : kw ≠ L) (hsL : src ≠ L) {N Wd r s w : ℕ}
    (hr : 1 ≤ r) (hN : N = Wd * r) (τ : Fin 𝕌 → WTape) (hA : τ ∘ ι = aluBank N) {v : List Bool}
    (hv : v.length = N + 1) (hs : τ src = reg v) (hR : τ kR = reg (Rules.ruler Wd (Wd + 1) r))
    (hH : τ kH = reg (bits (Wd + 1) (2 ^ (Wd - 1)))) (hC : τ kC = reg (bits (Wd + 1) (2 ^ s - 1)))
    (hS : τ kS = reg (ones s)) (hw : τ kw = reg (ones w)) {Ll : List (List Bool)} (hLt : τ L = ⟨Ll, []⟩) :
    Runs (unpack src L os oL hL) τ (· = Function.update τ L
      ⟨((pieces Wd r (bval v)).map (outWord Wd s w)).reverse ++ Ll, []⟩)
      (r * (26 * Wd + 3 * s + 4 * w + 170) + 24 * r * (Wd + 2) + 20 * N + 200) := by
  have hz : ∀ i, τ (ι i) = aluBank N i := fun i => congrFun hA i
  have hX : τ (ι sX) = emp := by rw [hz]; tsimp [aluBank]
  have hcR : τ (ι cR) = emp := by rw [hz]; tsimp [aluBank]
  have hD : τ (ι tD) = emp := by rw [hz]; tsimp [aluBank]
  have hU : τ (ι tU) = emp := by rw [hz]; tsimp [aluBank]
  have hV : τ (ι tV) = emp := by rw [hz]; tsimp [aluBank]
  have hO : τ (ι tO1) = emp := by rw [hz]; tsimp [aluBank]
  have m1 : kH ≠ L := fun q => by rw [← q] at hLt; rw [hLt] at hH; cases hH
  have m2 : kC ≠ L := fun q => by rw [← q] at hLt; rw [hLt] at hC; cases hC
  have m3 : kS ≠ L := fun q => by rw [← q] at hLt; rw [hLt] at hS; cases hS
  have m4 : kR ≠ L := fun q => by rw [← q] at hLt; rw [hLt] at hR; cases hR
  set es := pieces Wd r (bval v)
  have s1 := runs_regDup (a := 0) (os.ne sX) τ hs hX
  have s2 := runs_regDup (a := 0) (show kR ≠ ι cR by decide) (Function.update τ (ι sX) (reg v)) (w := Rules.ruler Wd (Wd + 1) r)
    (by tsimp [hR]) (by tsimp [hcR])
  set τ₂ := Function.update (Function.update τ (ι sX) (reg v)) (ι cR) (reg (Rules.ruler Wd (Wd + 1) r))
  have e₂ : τ₂ ∘ ι = Function.update (Function.update (aluBank N) sX (reg v)) cR (reg (Rules.ruler Wd (Wd + 1) r)) := by
    simp only [τ₂, comp_ι_update, hA]
  have hbv : bval v < 2 ^ (Wd * r + 1) := by rw [← hN, ← hv]; exact bval_lt v
  have s3 := runs_splitOp (M := Wd) (W := Wd + 1) (K := r) le_rfl (by omega) (τ₂ ∘ ι) hbv (Dl := [])
    (by rw [e₂]; tsimp) (by rw [e₂]; tsimp) (by rw [e₂]; tsimp [aluBank, emp])
  set τ₃ := Function.update (Function.update τ₂ (ι sX) emp) (ι tD) ⟨(es.map (bits (Wd + 1))).reverse ++ [], []⟩
  have s3' : Runs (up splitOp) τ₂ (· = τ₃)
      (2 * (Rules.ruler Wd (Wd + 1) r).length + 3 * v.length + 20) := by
    refine runs_up' s3 ?_
    rw [ext_update, ext_update, ext_self]
  have s4 := runs_clear (a := 0) (ι cR) τ₃
  have s5 := runs_rewind (a := 0) (ι tD) (Function.update τ₃ (ι cR) ⟨[], []⟩)
  set τ₅ := Function.update τ (ι tD) ⟨[], es.map (bits (Wd + 1))⟩
  have e₅ : Function.update (Function.update τ₃ (ι cR) ⟨[], []⟩) (ι tD)
      ⟨[], (Function.update τ₃ (ι cR) ⟨[], []⟩ (ι tD)).left.reverse ++
        (Function.update τ₃ (ι cR) ⟨[], []⟩ (ι tD)).right⟩ = τ₅ := by
    funext x
    simp only [τ₅, τ₃, τ₂, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hX, hcR, emp] at *
  have s6 := runs_digitLoop oL hL (Wd := Wd) (s := s) (w := w) es τ₅ [] Ll (by simp [τ₅])
    (by tsimp [τ₅, hH]) (by tsimp [τ₅, hC]) (by tsimp [τ₅, hS]) (by tsimp [τ₅, hw])
    (by tsimp [τ₅, hU]) (by tsimp [τ₅, hV]) (by tsimp [τ₅, hO]) (by simp [τ₅, oL.ne tD, hLt])
  have s7 := runs_clear (a := 0) (ι tD) (Function.update (Function.update τ₅ (ι tD)
      ⟨(es.map (bits (Wd + 1))).reverse ++ [], []⟩) L ⟨(es.map (outWord Wd s w)).reverse ++ Ll, []⟩)
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3' (Runs.then s4 (Runs.then (s5.mono (fun _ h => h.trans e₅)
    le_rfl) (Runs.then s6 s7)))))).mono (fun τ' h => ?_) ?_
  · rw [h]; funext x
    by_cases a1 : x = L
    · subst a1; simp [τ₅, oL.ne tD]
    · simp only [τ₅, Function.update_apply, a1, ite_false]
      split_ifs <;> (try subst_vars) <;> tsimp [hD, emp] at *
  · have l1 := length_ruler (show Wd + 1 ≤ Wd + 1 from le_rfl) r
    have l2 : es.length = r := length_pieces _ _ _
    have l3 : clen (es.map (bits (Wd + 1))) = r * (Wd + 1 + 1) := by
      rw [clen_map_eq (w := Wd + 1) es (fun _ _ => by simp), l2]
    tsimp [τ₅, τ₃, τ₂, oL.ne tD, oL.ne' tD, WTape.words, clen_reverse, clen_append, l3, l2, hv, reg, hcR, hD,
      emp, clen_cons, clen_nil]
    nlinarith [l1]

end IntegerMultBounds.Schoenhage
