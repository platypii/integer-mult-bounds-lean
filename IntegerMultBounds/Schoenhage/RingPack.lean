import IntegerMultBounds.Schoenhage.RingAlu
import IntegerMultBounds.Schoenhage.RingWords

/-! Packing one component of a polynomial into a residue. The input tape
holds the coefficient pairs, real word then imaginary word. One pass flips
the top bit of every real (or every imaginary) word onto the multiplier's
coefficient tape; the shifted sum of these digits is one word, cut to
`N + 1` bits; subtracting the offset word gives the residue
(`runs_pack`). -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

variable {t : ℕ}

theorem runs_flip {s d : Fin t} (h : s ≠ d) (σ : Fin t → WTape) {L R C : List (List Bool)} {w : List Bool}
    (hs : σ s = ⟨L, w :: R⟩) (hw : w ≠ []) (hd : σ d = ⟨C, []⟩) :
    Runs (a := 0) (op0 Rules.flip false s d h) σ
      (· = Function.update (Function.update σ s ⟨w :: L, R⟩) d ⟨flipLast w :: C, []⟩) (w.length + 7) := by
  apply Runs.of_wp
  rw [wp_op0]
  have ho : output Rules.flip (σ s).cur (fun j => j.elim0) = syms [flipLast w] := by
    rw [hs]; exact Rules.output_flip w _ hw
  rw [ho, parse_syms]
  refine ⟨⟨by simp [hs], by simp [hd], rfl, by simp⟩, ?_, ?_⟩
  · simp [hs, hd]
  · have hc : (σ s).cur = w := by simp [hs]
    have := time_le Rules.flip w (fun j => j.elim0) 0 (fun j => j.elim0)
    rw [hc]; simp at this; omega

/-- The coefficient pairs as words: real, imaginary, real, imaginary, … -/
def flat (ps : List (List Bool × List Bool)) : List (List Bool) := ps.flatMap fun p => [p.1, p.2]

@[simp] theorem flat_nil : flat [] = [] := rfl
@[simp] theorem flat_cons (p : List Bool × List Bool) (ps : List (List Bool × List Bool)) :
    flat (p :: ps) = p.1 :: p.2 :: flat ps := rfl

/-- The real (`odd = false`) or imaginary (`odd = true`) word of a pair. -/
def pick (odd : Bool) (p : List Bool × List Bool) : List Bool := if odd then p.2 else p.1

/-- One pair: flip the chosen word onto the coefficient tape, step past the other. -/
noncomputable def packBody (src : Fin 𝕌) (o : Own src) : Bool → Cmd 0 𝕌
  | false => .seq (op0 Rules.flip false src (ι tC) (o.ne tC)) (skp src (ι tU) (o.ne tU))
  | true => .seq (skp src (ι tU) (o.ne tU)) (op0 Rules.flip false src (ι tC) (o.ne tC))

theorem runs_packBody {src : Fin 𝕌} (o : Own src) (odd : Bool) (τ : Fin 𝕌 → WTape)
    {L R C : List (List Bool)} {p : List Bool × List Bool} (h1 : p.1 ≠ []) (h2 : p.2 ≠ [])
    (hs : τ src = ⟨L, p.1 :: p.2 :: R⟩) (hC : τ (ι tC) = ⟨C, []⟩) (hU : τ (ι tU) = emp) :
    Runs (packBody src o odd) τ (· = Function.update (Function.update τ src ⟨p.2 :: p.1 :: L, R⟩)
      (ι tC) ⟨flipLast (pick odd p) :: C, []⟩) (p.1.length + p.2.length + 13) := by
  have n1 := o.ne tC; have n2 := o.ne tU
  have n3 : ι tU ≠ ι tC := by decide
  cases odd with
  | false =>
    have s1 := runs_flip n1 τ hs h1 hC
    have s2 := runs_skp (a := 0) n2 (Function.update (Function.update τ src ⟨p.1 :: L, p.2 :: R⟩) (ι tC)
      ⟨flipLast p.1 :: C, []⟩) (by rw [Function.update_of_ne n1]; simp)
      (by rw [Function.update_of_ne n3, Function.update_of_ne n2.symm, hU]; rfl)
    refine (Runs.then s1 s2).mono (fun τ' h => ?_) ?_
    · rw [h]; funext x
      by_cases a1 : x = src <;> by_cases a2 : x = ι tC <;> simp_all [Function.update_apply, pick]
    · rw [Function.update_of_ne n1, Function.update_self]; simp; omega
  | true =>
    have s1 := runs_skp (a := 0) n2 τ (by simp [hs]) (by rw [hU]; rfl)
    have s2 := runs_flip n1 (Function.update τ src (τ src).next) (L := p.1 :: L) (R := R) (w := p.2)
      (by simp [hs]) h2 (by rw [Function.update_of_ne n1.symm, hC])
    refine (Runs.then s1 s2).mono (fun τ' h => ?_) ?_
    · rw [h]; funext x
      by_cases a1 : x = src <;> by_cases a2 : x = ι tC <;> simp_all [Function.update_apply, pick]
    · simp [hs]; omega

/-- Every pair of the source. -/
noncomputable def packLoop (src : Fin 𝕌) (o : Own src) (odd : Bool) : Cmd 0 𝕌 := .loop src (packBody src o odd)

theorem runs_packLoop {src : Fin 𝕌} (o : Own src) (odd : Bool) {w : ℕ} :
    ∀ (ps : List (List Bool × List Bool)) (τ : Fin 𝕌 → WTape) (L C : List (List Bool)),
      (∀ p ∈ ps, p.1.length = w ∧ p.2.length = w) → 0 < w →
      τ src = ⟨L, flat ps⟩ → τ (ι tC) = ⟨C, []⟩ → τ (ι tU) = emp →
      Runs (packLoop src o odd) τ (· = Function.update (Function.update τ src ⟨(flat ps).reverse ++ L, []⟩)
        (ι tC) ⟨(ps.map fun p => flipLast (pick odd p)).reverse ++ C, []⟩) (ps.length * (2 * w + 15))
  | [], τ, L, C, _, _, hs, hC, _ => by
    refine (Runs.loop_done (by simp [hs]) rfl).mono (fun τ' h => ?_) (by simp)
    rw [← h]; funext x
    by_cases a1 : x = src <;> by_cases a2 : x = ι tC <;> simp_all [Function.update_apply]
  | p :: ps, τ, L, C, hw, hw0, hs, hC, hU => by
    have hp := hw p (by simp)
    have h1 : p.1 ≠ [] := by intro e; rw [e] at hp; simp at hp; omega
    have h2 : p.2 ≠ [] := by intro e; rw [e] at hp; simp at hp; omega
    have s1 := runs_packBody o odd τ h1 h2 hs hC hU
    set τ₁ := Function.update (Function.update τ src ⟨p.2 :: p.1 :: L, flat ps⟩) (ι tC)
      ⟨flipLast (pick odd p) :: C, []⟩
    have ih := runs_packLoop o odd ps τ₁ (p.2 :: p.1 :: L) (flipLast (pick odd p) :: C)
      (fun q hq => hw q (by simp [hq])) hw0 (by simp [τ₁, o.ne tC]) (by simp [τ₁])
      (by simp [τ₁, Function.update_of_ne (show ι tU ≠ ι tC by decide), (o.ne tU).symm, hU])
    refine (Runs.loop_step (by simp [hs]) ((s1.mono (fun τ' h => by rw [h]; exact ih) le_rfl))).mono
      (fun τ' h => ?_) ?_
    · rw [h]; funext x
      by_cases a1 : x = src <;> by_cases a2 : x = ι tC <;> simp_all [τ₁, Function.update_apply]
    · simp only [List.length_cons]; rw [hp.1, hp.2]; ring_nf; omega

/-! ### The whole component -/

theorem clen_map_eq {α : Type} {f : α → List Bool} {w : ℕ} :
    ∀ l : List α, (∀ x ∈ l, (f x).length = w) → clen (l.map f) = l.length * (w + 1)
  | [], _ => by simp
  | x :: l, h => by
    rw [List.map_cons, clen_cons, clen_map_eq l (fun y hy => h y (by simp [hy])), h x (by simp)]
    simp [List.length_cons]; ring

theorem comp_ι_update_own {s : Fin 𝕌} (o : Own s) (τ : Fin 𝕌 → WTape) (v : WTape) :
    Function.update τ s v ∘ ι = τ ∘ ι := by
  funext i; simp [Function.update_of_ne (o.ne' i)]

/-- Flip the chosen words onto the coefficient tape and load the window widths. -/
noncomputable def packA (src : Fin 𝕌) (o : Own src) (odd : Bool) : Cmd 0 𝕌 :=
  .seq (packLoop src o odd) <| .seq (rewind src) <| .seq (rewind (ι tC)) <|
  .seq (regDup kW (ι cM) (by decide)) (regDup kW (ι cWA) (by decide))

theorem runs_packA {src : Fin 𝕌} (o : Own src) (hW : src ≠ kW) (odd : Bool) {w Wd : ℕ}
    (ps : List (List Bool × List Bool)) (hw : ∀ p ∈ ps, p.1.length = w ∧ p.2.length = w) (hw0 : 0 < w)
    (τ : Fin 𝕌 → WTape) (hs : τ src = ⟨[], flat ps⟩) (hC : τ (ι tC) = emp) (hU : τ (ι tU) = emp)
    (hM : τ (ι cM) = emp) (hA : τ (ι cWA) = emp) (hK : τ kW = reg (ones Wd)) :
    Runs (packA src o odd) τ (· = Function.update (Function.update (Function.update τ
      (ι tC) ⟨[], ps.map fun p => flipLast (pick odd p)⟩) (ι cM) (reg (ones Wd))) (ι cWA) (reg (ones Wd)))
      (ps.length * (4 * w + 20) + 2 * clen (flat ps) + 6 * Wd + 60) := by
  have s1 := runs_packLoop o odd ps τ [] [] hw hw0 hs (by rw [hC]; rfl) hU
  set ds := ps.map fun p => flipLast (pick odd p)
  set τ₁ := Function.update (Function.update τ src ⟨(flat ps).reverse ++ [], []⟩) (ι tC) ⟨ds.reverse ++ [], []⟩
  have s2 := runs_rewind (a := 0) src τ₁
  have s3 := runs_rewind (a := 0) (ι tC) (Function.update τ₁ src ⟨[], (τ₁ src).left.reverse ++ (τ₁ src).right⟩)
  set τ₃ := Function.update τ (ι tC) ⟨[], ds⟩
  have e₃ : Function.update (Function.update τ₁ src ⟨[], (τ₁ src).left.reverse ++ (τ₁ src).right⟩) (ι tC)
      ⟨[], (Function.update τ₁ src ⟨[], (τ₁ src).left.reverse ++ (τ₁ src).right⟩ (ι tC)).left.reverse ++
        (Function.update τ₁ src ⟨[], (τ₁ src).left.reverse ++ (τ₁ src).right⟩ (ι tC)).right⟩ = τ₃ := by
    funext x
    by_cases a1 : x = src <;> by_cases a2 : x = ι tC <;> simp_all [τ₁, τ₃, Function.update_apply, o.ne tC]
  have s4 := runs_regDup (a := 0) (show kW ≠ ι cM by decide) τ₃ (w := ones Wd) (by tsimp [τ₃, hK])
    (by tsimp [τ₃, hM])
  have s5 := runs_regDup (a := 0) (show kW ≠ ι cWA by decide) (Function.update τ₃ (ι cM) (reg (ones Wd)))
    (w := ones Wd) (by tsimp [τ₃, hK]) (by tsimp [τ₃, hA])
  refine (Runs.then s1 (Runs.then s2 (Runs.then (s3.mono (fun _ h => h.trans e₃) le_rfl)
    (Runs.then s4 s5)))).mono (fun τ' h => h) ?_
  have c1 : clen ds = ps.length * (w + 1) := by
    apply clen_map_eq; intro p hp; have := hw p hp
    have h1 : p.1 ≠ [] := by intro e; rw [e] at this; simp at this; omega
    have h2 : p.2 ≠ [] := by intro e; rw [e] at this; simp at this; omega
    cases odd <;> simp [pick, length_flipLast h1, length_flipLast h2, this.1, this.2]
  have e : ps.length * (4 * w + 20) = ps.length * (2 * w + 15) + 2 * (ps.length * (w + 1)) + 3 * ps.length := by
    ring
  simp [τ₁, clen_reverse, clen_append, c1, Function.update_of_ne (o.ne tC).symm,
    Function.update_of_ne (o.ne tC)]
  omega

/-- Cut the sum to `N + 1` bits into `xP` and clear the window's tapes. -/
noncomputable def packD : Cmd 0 𝕌 :=
  .seq (rewind (ι sO)) <| .seq (op1 Rules.take false (ι cW) (ι sO) xP (by decide) (by decide) (by decide)) <|
  .seq (rewind (ι cW)) <| .seq (rewind xP) <| .seq (clear (ι sO)) <| .seq (clear (ι tC)) <|
  .seq (clear (ι cM)) (clear (ι cWA))

theorem runs_packD {N : ℕ} (τ : Fin 𝕌 → WTape) {z : List Bool} {C M A : WTape}
    (hO : τ (ι sO) = emp) (hC : τ (ι tC) = emp) (hM : τ (ι cM) = emp) (hA : τ (ι cWA) = emp)
    (hP : τ xP = emp) (hW : τ (ι cW) = reg (ones (N + 1))) :
    Runs packD (Function.update (Function.update (Function.update (Function.update τ (ι tC) C) (ι cM) M)
        (ι cWA) A) (ι sO) ⟨[z], []⟩)
      (· = Function.update τ xP (reg (Rules.fit (N + 1) z)))
      (2 * clen C.words + 2 * clen M.words + 2 * clen A.words + 6 * z.length + 6 * N + 60) := by
  apply Runs.of_wp
  simp only [packD, WP, wp_op1, wp_rewind, wp_clear]
  tsimp [hO, hW, hP, emp, reg, Rules.output_take]
  have t1 := time_le Rules.take (ones (N + 1)) (fun _ => z) z.length (fun _ => le_rfl)
  refine ⟨?_, ?_⟩
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hO, hC, hM, hA, hW, hP, emp, reg] at *
  · simp [clen, WTape.words] at t1 ⊢; omega

/-- One component of a polynomial as a residue in `dst`. -/
noncomputable def pack (src dst : Fin 𝕌) (o : Own src) (od : Own dst) (odd : Bool) : Cmd 0 𝕌 :=
  .seq (packA src o odd) <| .seq (up winSum) <| .seq packD <|
  .seq (aluOp subMod xP kI dst (by unfold Own; decide) (by unfold Own; decide) od) (clear xP)

/-- The digits of the chosen words. -/
def digits (odd : Bool) (ps : List (List Bool × List Bool)) : List ℕ :=
  ps.map fun p => bval (flipLast (pick odd p))

theorem pick_length {w : ℕ} {ps : List (List Bool × List Bool)} (hw : ∀ p ∈ ps, p.1.length = w ∧ p.2.length = w)
    (hw0 : 0 < w) (odd : Bool) : ∀ p ∈ ps, (flipLast (pick odd p)).length = w := by
  intro p hp
  have := hw p hp
  have h1 : p.1 ≠ [] := by intro e; rw [e] at this; simp at this; omega
  have h2 : p.2 ≠ [] := by intro e; rw [e] at this; simp at this; omega
  cases odd <;> simp [pick, length_flipLast h1, length_flipLast h2, this.1, this.2]

set_option maxHeartbeats 1000000 in
theorem runs_pack {src dst : Fin 𝕌} (o : Own src) (od : Own dst) (hsW : src ≠ kW) (hdP : dst ≠ xP)
    (hdI : dst ≠ kI) (odd : Bool) {w Wd r N Oin : ℕ} (ps : List (List Bool × List Bool))
    (hl : ps.length = r) (hr : 1 ≤ r) (hw : ∀ p ∈ ps, p.1.length = w ∧ p.2.length = w) (hw0 : 0 < w)
    (hWd : w + 1 ≤ Wd) (hN : N = Wd * r) (hOin : Oin < 2 ^ N)
    (τ : Fin 𝕌 → WTape) (hA : τ ∘ ι = aluBank N) (hs : τ src = ⟨[], flat ps⟩) (hK : τ kW = reg (ones Wd))
    (hI : τ kI = reg (rwd N Oin)) (hP : τ xP = emp) (hD : τ dst = emp) :
    Runs (pack src dst o od odd) τ
      (· = Function.update τ dst (reg (rwd N ((wsum Wd (digits odd ps) + Fm N - Oin) % Fm N))))
      (r * (4 * w + 20) + 2 * clen (flat ps) + (r + 1) * (40 * Wd + 110) + 2 * (r * (w + 1)) + 6 * (Wd * r + Wd) +
        120 * N + 20 * Wd + 600) := by
  have hz : ∀ i, τ (ι i) = aluBank N i := fun i => congrFun hA i
  have hC : τ (ι tC) = emp := by rw [hz]; tsimp [aluBank]
  have hU : τ (ι tU) = emp := by rw [hz]; tsimp [aluBank]
  have hM : τ (ι cM) = emp := by rw [hz]; tsimp [aluBank]
  have hWA : τ (ι cWA) = emp := by rw [hz]; tsimp [aluBank]
  have hO : τ (ι sO) = emp := by rw [hz]; tsimp [aluBank]
  have hcW : τ (ι cW) = reg (ones (N + 1)) := by rw [hz]; tsimp [aluBank]
  have s1 := runs_packA o hsW odd ps hw hw0 τ hs hC hU hM hWA hK
  set ds := ps.map fun p => flipLast (pick odd p)
  set cs := digits odd ps
  have hfl := pick_length hw hw0 odd
  have hds : ds = cs.map (bits w) := by
    simp only [ds, cs, digits, List.map_map]
    apply List.map_congr_left; intro p hp
    simp only [Function.comp_apply]; rw [← hfl p hp, bits_bval]
  have hcs : ∀ c ∈ cs, c < 2 ^ w := by
    intro c hc; simp only [cs, digits, List.mem_map] at hc; obtain ⟨p, hp, rfl⟩ := hc
    rw [← hfl p hp]; exact bval_lt _
  have hcl : cs.length = r := by simp [cs, digits, hl]
  set τA := Function.update (Function.update (Function.update τ (ι tC) ⟨[], ds⟩) (ι cM) (reg (ones Wd)))
    (ι cWA) (reg (ones Wd))
  have eA : τA ∘ ι = Function.update (Function.update (Function.update (aluBank N) tC ⟨[], ds⟩) cM
      (reg (ones Wd))) cWA (reg (ones Wd)) := by simp only [τA, comp_ι_update, hA]
  obtain ⟨zw, hz1, hz2, s2⟩ := runs_winSum (M := Wd) (W := Wd) (Wc := w) (by omega) hWd le_rfl cs hcs
    (τA ∘ ι) (Cl := []) (by rw [eA]; tsimp [aluBank]) (by rw [eA]; tsimp [hds]) (by rw [eA]; tsimp [aluBank])
    (by rw [eA]; tsimp [aluBank]) (by rw [eA]; tsimp [aluBank]) (by rw [eA]; tsimp) (by rw [eA]; tsimp)
  set Cw : WTape := ⟨(cs.map (bits w)).reverse ++ [], []⟩
  have s2' : Runs (up winSum) τA (· = Function.update (Function.update (Function.update (Function.update τ
      (ι tC) Cw) (ι cM) (reg (ones Wd))) (ι cWA) (reg (ones Wd))) (ι sO) ⟨[zw], []⟩)
      ((cs.length + 1) * (40 * Wd + 110)) := by
    refine runs_up' s2 ?_
    rw [ext_update, ext_update, ext_self]
    funext x
    simp only [τA, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp at *
  have s3 := runs_packD (N := N) τ (z := zw) (C := Cw) (M := reg (ones Wd)) (A := reg (ones Wd)) hO hC hM hWA hP hcW
  set τD := Function.update τ xP (reg (Rules.fit (N + 1) zw))
  have hwl : wsum Wd cs < 2 ^ N := by
    have := wsum_lt_pow Wd cs (fun c hc => lt_of_lt_of_le (hcs c hc) (Nat.pow_le_pow_right (by norm_num)
      (by omega)))
    rwa [hcl, ← hN] at this
  have hfit : bval (Rules.fit (N + 1) zw) = wsum Wd cs := by
    rw [Rules.bval_fit_mod, hz1, Nat.mod_eq_of_lt (lt_of_lt_of_le hwl (Nat.pow_le_pow_right (by norm_num)
      (by omega)))]
  have hIv : bval (rwd N Oin) = Oin := bval_rwd (by omega)
  have s4 := runs_aluOp subMod (s₁ := xP) (s₂ := kI) (by unfold Own; decide) (by unfold Own; decide) od
    (by decide) hdP hdI (aluBank_sub (N := N) (by subst hN; exact Nat.mul_pos (by omega) (by omega)) (x := Rules.fit (N + 1) zw)
      (y := rwd N Oin) (by simp) (rwd_length N Oin) (by rw [hfit]; omega) (by rw [hIv]; omega))
    τD (by simp only [τD, comp_ι_update_own (show Own xP by unfold Own; decide), hA])
    (by simp [τD]) (by simp only [τD]; rw [Function.update_of_ne (by decide), hI])
    (by simp only [τD]; rw [Function.update_of_ne hdP, hD])
  have s5 := runs_clear (a := 0) xP (Function.update τD dst (reg (subRes N (Rules.fit (N + 1) zw) (rwd N Oin))))
  refine (Runs.then s1 (Runs.then s2' (Runs.then s3 (Runs.then s4 s5)))).mono (fun τ' h => ?_) ?_
  · rw [h]
    have e : subRes N (Rules.fit (N + 1) zw) (rwd N Oin) = rwd N ((wsum Wd cs + Fm N - Oin) % Fm N) := by
      rw [subRes, hfit, hIv]; rfl
    rw [e]
    funext x
    by_cases a1 : x = xP <;> by_cases a2 : x = dst <;> simp_all [τD, Function.update_apply, emp]
  · have c1 : clen ds = r * (w + 1) := by rw [clen_map_eq ps hfl, hl]
    have c2 : clen (cs.map (bits w)) = r * (w + 1) := by rw [← hds, c1]
    simp only [Cw, τD, WTape.words, clen_append, clen_reverse, c1, hcl, Function.update_of_ne hdP,
      Function.update_self, hz2, rwd_length, reg, clen_nil, List.reverse_nil, List.nil_append, List.append_nil,
      clen_cons, clen_nil, Rules.length_fit, length_ones]
    have c3 : (subRes N (Rules.fit (N + 1) zw) (rwd N Oin)).length = N + 1 := by simp [subRes]
    simp only [Function.update_of_ne hdP.symm, Function.update_self] at *
    simp only [clen_cons, clen_nil, Rules.length_fit, hl, c2, c3] at *
    omega

end IntegerMultBounds.Schoenhage
