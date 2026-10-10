import IntegerMultBounds.Schoenhage.RingUnpack

/-! The packed ring product on tapes (the paper's signed ring product,
`lem:signed-ring-product`). Both polynomials come as coefficient pairs of
signed `w`-bit words; the four component residues are packed, multiplied
pairwise by the Schönhage–Strassen machine modulo `2^N + 1` (`N = W r`, so
the wrap is the negacyclic one), combined into the real and imaginary
residues, and unpacked into truncated output words, interleaved on `rO`. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-! ### Moving between the unit's states -/

theorem ext_update_own {x : Fin 𝕌} (o : Own x) (τ : Fin 𝕌 → WTape) (σ : Fin 𝕋 → WTape) (v : WTape) :
    ext (Function.update τ x v) σ = Function.update (ext τ σ) x v := by
  funext y
  by_cases e : y = x
  · subst e
    have : ¬ y.val < 64 := by unfold Own at o; omega
    simp [ext, this]
  · rw [Function.update_of_ne e]
    unfold ext
    split_ifs
    · rfl
    · rw [Function.update_of_ne e]

theorem ext_ext (τ : Fin 𝕌 → WTape) (σ₁ σ₂ : Fin 𝕋 → WTape) : ext (ext τ σ₁) σ₂ = ext τ σ₂ := by
  funext y
  unfold ext
  split_ifs <;> rfl

theorem ext_comp (τ : Fin 𝕌 → WTape) (σ : Fin 𝕋 → WTape) : ext τ σ ∘ ι = σ := by
  funext i
  simp [ext, ι]

theorem ext_own {x : Fin 𝕌} (o : Own x) (τ : Fin 𝕌 → WTape) (σ : Fin 𝕋 → WTape) : ext τ σ x = τ x := by
  unfold ext Own at *
  rw [dif_neg (by omega)]

theorem clean_ext (τ : Fin 𝕌 → WTape) : Clean (ext τ (fun _ => emp)) := ext_comp τ _

/-! ### Interleaving the output words -/

/-- Real word, imaginary word, for every coefficient. -/
noncomputable def weave : Cmd 0 𝕌 := .loop lR (.seq (cpy lR rO (by decide)) (cpy lI rO (by decide)))

theorem runs_weave :
    ∀ (ps : List (List Bool × List Bool)) (τ : Fin 𝕌 → WTape) (Al Bl Ol : List (List Bool)) (W : ℕ),
      τ lR = ⟨Al, ps.map Prod.fst⟩ → τ lI = ⟨Bl, ps.map Prod.snd⟩ → τ rO = ⟨Ol, []⟩ →
      (∀ p ∈ ps, p.1.length ≤ W ∧ p.2.length ≤ W) →
      Runs weave τ (· = Function.update (Function.update (Function.update τ lR ⟨(ps.map Prod.fst).reverse ++ Al, []⟩)
        lI ⟨(ps.map Prod.snd).reverse ++ Bl, []⟩) rO ⟨(flat ps).reverse ++ Ol, []⟩) (ps.length * (2 * W + 16))
  | [], τ, Al, Bl, Ol, W, hA, hB, hO, _ => by
    refine (Runs.loop_done (by simp [hA]) rfl).mono (fun τ' h => ?_) (by simp)
    rw [← h]; funext x
    by_cases a1 : x = lR <;> by_cases a2 : x = lI <;> by_cases a3 : x = rO <;>
      simp_all [Function.update_apply]
  | p :: ps, τ, Al, Bl, Ol, W, hA, hB, hO, hW => by
    have hp := hW p (by simp)
    have s1 := runs_cpy (a := 0) (show lR ≠ rO by decide) τ (by simp [hA]) (by simp [hO])
    set τ₁ := Function.update (Function.update τ lR (τ lR).next) rO ((τ rO).put false [(τ lR).cur])
    have s2 := runs_cpy (a := 0) (show lI ≠ rO by decide) τ₁ (by tsimp [τ₁, hB]) (by tsimp [τ₁, hO, hA])
    set τ₂ := Function.update (Function.update τ₁ lI (τ₁ lI).next) rO ((τ₁ rO).put false [(τ₁ lI).cur])
    have ih := runs_weave ps τ₂ (p.1 :: Al) (p.2 :: Bl) (p.2 :: p.1 :: Ol) W (by tsimp [τ₂, τ₁, hA])
      (by tsimp [τ₂, τ₁, hB]) (by tsimp [τ₂, τ₁, hO, hA, hB]) (fun q hq => hW q (by simp [hq]))
    refine (Runs.loop_step (by simp [hA]) ((Runs.then s1 s2).mono (fun τ' h => by rw [h]; exact ih)
      le_rfl)).mono (fun τ' h => ?_) ?_
    · rw [h]; funext x
      by_cases a1 : x = lR <;> by_cases a2 : x = lI <;> by_cases a3 : x = rO <;>
        simp_all [τ₂, τ₁, Function.update_apply, flat]
    · tsimp [τ₁, hA, hB]
      nlinarith

/-! ### Packing all four components -/

theorem own_rF : Own rF := by unfold Own; decide
theorem own_rG : Own rG := by unfold Own; decide
theorem own_rO : Own rO := by unfold Own; decide
theorem own_xA : Own xA := by unfold Own; decide
theorem own_xB : Own xB := by unfold Own; decide
theorem own_xC : Own xC := by unfold Own; decide
theorem own_xE : Own xE := by unfold Own; decide
theorem own_xP : Own xP := by unfold Own; decide
theorem own_xQ : Own xQ := by unfold Own; decide
theorem own_lR : Own lR := by unfold Own; decide
theorem own_lI : Own lI := by unfold Own; decide
theorem own_kO : Own kO := by unfold Own; decide

/-- The residue of one packed component. -/
def resid (Wd r w N : ℕ) (odd : Bool) (ps : List (List Bool × List Bool)) : ℕ :=
  (wsum Wd (digits odd ps) + Fm N - wsum Wd (List.replicate r (2 ^ (w - 1)))) % Fm N

/-- Pack the real and imaginary parts of both inputs. -/
noncomputable def phaseP : Cmd 0 𝕌 :=
  .seq aluOn <| .seq (pack rF xA own_rF own_xA false) <| .seq (pack rF xB own_rF own_xB true) <|
  .seq (pack rG xC own_rG own_xC false) <| .seq (pack rG xE own_rG own_xE true) aluOff

/-- The data a ring product needs: sizes, constants, operands. -/
structure RingSetup (Wd r w s N : ℕ) (fs gs : List (List Bool × List Bool)) (τ : Fin 𝕌 → WTape) : Prop where
  hr : 1 ≤ r
  hw : 1 ≤ w
  hWd : w + 1 ≤ Wd
  hws : w + s ≤ Wd + 1
  hN : N = Wd * r
  hk : 2 ^ kOf N ∣ N
  lf : fs.length = r
  lg : gs.length = r
  wf : ∀ p ∈ fs, p.1.length = w ∧ p.2.length = w
  wg : ∀ p ∈ gs, p.1.length = w ∧ p.2.length = w
  clean : Clean τ
  F : τ rF = ⟨[], flat fs⟩
  G : τ rG = ⟨[], flat gs⟩
  O : τ rO = emp
  KW : τ kW = reg (ones Wd)
  KN : τ kN = reg (ones N)
  KR : τ kR = reg (Rules.ruler Wd (Wd + 1) r)
  KI : τ kI = reg (rwd N (wsum Wd (List.replicate r (2 ^ (w - 1)))))
  KO : τ kO = reg (rwd N (wsum Wd (List.replicate r (2 ^ (Wd - 1)))))
  KS : τ kS = reg (ones s)
  KH : τ kH = reg (bits (Wd + 1) (2 ^ (Wd - 1)))
  KC : τ kC = reg (bits (Wd + 1) (2 ^ s - 1))
  Kw : τ kw = reg (ones w)
  A : τ xA = emp
  B : τ xB = emp
  C : τ xC = emp
  E : τ xE = emp
  P : τ xP = emp
  Q : τ xQ = emp
  R : τ lR = emp
  I : τ lI = emp

theorem clen_flat {w : ℕ} : ∀ ps : List (List Bool × List Bool), (∀ p ∈ ps, p.1.length = w ∧ p.2.length = w) →
    clen (flat ps) = ps.length * 2 * (w + 1)
  | [], _ => by simp
  | p :: ps, hp => by
    have h1 := hp p (by simp)
    have h2 := clen_flat ps (fun q hq => hp q (by simp [hq]))
    rw [flat_cons, clen_cons, clen_cons, h2, h1.1, h1.2, List.length_cons]; ring

theorem RingSetup.N_pos {Wd r w s N fs gs τ} (h : RingSetup Wd r w s N fs gs τ) : 0 < N := by
  rw [h.hN]; exact Nat.mul_pos (by have := h.hWd; omega) h.hr

theorem RingSetup.Oin_lt {Wd r w s N fs gs τ} (h : RingSetup Wd r w s N fs gs τ) :
    wsum Wd (List.replicate r (2 ^ (w - 1))) < 2 ^ N := by
  have := wsum_lt_pow Wd (List.replicate r (2 ^ (w - 1))) (fun d hd => by
    rw [List.eq_of_mem_replicate hd]
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by have := h.hWd; omega))
      (Nat.pow_le_pow_right (by norm_num) le_rfl))
  rwa [List.length_replicate, ← h.hN] at this

set_option maxHeartbeats 2000000 in
theorem runs_phaseP {Wd r w s N fs gs τ} (h : RingSetup Wd r w s N fs gs τ) :
    Runs phaseP τ (· = Function.update (Function.update (Function.update (Function.update τ
      xA (reg (rwd N (resid Wd r w N false fs)))) xB (reg (rwd N (resid Wd r w N true fs))))
      xC (reg (rwd N (resid Wd r w N false gs)))) xE (reg (rwd N (resid Wd r w N true gs))))
      (4 * (r * (4 * w + 20) + 2 * (r * 2 * (w + 1)) + (r + 1) * (40 * Wd + 110) + 2 * (r * (w + 1)) +
        6 * (Wd * r + Wd) + 120 * N + 20 * Wd + 600) + 50 * N + 400) := by
  have hN0 := h.N_pos
  have hO := h.Oin_lt
  have cf : clen (flat fs) = r * 2 * (w + 1) := by rw [clen_flat fs h.wf, h.lf]
  have cg : clen (flat gs) = r * 2 * (w + 1) := by rw [clen_flat gs h.wg, h.lg]
  have s0 := runs_aluOn hN0 τ h.clean h.KN
  set τ₀ := ext τ (aluBank N)
  have e : ∀ x, Own x → τ₀ x = τ x := fun x o => ext_own o τ _
  have s1 := runs_pack own_rF own_xA (by decide) (by decide) (by decide) false fs h.lf h.hr h.wf (by have := h.hw; omega)
    h.hWd h.hN hO τ₀ (ext_comp τ _) (by rw [e _ own_rF, h.F]) (by rw [e _ (by unfold Own; decide), h.KW])
    (by rw [e _ (by unfold Own; decide), h.KI]) (by rw [e _ own_xP, h.P]) (by rw [e _ own_xA, h.A])
  set τ₁ := Function.update τ₀ xA (reg (rwd N (resid Wd r w N false fs)))
  have s2 := runs_pack own_rF own_xB (by decide) (by decide) (by decide) true fs h.lf h.hr h.wf (by have := h.hw; omega)
    h.hWd h.hN hO τ₁ (by simp only [τ₁, comp_ι_update_own own_xA, τ₀, ext_comp])
    (by simp only [τ₁]; rw [Function.update_of_ne (by decide), e _ own_rF, h.F])
    (by simp only [τ₁]; rw [Function.update_of_ne (by decide), e _ (by unfold Own; decide), h.KW])
    (by simp only [τ₁]; rw [Function.update_of_ne (by decide), e _ (by unfold Own; decide), h.KI])
    (by simp only [τ₁]; rw [Function.update_of_ne (by decide), e _ own_xP, h.P])
    (by simp only [τ₁]; rw [Function.update_of_ne (by decide), e _ own_xB, h.B])
  set τ₂ := Function.update τ₁ xB (reg (rwd N (resid Wd r w N true fs)))
  have s3 := runs_pack own_rG own_xC (by decide) (by decide) (by decide) false gs h.lg h.hr h.wg (by have := h.hw; omega)
    h.hWd h.hN hO τ₂ (by simp only [τ₂, τ₁, comp_ι_update_own own_xA, comp_ι_update_own own_xB, τ₀, ext_comp])
    (by simp only [τ₂, τ₁]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), e _ own_rG, h.G])
    (by simp only [τ₂, τ₁]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      e _ (by unfold Own; decide), h.KW])
    (by simp only [τ₂, τ₁]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      e _ (by unfold Own; decide), h.KI])
    (by simp only [τ₂, τ₁]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), e _ own_xP, h.P])
    (by simp only [τ₂, τ₁]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), e _ own_xC, h.C])
  set τ₃ := Function.update τ₂ xC (reg (rwd N (resid Wd r w N false gs)))
  have s4 := runs_pack own_rG own_xE (by decide) (by decide) (by decide) true gs h.lg h.hr h.wg (by have := h.hw; omega)
    h.hWd h.hN hO τ₃ (by simp only [τ₃, τ₂, τ₁, comp_ι_update_own own_xA, comp_ι_update_own own_xB,
      comp_ι_update_own own_xC, τ₀, ext_comp])
    (by simp only [τ₃, τ₂, τ₁]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), e _ own_rG, h.G])
    (by simp only [τ₃, τ₂, τ₁]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), e _ (by unfold Own; decide), h.KW])
    (by simp only [τ₃, τ₂, τ₁]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), e _ (by unfold Own; decide), h.KI])
    (by simp only [τ₃, τ₂, τ₁]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), e _ own_xP, h.P])
    (by simp only [τ₃, τ₂, τ₁]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), e _ own_xE, h.E])
  set τ₄ := Function.update τ₃ xE (reg (rwd N (resid Wd r w N true gs)))
  have s5 := runs_aluOff (N := N) τ₄ (by simp only [τ₄, τ₃, τ₂, τ₁, comp_ι_update_own own_xA,
    comp_ι_update_own own_xB, comp_ι_update_own own_xC, comp_ι_update_own own_xE, τ₀, ext_comp])
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5))))).mono
    (fun τ' hh => ?_) ?_
  · rw [hh]
    simp only [τ₄, τ₃, τ₂, τ₁, τ₀, ext_update_own own_xA, ext_update_own own_xB, ext_update_own own_xC,
      ext_update_own own_xE, ext_ext, ext_clean h.clean, resid]
  · rw [cf, cg] at *
    simp only [h.lf, h.lg, resid] at *
    omega

/-! ### Combining two products -/

/-- Combine `xP` and `xQ` into `d` with the unit, clearing both. -/
noncomputable def phaseC (op : Cmd 0 𝕋) (d : Fin 𝕌) (od : Own d) : Cmd 0 𝕌 :=
  .seq aluOn <| .seq (aluOp op xP xQ d own_xP own_xQ od) <| .seq (clear xP) <| .seq (clear xQ) aluOff

theorem runs_phaseC (op : Cmd 0 𝕋) {d : Fin 𝕌} (od : Own d) (hdP : d ≠ xP) (hdQ : d ≠ xQ) {N B : ℕ}
    (hN : 0 < N) {x y z : List Bool}
    (hop : Runs op (Function.update (Function.update (aluBank N) aX (reg x)) aY (reg y))
      (· = Function.update (aluBank N) aO (reg z)) B)
    (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hK : τ kN = reg (ones N)) (hx : τ xP = reg x) (hy : τ xQ = reg y)
    (hd : τ d = emp) :
    Runs (phaseC op d od) τ (· = Function.update (Function.update (Function.update τ d (reg z)) xP emp) xQ emp)
      (3 * x.length + 3 * y.length + B + 4 * z.length + 2 * (x.length + 1) + 2 * (y.length + 1) + 48 * N + 420) := by
  have s0 := runs_aluOn hN τ hc hK
  set τ₀ := ext τ (aluBank N)
  have e : ∀ x, Own x → τ₀ x = τ x := fun x o => ext_own o τ _
  have s1 := runs_aluOp op own_xP own_xQ od (by decide) hdP hdQ hop τ₀ (ext_comp τ _) (by rw [e _ own_xP, hx])
    (by rw [e _ own_xQ, hy]) (by rw [e _ od, hd])
  have s2 := runs_clear (a := 0) xP (Function.update τ₀ d (reg z))
  have s3 := runs_clear (a := 0) xQ (Function.update (Function.update τ₀ d (reg z)) xP ⟨[], []⟩)
  have s4 := runs_aluOff (N := N) (Function.update (Function.update (Function.update τ₀ d (reg z)) xP ⟨[], []⟩)
    xQ ⟨[], []⟩) (by simp only [comp_ι_update_own od, comp_ι_update_own own_xP, comp_ι_update_own own_xQ,
      τ₀, ext_comp])
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s3 s4)))).mono (fun τ' h => ?_) ?_
  · rw [h]
    simp only [τ₀, ext_update_own od, ext_update_own own_xP, ext_update_own own_xQ, ext_ext, ext_clean hc]
    rfl
  · simp only [Function.update_of_ne hdP.symm, Function.update_of_ne hdQ.symm,
      Function.update_of_ne (show xQ ≠ xP by decide), e _ own_xP, e _ own_xQ, hx, hy, reg, WTape.words,
      clen_cons, clen_nil, List.reverse_nil, List.nil_append]
    omega

/-! ### Unpacking both parts -/

theorem own_kR : Own kR := by unfold Own; decide
theorem own_kH : Own kH := by unfold Own; decide
theorem own_kC : Own kC := by unfold Own; decide
theorem own_kS : Own kS := by unfold Own; decide
theorem own_kw : Own kw := by unfold Own; decide

/-- Add the offset to both residues, unpack them, interleave the words on `rO`. -/
noncomputable def phaseU : Cmd 0 𝕌 :=
  .seq aluOn <| .seq (aluOp addMod lR kO xP own_lR own_kO own_xP) <|
  .seq (aluOp addMod lI kO xQ own_lI own_kO own_xQ) <| .seq (clear lR) <| .seq (clear lI) <|
  .seq (unpack xP lR own_xP own_lR (by decide)) <| .seq (unpack xQ lI own_xQ own_lI (by decide)) <|
  .seq (rewind lR) <| .seq (rewind lI) <| .seq weave <| .seq (clear lR) <| .seq (clear lI) <|
  .seq (clear xP) <| .seq (clear xQ) <| .seq aluOff (rewind rO)

/-- The output words of a residue. -/
def outs (Wd r s w N v : ℕ) : List (List Bool) :=
  (pieces Wd r ((v + wsum Wd (List.replicate r (2 ^ (Wd - 1)))) % Fm N)).map (outWord Wd s w)

theorem length_outs (Wd r s w N v : ℕ) : (outs Wd r s w N v).length = r := by simp [outs, length_pieces]

theorem outs_length_le {Wd r s w N v : ℕ} : ∀ x ∈ outs Wd r s w N v, x.length ≤ w := by
  intro x hx; simp only [outs, List.mem_map] at hx; obtain ⟨e, -, rfl⟩ := hx; simp [outWord]

theorem Oout_lt {Wd r N : ℕ} (hW : 1 ≤ Wd) (hN : N = Wd * r) :
    wsum Wd (List.replicate r (2 ^ (Wd - 1))) < 2 ^ N := by
  have := wsum_lt_pow Wd (List.replicate r (2 ^ (Wd - 1))) (fun d hd => by
    rw [List.eq_of_mem_replicate hd]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  rwa [List.length_replicate, ← hN] at this

set_option maxHeartbeats 4000000 in
theorem runs_phaseU {Wd r w s N : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hWd : w + 1 ≤ Wd) (hN : N = Wd * r)
    (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hKN : τ kN = reg (ones N))
    (hKR : τ kR = reg (Rules.ruler Wd (Wd + 1) r))
    (hKO : τ kO = reg (rwd N (wsum Wd (List.replicate r (2 ^ (Wd - 1))))))
    (hKS : τ kS = reg (ones s)) (hKH : τ kH = reg (bits (Wd + 1) (2 ^ (Wd - 1))))
    (hKC : τ kC = reg (bits (Wd + 1) (2 ^ s - 1))) (hKw : τ kw = reg (ones w))
    {a b : ℕ} (ha : a < Fm N) (hb : b < Fm N) (hR : τ lR = reg (rwd N a)) (hI : τ lI = reg (rwd N b))
    (hP : τ xP = emp) (hQ : τ xQ = emp) (hO : τ rO = emp) :
    Runs phaseU τ (· = Function.update (Function.update (Function.update τ lR emp) lI emp) rO
      ⟨[], flat (List.zip (outs Wd r s w N a) (outs Wd r s w N b))⟩)
      (2 * (r * (26 * Wd + 3 * s + 4 * w + 170) + 24 * r * (Wd + 2)) + r * (12 * w + 40) + 600 * N + 2000) := by
  have hN0 : 0 < N := by rw [hN]; exact Nat.mul_pos (by omega) hr
  have hOo := Oout_lt (r := r) (by omega) hN
  set Oo := wsum Wd (List.replicate r (2 ^ (Wd - 1)))
  have hFm : Fm N = 2 ^ N + 1 := rfl
  have s0 := runs_aluOn hN0 τ hc hKN
  set τ₀ := ext τ (aluBank N)
  have e : ∀ x, Own x → τ₀ x = τ x := fun x o => ext_own o τ _
  have hva : bval (rwd N a) = a := bval_rwd (by rw [← hFm]; exact ha)
  have hvb : bval (rwd N b) = b := bval_rwd (by rw [← hFm]; exact hb)
  have hvo : bval (rwd N Oo) = Oo := bval_rwd (by omega)
  have ea : addRes N (rwd N a) (rwd N Oo) = rwd N ((a + Oo) % Fm N) := by rw [addRes, hva, hvo]; rfl
  have eb : addRes N (rwd N b) (rwd N Oo) = rwd N ((b + Oo) % Fm N) := by rw [addRes, hvb, hvo]; rfl
  have s1 := runs_aluOp addMod own_lR own_kO own_xP (by decide) (by decide) (by decide)
    (aluBank_add hN0 (rwd_length N a) (rwd_length N Oo) (by rw [hva]; omega) (by rw [hvo]; omega))
    τ₀ (ext_comp τ _) (by rw [e _ own_lR, hR]) (by rw [e _ own_kO, hKO]) (by rw [e _ own_xP, hP])
  rw [ea] at s1
  set τ₁ := Function.update τ₀ xP (reg (rwd N ((a + Oo) % Fm N)))
  have s2 := runs_aluOp addMod own_lI own_kO own_xQ (by decide) (by decide) (by decide)
    (aluBank_add hN0 (rwd_length N b) (rwd_length N Oo) (by rw [hvb]; omega) (by rw [hvo]; omega))
    τ₁ (by simp only [τ₁, comp_ι_update_own own_xP, τ₀, ext_comp]) (by tsimp [τ₁, e _ own_lI, hI])
    (by tsimp [τ₁, e _ own_kO, hKO]) (by tsimp [τ₁, e _ own_xQ, hQ])
  rw [eb] at s2
  set τ₂ := Function.update τ₁ xQ (reg (rwd N ((b + Oo) % Fm N)))
  have s3 := runs_clear (a := 0) lR τ₂
  have s4 := runs_clear (a := 0) lI (Function.update τ₂ lR ⟨[], []⟩)
  set τ₄ := Function.update (Function.update τ₂ lR ⟨[], []⟩) lI ⟨[], []⟩
  have c₄ : τ₄ ∘ ι = aluBank N := by
    simp only [τ₄, τ₂, τ₁, comp_ι_update_own own_xP, comp_ι_update_own own_xQ, comp_ι_update_own own_lR,
      comp_ι_update_own own_lI, τ₀, ext_comp]
  have s5 := runs_unpack (src := xP) (L := lR) own_xP own_lR (by decide) (by decide) (s := s) (w := w) hr hN τ₄ c₄
    (v := rwd N ((a + Oo) % Fm N))
    (rwd_length N _) (by tsimp [τ₄, τ₂, τ₁]) (by tsimp [τ₄, τ₂, τ₁, e _ own_kR, hKR])
    (by tsimp [τ₄, τ₂, τ₁, e _ own_kH, hKH]) (by tsimp [τ₄, τ₂, τ₁, e _ own_kC, hKC])
    (by tsimp [τ₄, τ₂, τ₁, e _ own_kS, hKS]) (by tsimp [τ₄, τ₂, τ₁, e _ own_kw, hKw]) (Ll := [])
    (by tsimp [τ₄, τ₂, τ₁])
  set A := (pieces Wd r (bval (rwd N ((a + Oo) % Fm N)))).map (outWord Wd s w)
  set τ₅ := Function.update τ₄ lR ⟨A.reverse ++ [], []⟩
  have s6 := runs_unpack (src := xQ) (L := lI) own_xQ own_lI (by decide) (by decide) (s := s) (w := w) hr hN τ₅
    (by simp only [τ₅, comp_ι_update_own own_lR, c₄]) (v := rwd N ((b + Oo) % Fm N))
    (rwd_length N _) (by tsimp [τ₅, τ₄, τ₂, τ₁]) (by tsimp [τ₅, τ₄, τ₂, τ₁, e _ own_kR, hKR])
    (by tsimp [τ₅, τ₄, τ₂, τ₁, e _ own_kH, hKH]) (by tsimp [τ₅, τ₄, τ₂, τ₁, e _ own_kC, hKC])
    (by tsimp [τ₅, τ₄, τ₂, τ₁, e _ own_kS, hKS]) (by tsimp [τ₅, τ₄, τ₂, τ₁, e _ own_kw, hKw]) (Ll := [])
    (by tsimp [τ₅, τ₄, τ₂, τ₁])
  set B := (pieces Wd r (bval (rwd N ((b + Oo) % Fm N)))).map (outWord Wd s w)
  set τ₆ := Function.update τ₅ lI ⟨B.reverse ++ [], []⟩
  have s7 := runs_rewind (a := 0) lR τ₆
  have s8 := runs_rewind (a := 0) lI (Function.update τ₆ lR ⟨[], (τ₆ lR).left.reverse ++ (τ₆ lR).right⟩)
  set τ₈ := Function.update (Function.update τ₆ lR ⟨[], A⟩) lI ⟨[], B⟩
  have e₈ : Function.update (Function.update τ₆ lR ⟨[], (τ₆ lR).left.reverse ++ (τ₆ lR).right⟩) lI
      ⟨[], (Function.update τ₆ lR ⟨[], (τ₆ lR).left.reverse ++ (τ₆ lR).right⟩ lI).left.reverse ++
        (Function.update τ₆ lR ⟨[], (τ₆ lR).left.reverse ++ (τ₆ lR).right⟩ lI).right⟩ = τ₈ := by
    simp only [τ₈]; tsimp [τ₆, τ₅]
  have hAl : A.length = r := by simp [A, length_pieces]
  have hBl : B.length = r := by simp [B, length_pieces]
  have hA' : (List.zip A B).map Prod.fst = A := by rw [List.map_fst_zip]; omega
  have hB' : (List.zip A B).map Prod.snd = B := by rw [List.map_snd_zip]; omega
  have s9 := runs_weave (List.zip A B) τ₈ [] [] [] w (by tsimp [τ₈, hA']) (by tsimp [τ₈, hB'])
    (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, e _ own_rO, hO, emp]) (by
      intro p hp
      have := List.of_mem_zip hp
      refine ⟨?_, ?_⟩
      · obtain ⟨x, -, hx⟩ := List.mem_map.mp this.1; rw [← hx]; simp [outWord]
      · obtain ⟨x, -, hx⟩ := List.mem_map.mp this.2; rw [← hx]; simp [outWord])
  set τ₉ := Function.update (Function.update (Function.update τ₈ lR ⟨((List.zip A B).map Prod.fst).reverse ++ [], []⟩)
    lI ⟨((List.zip A B).map Prod.snd).reverse ++ [], []⟩) rO ⟨(flat (List.zip A B)).reverse ++ [], []⟩
  have s10 := runs_clear (a := 0) lR τ₉
  have s11 := runs_clear (a := 0) lI (Function.update τ₉ lR ⟨[], []⟩)
  have s12 := runs_clear (a := 0) xP (Function.update (Function.update τ₉ lR ⟨[], []⟩) lI ⟨[], []⟩)
  have s13 := runs_clear (a := 0) xQ (Function.update (Function.update (Function.update τ₉ lR ⟨[], []⟩) lI ⟨[], []⟩)
    xP ⟨[], []⟩)
  set τ₁₃ := Function.update (Function.update (Function.update (Function.update τ₉ lR ⟨[], []⟩) lI ⟨[], []⟩)
    xP ⟨[], []⟩) xQ ⟨[], []⟩
  have s14 := runs_aluOff (N := N) τ₁₃ (by
    simp only [τ₁₃, τ₉, τ₈, τ₆, τ₅, comp_ι_update_own own_xP, comp_ι_update_own own_xQ, comp_ι_update_own own_lR,
      comp_ι_update_own own_lI, comp_ι_update_own own_rO, c₄])
  have s15 := runs_rewind (a := 0) rO (ext τ₁₃ (fun _ => emp))
  have hAo : A = outs Wd r s w N a := by
    simp only [A, outs]; rw [bval_rwd (N := N) (r := (a + Oo) % Fm N) (Nat.mod_lt _ (by simp [Fm]))]
  have hBo : B = outs Wd r s w N b := by
    simp only [B, outs]; rw [bval_rwd (N := N) (r := (b + Oo) % Fm N) (Nat.mod_lt _ (by simp [Fm]))]
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 (Runs.then (s8.mono (fun _ h => h.trans e₈) le_rfl) (Runs.then s9 (Runs.then s10
    (Runs.then s11 (Runs.then s12 (Runs.then s13 (Runs.then s14 s15))))))))))))))).mono (fun τ' h => ?_) ?_
  · rw [h, ← hAo, ← hBo]
    simp only [τ₁₃, τ₉, τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, ext_update_own own_xP, ext_update_own own_xQ,
      ext_update_own own_lR, ext_update_own own_lI, ext_update_own own_rO, ext_ext, ext_clean hc]
    funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hP, hQ, hO, emp] at *
  · have l1 : clen A = r * (w + 1) := by rw [clen_map_eq (w := w) _ (fun _ _ => by simp [outWord]), length_pieces]
    have l2 : clen B = r * (w + 1) := by rw [clen_map_eq (w := w) _ (fun _ _ => by simp [outWord]), length_pieces]
    have l3 : clen (flat (List.zip A B)) = r * 2 * (w + 1) := by
      rw [clen_flat (w := w) _ (fun p hp => by
        have := List.of_mem_zip hp
        obtain ⟨x, -, hx⟩ := List.mem_map.mp this.1; obtain ⟨y, -, hy⟩ := List.mem_map.mp this.2
        rw [← hx, ← hy]; simp [outWord]), List.length_zip, hAl, hBl, min_self]
    tsimp [τ₁₃, τ₉, τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, e _ own_lR, e _ own_lI, e _ own_rO, hR, hI, hO, hA', hB', reg, emp,
      WTape.words, clen_reverse, clen_append, l1, l2, l3, rwd_length, clen_cons, clen_nil, ext_own own_rO,
      hAl, hBl, min_self]
    ring_nf
    nlinarith

/-! ### The whole ring product -/

/-- The packed ring product. -/
noncomputable def ringProd : Cmd 0 𝕌 :=
  .seq phaseP <| .seq (mulStep xA xC xP own_xA own_xC own_xP) <| .seq (mulStep xB xE xQ own_xB own_xE own_xQ) <|
  .seq (phaseC subMod lR own_lR) <| .seq (mulStep xA xE xP own_xA own_xE own_xP) <|
  .seq (mulStep xB xC xQ own_xB own_xC own_xQ) <| .seq (phaseC addMod lI own_lI) <|
  .seq (clear xA) <| .seq (clear xB) <| .seq (clear xC) <| .seq (clear xE) phaseU

/-- The real residue. -/
def reRes (Wd r w N : ℕ) (fs gs : List (List Bool × List Bool)) : ℕ :=
  (resid Wd r w N false fs * resid Wd r w N false gs % Fm N + Fm N -
    resid Wd r w N true fs * resid Wd r w N true gs % Fm N) % Fm N

/-- The imaginary residue. -/
def imRes (Wd r w N : ℕ) (fs gs : List (List Bool × List Bool)) : ℕ :=
  (resid Wd r w N false fs * resid Wd r w N true gs % Fm N +
    resid Wd r w N true fs * resid Wd r w N false gs % Fm N) % Fm N

/-- A bound on the ring product's steps. -/
def ringCost (Wd r w s N : ℕ) : ℕ :=
  4 * (cost cA cB cC0 N + 640 * N + 56000) + 2000 * N + 400 * r * (Wd + w + s + 10) + 20000

theorem Clean.update {τ : Fin 𝕌 → WTape} (hc : Clean τ) {x : Fin 𝕌} (o : Own x) (v : WTape) :
    Clean (Function.update τ x v) := by
  unfold Clean; rw [comp_ι_update_own o]; exact hc

theorem resid_lt (Wd r w N : ℕ) (odd : Bool) (ps : List (List Bool × List Bool)) :
    resid Wd r w N odd ps < Fm N := Nat.mod_lt _ (by simp [Fm])

theorem rwd_bval_lt {N v : ℕ} (h : v < Fm N) : bval (rwd N v) < 2 ^ N + 1 := by rw [bval_rwd h]; exact h

set_option maxHeartbeats 8000000 in
theorem runs_ringProd {Wd r w s N : ℕ} {fs gs : List (List Bool × List Bool)} {τ : Fin 𝕌 → WTape}
    (h : RingSetup Wd r w s N fs gs τ) :
    Runs ringProd τ (· = Function.update τ rO
      ⟨[], flat (List.zip (outs Wd r s w N (reRes Wd r w N fs gs)) (outs Wd r s w N (imRes Wd r w N fs gs)))⟩)
      (ringCost Wd r w s N) := by
  have hN0 := h.N_pos
  have hA := resid_lt Wd r w N false fs; have hB := resid_lt Wd r w N true fs
  have hC := resid_lt Wd r w N false gs; have hE := resid_lt Wd r w N true gs
  set RA := resid Wd r w N false fs
  set RB := resid Wd r w N true fs
  set RC := resid Wd r w N false gs
  set RE := resid Wd r w N true gs
  have s1 := runs_phaseP h
  set τ₁ := Function.update (Function.update (Function.update (Function.update τ
      xA (reg (rwd N RA))) xB (reg (rwd N RB))) xC (reg (rwd N RC))) xE (reg (rwd N RE))
  have c₁ : Clean τ₁ := (((h.clean.update own_xA _).update own_xB _).update own_xC _).update own_xE _
  have s2 := runs_mulStep own_xA own_xC own_xP (by decide) (by decide) (by decide) hN0 h.hk hA hC τ₁ c₁
    (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁, h.KN]) (by tsimp [τ₁, h.P])
  set τ₂ := Function.update τ₁ xP (reg (rwd N (RA * RC % Fm N)))
  have s3 := runs_mulStep own_xB own_xE own_xQ (by decide) (by decide) (by decide) hN0 h.hk hB hE τ₂
    (c₁.update own_xP _) (by tsimp [τ₂, τ₁]) (by tsimp [τ₂, τ₁]) (by tsimp [τ₂, τ₁, h.KN]) (by tsimp [τ₂, τ₁, h.Q])
  set τ₃ := Function.update τ₂ xQ (reg (rwd N (RB * RE % Fm N)))
  have hP1 := Nat.mod_lt (RA * RC) (show 0 < Fm N by simp [Fm])
  have hP2 := Nat.mod_lt (RB * RE) (show 0 < Fm N by simp [Fm])
  have s4 := runs_phaseC subMod own_lR (by decide) (by decide) hN0
    (aluBank_sub hN0 (rwd_length N _) (rwd_length N _) (rwd_bval_lt hP1) (rwd_bval_lt hP2))
    τ₃ ((c₁.update own_xP _).update own_xQ _) (by tsimp [τ₃, τ₂, τ₁, h.KN]) (by tsimp [τ₃, τ₂, τ₁])
    (by tsimp [τ₃, τ₂, τ₁]) (by tsimp [τ₃, τ₂, τ₁, h.R])
  have eRe : subRes N (rwd N (RA * RC % Fm N)) (rwd N (RB * RE % Fm N)) = rwd N (reRes Wd r w N fs gs) := by
    rw [subRes, bval_rwd hP1, bval_rwd hP2]; rfl
  rw [eRe] at s4
  set τ₄ := Function.update (Function.update (Function.update τ₃ lR (reg (rwd N (reRes Wd r w N fs gs)))) xP emp)
    xQ emp
  have c₄ : Clean τ₄ := ((((c₁.update own_xP _).update own_xQ _).update own_lR _).update own_xP _).update own_xQ _
  have s5 := runs_mulStep own_xA own_xE own_xP (by decide) (by decide) (by decide) hN0 h.hk hA hE τ₄ c₄
    (by tsimp [τ₄, τ₃, τ₂, τ₁]) (by tsimp [τ₄, τ₃, τ₂, τ₁]) (by tsimp [τ₄, τ₃, τ₂, τ₁, h.KN])
    (by tsimp [τ₄, emp])
  set τ₅ := Function.update τ₄ xP (reg (rwd N (RA * RE % Fm N)))
  have s6 := runs_mulStep own_xB own_xC own_xQ (by decide) (by decide) (by decide) hN0 h.hk hB hC τ₅
    (c₄.update own_xP _) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁])
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, h.KN]) (by tsimp [τ₅, τ₄, emp])
  set τ₆ := Function.update τ₅ xQ (reg (rwd N (RB * RC % Fm N)))
  have hP3 := Nat.mod_lt (RA * RE) (show 0 < Fm N by simp [Fm])
  have hP4 := Nat.mod_lt (RB * RC) (show 0 < Fm N by simp [Fm])
  have s7 := runs_phaseC addMod own_lI (by decide) (by decide) hN0
    (aluBank_add hN0 (rwd_length N _) (rwd_length N _) (rwd_bval_lt hP3) (rwd_bval_lt hP4))
    τ₆ ((c₄.update own_xP _).update own_xQ _) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h.KN])
    (by tsimp [τ₆, τ₅]) (by tsimp [τ₆]) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h.I])
  have eIm : addRes N (rwd N (RA * RE % Fm N)) (rwd N (RB * RC % Fm N)) = rwd N (imRes Wd r w N fs gs) := by
    rw [addRes, bval_rwd hP3, bval_rwd hP4]; rfl
  rw [eIm] at s7
  set τ₇ := Function.update (Function.update (Function.update τ₆ lI (reg (rwd N (imRes Wd r w N fs gs)))) xP emp)
    xQ emp
  have s8 := runs_clear (a := 0) xA τ₇
  have s9 := runs_clear (a := 0) xB (Function.update τ₇ xA ⟨[], []⟩)
  have s10 := runs_clear (a := 0) xC (Function.update (Function.update τ₇ xA ⟨[], []⟩) xB ⟨[], []⟩)
  have s11 := runs_clear (a := 0) xE (Function.update (Function.update (Function.update τ₇ xA ⟨[], []⟩) xB ⟨[], []⟩)
    xC ⟨[], []⟩)
  set τ₁₁ := Function.update (Function.update (Function.update (Function.update τ₇ xA ⟨[], []⟩) xB ⟨[], []⟩)
    xC ⟨[], []⟩) xE ⟨[], []⟩
  have c₁₁ : Clean τ₁₁ := by
    simp only [τ₁₁, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁]
    exact (((((((((((((((h.clean.update own_xA _).update own_xB _).update own_xC _).update own_xE _).update
      own_xP _).update own_xQ _).update own_lR _).update own_xP _).update own_xQ _).update own_xP _).update
      own_xQ _).update own_lI _).update own_xP _).update own_xQ _).update own_xA _).update own_xB _ |>.update
      own_xC _ |>.update own_xE _
  have s12 := runs_phaseU (s := s) h.hr h.hw h.hWd h.hN τ₁₁ c₁₁ (by tsimp [τ₁₁, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h.KN])
    (by tsimp [τ₁₁, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h.KR]) (by tsimp [τ₁₁, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h.KO])
    (by tsimp [τ₁₁, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h.KS]) (by tsimp [τ₁₁, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h.KH])
    (by tsimp [τ₁₁, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h.KC]) (by tsimp [τ₁₁, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h.Kw])
    (a := reRes Wd r w N fs gs) (b := imRes Wd r w N fs gs)
    (by unfold reRes; exact Nat.mod_lt _ (by simp [Fm])) (by unfold imRes; exact Nat.mod_lt _ (by simp [Fm]))
    (by tsimp [τ₁₁, τ₇, τ₆, τ₅, τ₄]) (by tsimp [τ₁₁, τ₇]) (by tsimp [τ₁₁, τ₇, emp]) (by tsimp [τ₁₁, τ₇, emp])
    (by tsimp [τ₁₁, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, h.O])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 s12))))))))))).mono (fun τ' hh => ?_) ?_
  · rw [hh]
    funext x
    simp only [τ₁₁, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [h.A, h.B, h.C, h.E, h.P, h.Q, h.R, h.I, emp] at *
  · have q1 := ssCost_le N RA RC; have q2 := ssCost_le N RB RE
    have q3 := ssCost_le N RA RE; have q4 := ssCost_le N RB RC
    tsimp [τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, reg, emp, WTape.words, clen_cons, clen_nil, rwd_length]
    have hWN : Wd ≤ N := by rw [h.hN]; exact Nat.le_mul_of_pos_right Wd h.hr
    have hrW : Wd * r = N := h.hN.symm
    unfold ringCost
    nlinarith [q1, q2, q3, q4, hWN, hrW]

end IntegerMultBounds.Schoenhage
