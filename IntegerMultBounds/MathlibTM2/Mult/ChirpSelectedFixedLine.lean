module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpFixedLine
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardCallerSize

/-! # The fixed forward line at explicit selected dimensions

All size, window, coefficient-envelope and scalar conditions follow from p,α,s,t.
The only remaining preconditions describe the prepared setup and actual input tapes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Spec.SignedRingProduct

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

/-- No caller-selected numerical gate or layout condition is needed by the prepared line. -/
theorem selected_program_exec {shared : Bool} (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (hA : 96 ≤ A)
    (s t α p : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
    ∀
    (u : ZMod s → GaussianInt) (_hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (v : HS 640 Q A U) (S : Stacks 640 A)
    (_hG : S.R (processor .ys) = chirpBlockStream (chirpBlockCount t m)
      (fun n => chirpEntryStream A w (3 * m + 1)
        (fun a => chirpNegativeNumerator false s t α q m (n * m) a)))
    (_hK : S.R (batch .srcY) = chirpBlockStream (chirpBlockCount t m)
      (fun n => chirpEntryStream A w (4 * m)
        (fun a => chirpNegativeNumerator true s t α q (2 * m - 1) (n * m) a)))
    (_hready : Ready (fun r => S.R (processor r)) w q)
    (_hproc : ∀ r ∈ [CR.xs, .xsv, .ysv, .acc, .out], S.R (processor r) = [])
    (_hclean : CClean output.mul S)
    (_hgather : tblHolds gather S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![s, t, m, w, 0, 0, 0, 0, 0, 0], []⟩))
    (_hconv : tblHolds convolution S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![q, t, m, w, l, 0, 0, 0, 0, 0], []⟩))
    (_hword : (S.R wordCounter).length = w) (_hproducer : ∀ i, S.R (producer i) = [])
    (_hring : RpClean host S) (_hworkspace : ∀ k ∈ correlationEmpty, S.R k = [])
    (_hdim : ∀ i, S.R (correlationDimensions i) = []) (_hoperand : S.R (batch .srcX) = [])
    (_hinput : S.R (raw .raw) = cstream A w (chirpLine s u))
    (_hraw : ChirpRawReady shared s t m w raw S)
    (_houtput : ChirpOutputState output S q w [] (chirpOutputFactors s t α q Γ m) (chirpNormalization q α))
    (_houtdim : ∀ i, (S.R (output.dim i)).length = chirpOutputDimensionCount p q l Γ w t i)
    (_houtwork : ∀ i : Fin 22, 9 ≤ i.val → S.R (output.bank i) = []),
    ∃ v' n, v'.user = v.user ∧
      n ≤ chirpRawCorrelationModeCost shared W w W w s t q l m w +
        chirpOutputCompleteCost (chirpBlockCount t m * m) p q l Γ w t ∧
      Exec body (programWith shared hQ hQrp) (mk v S) n
        (mk v' { S with R := (Function.update S.R (output.nr .out)
          (cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u))) }) := by
  dsimp only
  intro u hu v S hG hK hready hproc hclean hgather hconv hword hproducer hring hworkspace hdim
    hoperand hinput hraw houtput houtdim houtwork
  have hp : 1 ≤ p := by nlinarith
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  rcases chirpForwardCaller_fits s t p α hp hαp with
    ⟨hrawfit, hbW, h125, hwW, _, _, _, _, hsize, hvolume, htm, hproduct,
      _, hPfit, _, hBfit, _⟩
  have h125W : 125 * p < 2 ^ W := h125
  have widths := chirpForwardWidths_le p α hp hαp
  have hm : 0 < m := by dsimp [m, chirpForwardWindow]; nlinarith [Nat.zero_le (Nat.sqrt p)]
  have hmBound := chirpForwardWindow_le p α hαp
  have hlBound := chirpForwardRingLog_le p α hαp
  have hscalar : ∀ i : Fin 6, (![s, t, m, q + l + Γ + 5, q, l] : Fin 6 → ℕ) i < 2 ^ W := by
    intro i
    fin_cases i
    · exact (hrawfit 2).trans_le (Nat.pow_le_pow_right (by decide) hbW)
    · exact (hrawfit 3).trans_le (Nat.pow_le_pow_right (by decide) hbW)
    · dsimp [m]; omega
    · change q + l + Γ + 5 < 2 ^ W
      exact widths.2.1.trans_lt h125W
    · change q < 2 ^ W
      exact widths.1.trans_lt (by omega)
    · change l < 2 ^ W
      dsimp [l]; omega
  have hΓq : Γ ≤ q := by dsimp [q, Γ, chirpForwardPrecision, chirpForwardGrowth]; omega
  have hq : 13 ≤ q := by dsimp [q, chirpForwardPrecision]; omega
  have hqΓ : 13 ≤ q - Γ := by dsimp [q, Γ, chirpForwardPrecision, chirpForwardGrowth]; omega
  have hpq : p ≤ q := by dsimp [q, chirpForwardPrecision]; omega
  have hE := chirpOutputFactors_bound s t α q Γ m (NeZero.pos s) hst (by omega) hΓq hqΓ
    (by
      intro b hb
      have he := chirpForwardWindow_exponent s t α p b hst.le hp (NeZero.pos t) (by omega) hb
      have hnum : 16 * p + 1 ≤ q - Γ := by dsimp [q, Γ, chirpForwardPrecision, chirpForwardGrowth]; omega
      have hr : 16 * (p : ℝ) + 1 ≤ (q - Γ : ℕ) := by exact_mod_cast hnum
      linarith)
    (fun b hb => chirpForwardGrowth_good s t α p b (NeZero.pos s) hst (by omega) hp hb)
  exact program_exec (shared := shared) (body := body) hQ hQrp hA W s t α p q l Γ m (q + l + Γ + 5)
    (NeZero.pos s) hst hm (by omega) hq (by rfl) hpq hwW hscalar hsize hvolume htm hproduct
    hPfit hBfit (chirpForwardRingLog_good p α) u hu v S hG hK hready hproc hclean hgather hconv
    hword hproducer hring hworkspace hdim hoperand hinput hraw hE houtput houtdim houtwork

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
