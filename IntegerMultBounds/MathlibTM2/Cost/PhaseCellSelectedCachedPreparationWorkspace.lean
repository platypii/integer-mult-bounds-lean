module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedPreparationWorkspacePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! All recovery-preparation scratch is shared and fits selected whole-box volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedCachedRecoveryPreparationWorkspace_volume_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M cw cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ H : ReplicaHaloProblem (Sizes.s n i), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p →
      scale*cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M ≤ Sizes.T n := by
  let coeffs := recoveryPreparationPushCoefficients hQ push c M
  let C := coeffs.sum+cw+cV+20
  let K := 1000000*(ssMulConst+1)*16^4
  filter_upwards [selectedAxisPolynomial_le_volume (scale*K*C^8) 8 8] with n hn
  intro h i _ H hp ht hw hV
  let Y := C*H.t*H.p
  have htpos : 1 ≤ H.t := by have := H.s_lt_t; omega
  have hppos := H.p_pos
  have hC : 1 ≤ C := by dsimp only [C]; omega
  have hY : 1 ≤ Y := Nat.mul_pos (Nat.mul_pos hC htpos) hppos
  have hCY : C ≤ Y := by
    have ha := Nat.mul_le_mul_left C htpos
    have hb := Nat.mul_le_mul_left (C*H.t) hppos
    dsimp only [Y]; omega
  have hlinear (a : ℕ) (ha : a ≤ C) : a*H.p ≤ Y := by
    have hb := Nat.mul_le_mul_right H.p ha
    have hc := Nat.mul_le_mul_left (C*H.p) htpos
    dsimp only [Y]; nlinarith only [hb,hc]
  have hwY := hw.trans (hlinear cw (by dsimp only [C]; omega))
  have hVY := hV.trans (hlinear cV (by dsimp only [C]; omega))
  have htY : H.t ≤ Y := by
    have ha := Nat.mul_le_mul_right H.t hC
    have hb := Nat.mul_le_mul_left (C*H.t) hppos
    dsimp only [Y]; nlinarith only [ha,hb]
  have hqY : H.precision ≤ Y := by
    have hq : H.precision ≤ H.wordWidth := by
      unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
      omega
    exact hq.trans hwY
  have hspanY : H.span ≤ Y := by have := H.span_fit; have := H.s_lt_t; omega
  have hbandY : H.band ≤ Y := H.band_fit.trans (H.s_lt_t.le.trans htY)
  have hnY : (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card ≤ Y := by
    have hh : (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card ≤ Sizes.s n i := by
      simpa only [ZMod.card] using (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card_le_univ
    exact hh.trans (H.s_lt_t.le.trans htY)
  have hc := cachedRecoveryPreparationWorkspace_envelope_le H hQ push c M Y hY (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hqY
    · exact hwY
    · exact hspanY
    · exact hVY
    · exact hbandY
    · exact hnY) (by
    intro x hx
    have hxsum : x ≤ coeffs.sum := List.le_sum_of_mem hx
    have hsumC : coeffs.sum ≤ C := by dsimp only [C]; omega
    exact hxsum.trans (hsumC.trans hCY))
  have hscaled := Nat.mul_le_mul_left scale hc
  have heq (a b c d e : ℕ) : a*(b*(c*d*e)^8) = (a*b*c^8)*d^8*e^8 := by ring
  change scale*cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M ≤ scale*(K*(C*H.t*H.p)^8) at hscaled
  rw [heq] at hscaled
  exact hscaled.trans (by simpa only [hp,ht] using hn i)

end IntegerMultBounds.MathlibTM2.Cost
