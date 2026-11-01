module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaInteriorSharedWorkspaceScale
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedPreparationWorkspacePolynomial

/-! Uniform polynomial workspace estimates before summing distinct cores. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem replicaInteriorSharedWorkspace_axis_poly_le (hQ : SS.states ≤ Q)
    (R K cVratio cl cw cr cV : ℕ) :
    ∃ C : ℕ, ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.u ≤ H.p → H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p →
      H.metadataWidth ≤ cV*H.p →
      replicaInteriorSharedWorkspace (A := A) (U := U) H hQ R K cVratio ≤ C*H.t^22*H.p^22 := by
  let coeffs := [R,K,cachedOriginsSharedPush (A := A) (U := U) hQ,
    replicaClassSharedPush (Q := Q) (A := A) (U := U)]
  let C := coeffs.sum+32768+cl+cw+cr+cV+10
  let D := replicaInteriorSharedWorkspaceConstant*64^11
  refine ⟨D*C^22,?_⟩
  intro s _ H hu hl hw hr hV
  let Y := C*H.t*H.p
  have htpos : 1 ≤ H.t := by have := H.s_lt_t; omega
  have hppos := H.p_pos
  have hlinear (c : ℕ) (hc : c ≤ C) : c*H.p ≤ Y := by
    have ha := Nat.mul_le_mul_right H.p hc
    have hb := Nat.mul_le_mul_left (C*H.p) htpos
    dsimp only [Y]
    nlinarith only [ha,hb]
  have htY : H.t+2 ≤ Y := by
    have hC : 3 ≤ C := by dsimp only [C]; omega
    have ha := Nat.mul_le_mul_right H.t hC
    have hb := Nat.mul_le_mul_left (C*H.t) hppos
    dsimp only [Y]
    nlinarith only [ha,hb,htpos]
  have hPY : 2^15*H.p ≤ Y := hlinear _ (by dsimp only [C]; norm_num; omega)
  have hlY := hl.trans (hlinear cl (by dsimp only [C]; omega))
  have hwY := hw.trans (hlinear cw (by dsimp only [C]; omega))
  have hrY := hr.trans (hlinear cr (by dsimp only [C]; omega))
  have hVY := hV.trans (hlinear cV (by dsimp only [C]; omega))
  have hpY : H.p ≤ Y := by simpa only [one_mul] using hlinear 1 (by dsimp only [C]; omega)
  have huY := hu.trans hpY
  have hqY : H.precision ≤ Y := by
    have hh : H.precision ≤ H.wordWidth := by
      unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
      omega
    exact hh.trans hwY
  have hstageY : H.stage+1 ≤ Y := by
    have hh : H.stage+1 ≤ H.wordWidth := by
      unfold ReplicaHaloProblem.stage ReplicaHaloProblem.wordWidth executionStagePrecision executionWidth
      omega
    exact hh.trans hwY
  have hbandY : H.band ≤ Y := by have hh : H.band ≤ s := H.band_fit; have := H.s_lt_t; omega
  have hE := PackedHaloPassEnvelope.of_bounds H.s_lt_t (Nat.le_add_right H.origin H.span)
    H.span_fit htY hPY hstageY hqY hlY huY hwY hbandY hVY hVY
  have hCY : C ≤ Y := by
    have ha := Nat.mul_le_mul_left C htpos
    have hb := Nat.mul_le_mul_left (C*H.t) hppos
    dsimp only [Y]; nlinarith only [ha,hb]
  have hcoeff (x : ℕ) (hx : x ∈ coeffs) : x ≤ Y :=
    (List.le_sum_of_mem hx).trans ((show coeffs.sum ≤ C by dsimp only [C]; omega).trans hCY)
  have hc := replicaInteriorSharedWorkspace_envelope_le (A := A) (U := U) H hQ R K cVratio hE htY hrY
    (hcoeff R (by simp [coeffs])) (hcoeff K (by simp [coeffs]))
    (hcoeff _ (by simp [coeffs])) (hcoeff _ (by simp [coeffs]))
  have heq (a b c d : ℕ) : a*(b*c*d)^22 = (a*b^22)*c^22*d^22 := by ring
  change replicaInteriorSharedWorkspace (A := A) (U := U) H hQ R K cVratio ≤ D*(C*H.t*H.p)^22 at hc
  rw [heq] at hc
  exact hc

theorem cachedRecoveryPreparationWorkspace_axis_poly_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M cw cV : ℕ) :
    ∃ C : ℕ, ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.wordWidth ≤ cw*H.p → H.metadataWidth ≤ cV*H.p →
      cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M ≤ C*H.t^8*H.p^8 := by
  let coeffs := recoveryPreparationPushCoefficients hQ push c M
  let C := coeffs.sum+cw+cV+20
  let K := 1000000*(ssMulConst+1)*16^4
  refine ⟨K*C^8,?_⟩
  intro s _ H hw hV
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
  have hnY : (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card ≤ Y := by
    have hh : (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card ≤ s := by
      simpa only [ZMod.card] using (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card_le_univ
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
  have heq (a b c d : ℕ) : a*(b*c*d)^8 = (a*b^8)*c^8*d^8 := by ring
  change cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M ≤ K*(C*H.t*H.p)^8 at hc
  rw [heq] at hc
  exact hc

end IntegerMultBounds.MathlibTM2.Cost
