module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaInteriorSharedWorkspaceScale
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! The actual shared interior reserve fits selected whole-box volume uniformly in axes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

variable {Q A : ℕ} {U : Type}

theorem selectedReplicaInteriorSharedWorkspace_volume_le (hQ : SS.states ≤ Q)
    (R K cVratio cl cw cr cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ H : ReplicaHaloProblem (Sizes.s n i), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.u ≤ H.p → H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p →
      H.metadataWidth ≤ cV*H.p → scale*replicaInteriorSharedWorkspace (A := A) (U := U) H hQ R K cVratio ≤ Sizes.T n := by
  let coeffs := [R,K,cachedOriginsSharedPush (A := A) (U := U) hQ,
    replicaClassSharedPush (Q := Q) (A := A) (U := U)]
  let C := coeffs.sum+32768+cl+cw+cr+cV+10
  let D := replicaInteriorSharedWorkspaceConstant*64^11
  filter_upwards [selectedAxisPolynomial_le_volume (scale*D*C^22) 22 22] with n hn
  intro h i _ H hp ht hu hl hw hr hV
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
  have hbandY : H.band ≤ Y := by have hh : H.band ≤ Sizes.s n i := H.band_fit; have := H.s_lt_t; omega
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
  have hscaled := Nat.mul_le_mul_left scale hc
  have hpoly : scale*replicaInteriorSharedWorkspace (A := A) (U := U) H hQ R K cVratio ≤
      (scale*D*C^22)*H.t^22*H.p^22 := by
    have heq (a b c d e : ℕ) : a*(b*(c*d*e)^22) = (a*b*c^22)*d^22*e^22 := by ring
    change scale*replicaInteriorSharedWorkspace (A := A) (U := U) H hQ R K cVratio ≤ scale*(D*(C*H.t*H.p)^22) at hscaled
    rw [heq] at hscaled
    exact hscaled
  exact hpoly.trans (by simpa only [hp,ht] using hn i)

end IntegerMultBounds.MathlibTM2.Cost
