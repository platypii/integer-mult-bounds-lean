module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryNumericalWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolvePushBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloProblem

/-! The retained boundary solver's real numerical scratch fits the selected volume allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedBoundarySolveWorkspace_volume_le (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (cw scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      ∀ H : ReplicaHaloProblem (Sizes.s n i), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.wordWidth ≤ cw*H.p →
      scale*push.workspace H.precision H.wordWidth
        (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1) ≤ Sizes.T n := by
  let C := push.normalize+push.unscale+push.reciprocal+push.column+cw+20
  let K := 100000*(ssMulConst+1)
  filter_upwards [selectedAxisPolynomial_le_volume (scale*K*C^4) 4 4] with n hn
  intro h i _ H hp ht hw
  let Z := C*H.t*H.p
  have htpos : 1 ≤ H.t := by have := H.s_lt_t; omega
  have hppos := H.p_pos
  have hC : 1 ≤ C := by dsimp only [C]; omega
  have hZ : 1 ≤ Z := Nat.mul_pos (Nat.mul_pos hC htpos) hppos
  have hCZ : C ≤ Z := by
    have ha := Nat.mul_le_mul_left C htpos
    have hb := Nat.mul_le_mul_left (C*H.t) hppos
    dsimp only [Z]; omega
  have hwZ : H.wordWidth ≤ Z := by
    have ha := Nat.mul_le_mul_right H.p (show cw ≤ C by dsimp only [C]; omega)
    have hb := Nat.mul_le_mul_left (C*H.p) htpos
    dsimp only [Z]; nlinarith only [hw,ha,hb]
  have hqZ : H.precision ≤ Z := by
    have hh : H.precision ≤ H.wordWidth := by
      unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
      omega
    exact hh.trans hwZ
  have hWZ : 12*H.band+1 ≤ Z := by
    have hb : H.band ≤ H.t := H.band_fit.trans H.s_lt_t.le
    have hC13 : 13 ≤ C := by dsimp only [C]; omega
    have ha := Nat.mul_le_mul_right H.t hC13
    have hm := Nat.mul_le_mul_left (C*H.t) hppos
    dsimp only [Z]; nlinarith only [hb,htpos,ha,hm]
  have hNZ : (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card ≤ Z := by
    have hh : (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card ≤ Sizes.s n i := by
      simpa only [ZMod.card] using (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card_le_univ
    have hCt : H.t ≤ Z := by
      have ha := Nat.mul_le_mul_right H.t hC
      have hm := Nat.mul_le_mul_left (C*H.t) hppos
      dsimp only [Z]; nlinarith only [ha,hm]
    exact hh.trans (H.s_lt_t.le.trans hCt)
  have hc := preparedResidualSolveWorkspace_poly hZ
    ((show push.normalize ≤ C by dsimp only [C]; omega).trans hCZ)
    ((show push.unscale ≤ C by dsimp only [C]; omega).trans hCZ)
    ((show push.reciprocal ≤ C by dsimp only [C]; omega).trans hCZ)
    ((show push.column ≤ C by dsimp only [C]; omega).trans hCZ) hqZ hwZ hNZ hWZ
  have hscaled := Nat.mul_le_mul_left scale hc
  have heq (a b c d e : ℕ) : a*(b*(c*d*e)^4) = (a*b*c^4)*d^4*e^4 := by ring
  change scale*push.workspace H.precision H.wordWidth _ _ ≤ scale*(K*(C*H.t*H.p)^4) at hscaled
  rw [heq] at hscaled
  exact hscaled.trans (by simpa only [hp,ht] using hn i)

end IntegerMultBounds.MathlibTM2.Cost
