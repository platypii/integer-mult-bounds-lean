module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaPublicationPages

/-! Publication pages are shared scalar setup, independent of replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

private theorem publicationPagesCost_le {V s L W k t cV cW : ℕ}
    (ht : 1 ≤ t) (hs : s ≤ t) (hL : L ≤ t) (hk : k ≤ t)
    (hV : V ≤ cV*t) (hW : W ≤ cW*t) :
    prepareReplicaPublicationPagesCost V s L W k ≤
      (3*(32*(cV+4)^2+8*cV)+105*cV+59*cW+4*cW*cV+175)*t^3 := by
  let H := 32*(cV+4)^2+8*cV
  have htSq : t ≤ t^2 := Nat.le_self_pow (by decide) t
  have htCube : t^2 ≤ t^3 := Nat.pow_le_pow_right ht (by decide)
  have htToCube := htSq.trans htCube
  have hone := ht.trans htToCube
  have hwidth : V+4 ≤ (cV+4)*t := by nlinarith only [hV,ht]
  have htable : tblC V V ≤ H*t^2 := by
    have hp := Nat.pow_le_pow_left hwidth 2
    have hv := hV.trans (Nat.mul_le_mul_left cV htSq)
    unfold tblC
    dsimp only [H]
    nlinarith only [hp,hv]
  have hktable := Nat.mul_le_mul hk htable
  have hkV := Nat.mul_le_mul hk hV
  have hWV := Nat.mul_le_mul hW hV
  have hsW := Nat.mul_le_mul hs hW
  have hLW := Nat.mul_le_mul hL hW
  have hkC := hk.trans htToCube
  have hLC := hL.trans htToCube
  have hVC := hV.trans (Nat.mul_le_mul_left cV htToCube)
  have hWC := hW.trans (Nat.mul_le_mul_left cW htToCube)
  have hkvC := Nat.mul_le_mul_left cV htCube
  have hwvC := Nat.mul_le_mul_left (cW*cV) htCube
  have hwC := Nat.mul_le_mul_left cW htCube
  unfold prepareReplicaPublicationPagesCost preparedOriginAdvanceCost
  change _ ≤ (3*H+105*cV+59*cW+4*cW*cV+175)*t^3
  nlinarith only [hktable,hkV,hWV,hsW,hLW,hkC,hLC,hVC,hWC,hkvC,hwvC,hwC,hone]

theorem selectedPublicationPagesCost_le (cV cW scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ V L W k : ℕ, V ≤ cV*Sizes.p n → W ≤ cW*Sizes.p n →
      L ≤ Sizes.s n i → k ≤ Sizes.s n i →
      scale*prepareReplicaPublicationPagesCost V (Sizes.s n i) L W k ≤ Sizes.T n := by
  let C := 3*(32*(cV+4)^2+8*cV)+105*cV+59*cW+4*cW*cV+175
  filter_upwards [selectedAxisPolynomial_le_volume (scale*C) 0 3] with n hn
  intro h i V L W k hV hW hL hk
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpt := selectedPrecision_le_axis h i
  have hs := (h.good.lt i).le
  have hc := publicationPagesCost_le (hp.trans hpt) hs (hL.trans hs) (hk.trans hs)
    (hV.trans (Nat.mul_le_mul_left cV hpt)) (hW.trans (Nat.mul_le_mul_left cW hpt))
  exact (Nat.mul_le_mul_left scale hc).trans (by
    simpa only [C,pow_zero,mul_one,Nat.mul_assoc] using hn i)

end IntegerMultBounds.MathlibTM2.Cost
