module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellUniformHaloWorkspacePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeometryControlSizing
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginPacketWidths

/-! Selected geometry discharges every dimension of the actual uniform halo reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

@[irreducible] def uniformHaloEnvelopeCoefficient (J R K cw : ℕ) : ℕ :=
  J+R+K+3000000*cw^2+100*cw+500000

private theorem uniformHaloEnvelopeCoefficient_bounds (J R K cw : ℕ) :
    let C := uniformHaloEnvelopeCoefficient J R K cw
    21 ≤ C ∧ J ≤ C ∧ R ≤ C ∧ K ≤ C ∧ cw ≤ C ∧ 2*cw+426009 ≤ C ∧
      4*cw+12 ≤ C ∧ 3000000*cw^2+10 ≤ C ∧ 32768 ≤ C := by
  dsimp only
  unfold uniformHaloEnvelopeCoefficient
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

theorem selectedSolveHaloInteriorUniformWorkspace_le (J R K cw scale : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ u target rhsExp : ℕ,
      let p := Sizes.p m
      let s := Sizes.s m i
      let t := Sizes.t m i
      let l := haloInverseRingLog s t
      executionWidth p l target rhsExp ≤ cw*p → u ≤ p → PhaseCellBand.width p u ≤ s →
      scale*solveHaloInteriorUniformWorkspace J R K p l s t u target rhsExp ≤ Sizes.T m := by
  let C := uniformHaloEnvelopeCoefficient J R K cw
  obtain ⟨hbaseC,hJC,hRC,hKC,hcwC,hVC,hprecC,hgenC,hPC⟩ := uniformHaloEnvelopeCoefficient_bounds J R K cw
  filter_upwards [selectedAxisPolynomial_le_volume (scale*uniformHaloWorkspaceConstant*C^11) 22 11] with m hv
  intro h i _ u target rhsExp
  dsimp only
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let Z := C*t*p^2
  intro hw hu hb
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hst : s < t := h.good.lt i
  have hC : 1 ≤ C := by omega
  have hp₂ : p ≤ p^2 := Nat.le_self_pow (by decide) p
  have hp₂pos : 1 ≤ p^2 := Nat.one_le_pow _ _ hp
  have hZ : 1 ≤ Z := Nat.mul_pos (Nat.mul_pos hC ht) hp₂pos
  have hCZ : C ≤ Z := by
    have ha := Nat.mul_le_mul_left C ht
    have hb := Nat.mul_le_mul_left (C*t) hp₂pos
    dsimp only [Z]; omega
  have hconst (x : ℕ) (hx : x ≤ C) : x ≤ Z := hx.trans hCZ
  have hlinear (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ C) : x ≤ Z := by
    have ha := Nat.mul_le_mul_left c hp₂
    have hb := Nat.mul_le_mul_right (p^2) hc
    have hd := Nat.mul_le_mul_left (C*p^2) ht
    dsimp only [Z]; nlinarith only [hx,ha,hb,hd]
  have htZ : t ≤ Z := by
    have ha := Nat.mul_le_mul_right t hC
    have hb := Nat.mul_le_mul_left (C*t) hp₂pos
    dsimp only [Z]; nlinarith only [ha,hb]
  have hqW : q ≤ w := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  have hlW : l ≤ w := by unfold w executionWidth executionExponent inputExponent sourceExponent; omega
  have hsourceW : sourceExponent l target rhsExp ≤ w := by
    unfold w executionWidth executionExponent inputExponent; omega
  have hstageW : executionStagePrecision p l target rhsExp+1 ≤ w := by
    unfold w executionWidth executionStagePrecision executionExponent inputExponent; omega
  have hwidth : w = 2*q+8 := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  have hwZ := hlinear w cw hw hcwC
  have hpZ := hlinear p 1 (by omega) hC
  have hV := selectedWeightWorkspaceWidth_le cw h i q w u hw hqW hu
  have hVZ : weightWorkspaceWidth (2^15*p) q (2*q+8) t u ≤ Z := by
    rw [←hwidth]
    exact hlinear _ (2*cw+426009) hV hVC
  have hGZ := (haloGeometryWidth_le_weightWorkspaceWidth (2^15*p) q (2*q+8) t u).trans hVZ
  have hring := (haloInverseRingLog_bounds hp hst (h.quarter_p_le_theta i)).2
  have hrZ := hlinear (2^l) 20 hring (by omega)
  have hprecisionZ := hlinear (q+sourceExponent l target rhsExp+(8*p+1)+2*l+3) (4*cw+12)
    (by nlinarith only [hw,hqW,hlW,hsourceW,hp]) hprecC
  have hlengthZ := hlinear (4*p+1) 5 (by omega) (by omega)
  have hE : p+l+target+rhsExp+1 ≤ cw*p := by
    apply (show p+l+target+rhsExp+1 ≤ w by
      unfold w executionWidth executionExponent inputExponent sourceExponent; omega).trans hw
  have hE₂ := Nat.pow_le_pow_left hE 2
  have hsizeT : Nat.size t ≤ t := Nat.size_le.mpr Nat.lt_two_pow_self
  have hsizeU : Nat.size u ≤ p := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hu
  have hsizeB : Nat.size band ≤ t := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (hb.trans hst.le)
  have hbase : p^2 ≤ t*p^2 := Nat.le_mul_of_pos_left _ ht
  have htbase : t ≤ t*p^2 := Nat.le_mul_of_pos_right _ hp₂pos
  have hscaled := Nat.mul_le_mul_left (3000000*cw^2) hbase
  have hgen : generatedSetupScale p l target rhsExp t u band ≤ (3000000*cw^2+10)*t*p^2 := by
    unfold generatedSetupScale
    nlinarith only [hE₂,hsizeT,hsizeU,hsizeB,hbase,htbase,hscaled,hp₂,hp]
  have hgenZ : generatedSetupScale p l target rhsExp t u band ≤ Z := by
    apply hgen.trans
    have hm := Nat.mul_le_mul_right (t*p^2) hgenC
    simpa only [Z,Nat.mul_assoc] using hm
  have hratio := phaseGap_cellLength_le hp hst (h.quarter_p_le_theta i)
  have hL : (s/(t-s)+1)-2*band ≤ 4*p+1 := by omega
  have hpoly := solveHaloInteriorUniformWorkspace_poly J R K p l s t u target rhsExp Z hZ hL (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hconst _ hJC
    · exact hconst _ hRC
    · exact hconst _ hKC
    · exact hlinear _ (2^15) le_rfl (by simpa only [show (2 : ℕ)^15 = 32768 by norm_num] using hPC)
    · exact hlW.trans hwZ
    · exact hst.le.trans htZ
    · exact htZ
    · exact hu.trans hpZ
    · exact hb.trans (hst.le.trans htZ)
    · exact hstageW.trans hwZ
    · exact hqW.trans hwZ
    · exact hwZ
    · exact hrZ
    · exact hlengthZ
    · exact hgenZ
    · exact hVZ
    · exact hGZ
    · exact hprecisionZ)
  have hscaledPoly := Nat.mul_le_mul_left scale hpoly
  have heq : scale*(uniformHaloWorkspaceConstant*Z^11) =
      (scale*uniformHaloWorkspaceConstant*C^11)*t^11*p^22 := by dsimp only [Z]; ring
  rw [heq] at hscaledPoly
  exact hscaledPoly.trans (hv i)

end IntegerMultBounds.MathlibTM2.Cost
