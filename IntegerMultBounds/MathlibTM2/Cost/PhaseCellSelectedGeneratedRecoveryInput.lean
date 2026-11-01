module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryInputBank
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFirstCachedReplicaRecoveryTotal
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Initial ordinary headers cost one shared volume reserve; the packed input
archive costs linear replica payload. Global input/output tapes stay explicit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

private theorem generatedRecoveryHeaderStock_le {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    {cw cV : ℕ} (hp : 1 ≤ H.p) (ht : 1 ≤ H.t) (hl : H.l ≤ 20*H.p)
    (hu : H.u ≤ H.p) (hw : H.wordWidth ≤ cw*H.p) (hV : H.metadataWidth ≤ cV*H.p) :
    generatedRecoveryHeaderStock H ≤ (50000+4*cw+cV)*H.t*H.p+H.Fs.length := by
  have hq : H.precision ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  have hstage : H.stage+1 ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.stage ReplicaHaloProblem.wordWidth executionStagePrecision executionWidth
    omega
  have hs := H.s_lt_t.le
  have hab : H.origin+H.span ≤ H.t := H.span_fit.trans hs
  have ha : H.origin ≤ H.t := by omega
  have hspan : H.span ≤ H.t := by omega
  have hb : H.band ≤ 17*H.p := by
    have hh := Nat.sqrt_le_self (16*H.p/H.u)
    have hd := Nat.div_le_self (16*H.p) H.u
    unfold ReplicaHaloProblem.band PhaseCellBand.width
    omega
  have hvolume := Nat.mul_le_mul hspan hw
  have htp : H.p ≤ H.t*H.p := Nat.le_mul_of_pos_left _ ht
  have htt : H.t ≤ H.t*H.p := Nat.le_mul_of_pos_right _ hp
  have hcw := Nat.mul_le_mul_left cw htp
  have hcv := Nat.mul_le_mul_left cV htp
  unfold generatedRecoveryHeaderStock
  norm_num only [show 2^15 = 32768 by norm_num]
  nlinarith only [hq,hstage,hs,hab,ha,hl,hu,hw,hV,hb,hvolume,htp,htt,hcw,hcv]

theorem selectedGeneratedRecoveryInput_stock_le (ct ce : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) → H.u ≤ Sizes.p n →
      H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ (inp : List (Bool ⊕ Bool)) (out : List Bool) (v : HS 392 Q A U),
      mnSize (mk v (generatedRecoveryInput (A := A) H inp out)) ≤
        inp.length+out.length+Sizes.T n+C*H.Fs.length*H.t*H.p := by
  let cw := 16*20+8*ct+8*ce+128
  let cV := (2*cw+426009)*cw
  let cHead := 50000+4*cw+cV
  refine ⟨392+cw,?_⟩
  filter_upwards [selectedAxisPolynomial_le_volume (392*cHead) 1 1] with n hv
  intro h i _ H hp ht hl hu htarget hrhs inp out v
  obtain ⟨_,_,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hwH : H.wordWidth ≤ cw*H.p := by simpa only [ReplicaHaloProblem.wordWidth,hp,hl,cw] using hw
  have hVH : H.metadataWidth ≤ cV*H.p := by
    have hh : H.metadataWidth ≤ (2*cw+426009)*H.wordWidth := by
      simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hV
    exact hh.trans (by simpa only [cV,Nat.mul_assoc] using Nat.mul_le_mul_left (2*cw+426009) hwH)
  have hp1 : 1 ≤ H.p := by have := h.thirteen_le_p; omega
  have ht1 : 1 ≤ H.t := by have := H.s_lt_t; omega
  obtain ⟨hl20,_⟩ := haloInverseRingLog_bounds (by simpa only [hp] using hp1) (h.good.lt i) (h.quarter_p_le_theta i)
  have hheaders := generatedRecoveryHeaderStock_le H hp1 ht1 (by simpa only [hl,hp] using hl20)
    (by simpa only [hp] using hu) hwH hVH
  have hshared : 392*cHead*H.t*H.p ≤ Sizes.T n := by simpa only [pow_one,←ht,←hp] using hv i
  have hspan : H.span ≤ H.t := by have := H.span_fit; have := H.s_lt_t; omega
  have hpayload := Nat.mul_le_mul_left H.Fs.length (Nat.mul_le_mul hspan hwH)
  have hcount := Nat.mul_le_mul_left H.Fs.length (show 1 ≤ H.t*H.p from Nat.mul_pos ht1 hp1)
  have hinit := generatedRecoveryInput_stock_le H inp out v
  change generatedRecoveryHeaderStock H ≤ cHead*H.t*H.p+H.Fs.length at hheaders
  nlinarith only [hinit,hheaders,hshared,hpayload,hcount]

end IntegerMultBounds.MathlibTM2.Cost
