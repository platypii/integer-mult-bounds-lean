module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicComplexCaller
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryInputLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoverySeedCopyLedger

/-! Split the ordinary fitting caller's executed input bill before charging
shared headers and per-replica conversion at their actual frequencies. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s T A : ℕ} [NeZero s]

noncomputable def fittingCyclicInputSharedTime (H K : ReplicaHaloProblem s) (W : ℕ) : ℕ :=
  6+(recoverySeedCopyCost H W 0+completeComplexRecoveryHeadersCost H 0+
    (prepareComplexRecoveryInputCost H.span W 0+normalizeRecoveryInputSharedTime H W+2))+
    (recoverySeedCopyCost K W 0+completeComplexRecoveryHeadersCost K 0+
      (prepareComplexRecoveryInputCost K.span W 0+normalizeRecoveryInputSharedTime K W+2))

def fittingCyclicInputRowTime (H K : ReplicaHaloProblem s) (W : ℕ) : ℕ :=
  32*(H.span*W)+26*(K.span*W)+70+
    2*normalizeRecoveryInputRowTime H W+2*normalizeRecoveryInputRowTime K W

theorem fittingCyclicInputTime_affine (ports : CyclicComplexCallerLayout T)
    (H K : ReplicaHaloProblem s) (W N : ℕ) (S : Stacks T A)
    (hH : H.Fs.length = 2*N) (hK : K.Fs.length = 2*N)
    (hleft : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (ports.seedL i)).length = recoverySeedHeader H W N i)
    (hright : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (ports.seedR i)).length = recoverySeedHeader K W N i) :
    ports.inputTimeCost H K W N S =
      fittingCyclicInputSharedTime H K W+N*fittingCyclicInputRowTime H K W := by
  unfold CyclicComplexCallerLayout.inputTimeCost
  rw [recoverySeedCopyCost_eq H W N _ _ S hleft,
    recoverySeedCopyCost_eq K W N _ _ S hright,
    recoverySeedCopyCost_affine H W N,recoverySeedCopyCost_affine K W N]
  unfold prepareCachedComplexInputCost
  rw [normalizeRecoveryInputCost_affine,normalizeRecoveryInputCost_affine,hH,hK]
  unfold fittingCyclicInputSharedTime fittingCyclicInputRowTime
    completeComplexRecoveryHeadersCost prepareComplexRecoveryInputCost
  ring

/-- Conversion traffic stays linear in local coordinates and precision. The
shared scalar bill above contains no replica multiplicity. -/
theorem fittingCyclicInputRowTime_le (H K : ReplicaHaloProblem s) (W cw cW : ℕ)
    (hp : K.p = H.p) (hwH : H.wordWidth ≤ cw*H.p)
    (hwK : K.wordWidth ≤ cw*K.p) (hW : W ≤ cW*H.p) :
    fittingCyclicInputRowTime H K W ≤
      (32*cW+2*(4*cW+12*cw+28)+70)*(H.span+K.span+1)*H.p := by
  have hnH := normalizeRecoveryInputRowTime_le H W cw cW hwH hW
  have hnK := normalizeRecoveryInputRowTime_le K W cw cW hwK (by simpa only [hp] using hW)
  rw [hp] at hnK
  have hvolH := Nat.mul_le_mul_left H.span hW
  have hvolK := Nat.mul_le_mul_left K.span hW
  have hpos := H.p_pos
  unfold fittingCyclicInputRowTime
  nlinarith only [hnH,hnK,hvolH,hvolK,hpos]

/-- Charge the native input trace using the same actual seed headers as its
execution. Only the once-per-batch scalar term remains for shared absorption. -/
theorem fittingCyclicInputWorkspace_le {Q : ℕ} {U : Type}
    (ports : CyclicComplexCallerLayout T) (H K : ReplicaHaloProblem s)
    (W N cw cW : ℕ) (S : Stacks T A)
    (hH : H.Fs.length = 2*N) (hK : K.Fs.length = 2*N)
    (hleft : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (ports.seedL i)).length = recoverySeedHeader H W N i)
    (hright : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (ports.seedR i)).length = recoverySeedHeader K W N i)
    (hp : K.p = H.p) (hwH : H.wordWidth ≤ cw*H.p)
    (hwK : K.wordWidth ≤ cw*K.p) (hW : W ≤ cW*H.p)
    (hspan : H.span+K.span < H.t) :
    fittingCyclicInputPush (Q := Q) (A := A) (U := U)*ports.inputTimeCost H K W N S ≤
      fittingCyclicInputPush (Q := Q) (A := A) (U := U)*fittingCyclicInputSharedTime H K W+
        (fittingCyclicInputPush (Q := Q) (A := A) (U := U)*
          (32*cW+2*(4*cW+12*cw+28)+70))*N*H.t*H.p := by
  have hrow := (fittingCyclicInputRowTime_le H K W cw cW hp hwH hwK hW).trans
    (Nat.mul_le_mul_right H.p (Nat.mul_le_mul_left _ (by omega : H.span+K.span+1 ≤ H.t)))
  have htraffic := Nat.mul_le_mul_left
    (fittingCyclicInputPush (Q := Q) (A := A) (U := U)*N) hrow
  rw [fittingCyclicInputTime_affine ports H K W N S hH hK hleft hright]
  nlinarith only [htraffic]

/-- A coarse shared polynomial suffices; no replica traffic is hidden in it. -/
theorem fittingCyclicInputSharedTime_poly (H K : ReplicaHaloProblem s) (W Z : ℕ)
    (hZ : 1 ≤ Z) (hs : s ≤ Z) (hW : W ≤ Z)
    (hparameters : ∀ D ∈ [H,K], D.p ≤ Z ∧ D.precision ≤ Z ∧ D.wordWidth ≤ Z ∧
      D.stage ≤ Z ∧ D.l ≤ Z ∧ D.t ≤ Z ∧ D.u ≤ Z ∧ D.band ≤ Z) :
    fittingCyclicInputSharedTime H K W ≤ 2000006*Z^2 := by
  have hZsq : Z ≤ Z^2 := by nlinarith only [hZ]
  have hone (D : ReplicaHaloProblem s) (hD : D ∈ [H,K]) :
      recoverySeedCopyCost D W 0+completeComplexRecoveryHeadersCost D 0+
        (prepareComplexRecoveryInputCost D.span W 0+normalizeRecoveryInputSharedTime D W+2) ≤
      1000000*Z^2 := by
    obtain ⟨hp,hq,hw,hstage,hl,ht,hu,hband⟩ := hparameters D hD
    have hfit := D.span_fit
    have ha : D.origin ≤ Z := by omega
    have hn : D.span ≤ Z := by omega
    have hv := Nat.mul_le_mul hn hw
    have hvW := Nat.mul_le_mul hn hW
    have hwidth : 2*D.precision+8 = D.wordWidth := by
      unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
      omega
    have hd : D.precision-D.p-1 ≤ Z := (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hq)
    have hsub : W-D.wordWidth ≤ Z := (Nat.sub_le _ _).trans hW
    have hsub' : D.wordWidth-(D.precision-D.p-1) ≤ Z := (Nat.sub_le _ _).trans hw
    rw [recoverySeedCopyCost_zero_eq]
    simp only [recoveryMasterValues,masterHeaderValues,List.ofFn_succ,List.ofFn_zero,
      List.sum_cons,List.sum_nil,Matrix.cons_val_zero,Matrix.cons_val_succ] 
    unfold completeComplexRecoveryHeadersCost weightWidthCost prepareComplexRecoveryInputCost
      normalizeRecoveryInputSharedTime normalizeRecoveryInputCost packedInputConversionCost
    rw [hwidth]
    simp only [Nat.zero_mul,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
    nlinarith only [hp,hq,hw,hstage,hl,ht,hu,hband,ha,hn,hfit,hs,hW,hZ,hZsq,hv,hvW,hd,hsub,hsub']
  have hH := hone H (by simp)
  have hK := hone K (by simp)
  unfold fittingCyclicInputSharedTime
  nlinarith only [hH,hK,hZsq,hZ]

/-- A reusable axis envelope for the shared bill, before any schedule is summed. -/
theorem fittingCyclicInputSharedTime_axis (H K : ReplicaHaloProblem s) (W p t cw cW : ℕ)
    (hst : s < t) (hp : 1 ≤ p) (hW : W ≤ cW*p)
    (hprofile : ∀ D ∈ [H,K], D.p = p ∧ D.t = t ∧ D.l ≤ 20*p ∧ D.u ≤ p ∧ D.wordWidth ≤ cw*p) :
    fittingCyclicInputSharedTime H K W ≤ 2000006*(cw+cW+21)^2*t^2*p^2 := by
  let C := cw+cW+21
  let Z := C*t*p
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hC : 21 ≤ C := by dsimp only [C]; omega
  have htZ : t ≤ Z := by
    have := Nat.le_mul_of_pos_left t (by omega : 1 ≤ C)
    exact this.trans (Nat.le_mul_of_pos_right (C*t) hp)
  have hsZ : s ≤ Z := hst.le.trans htZ
  have hZ : 1 ≤ Z := ht.trans htZ
  have hparam (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ C) : x ≤ Z := by
    exact hx.trans (Nat.mul_le_mul_right p (hc.trans (Nat.le_mul_of_pos_right C ht)))
  have hpZ : p ≤ Z := hparam p 1 (by simp) (by omega)
  have hshared := fittingCyclicInputSharedTime_poly H K W Z hZ hsZ
    (hparam W cW hW (by dsimp only [C]; omega)) (by
      intro D hD
      obtain ⟨hpD,htD,hlD,huD,hwD⟩ := hprofile D hD
      have hwZ := hparam D.wordWidth cw hwD (by dsimp only [C]; omega)
      have hq : D.precision ≤ D.wordWidth := by
        unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
        omega
      have hstage : D.stage ≤ D.wordWidth := by
        unfold ReplicaHaloProblem.stage ReplicaHaloProblem.wordWidth executionStagePrecision executionWidth
        omega
      have hb : D.band ≤ 17*p := by
        have hsqrt := Nat.sqrt_le_self (16*p/D.u)
        have hdiv := Nat.div_le_self (16*p) D.u
        unfold ReplicaHaloProblem.band PhaseCellBand.width
        rw [hpD]
        change Nat.sqrt (16*p/D.u)+1 ≤ 17*p
        omega
      exact ⟨hpD ▸ hpZ,hq.trans hwZ,hwZ,hstage.trans hwZ,
        hparam _ 20 hlD (by omega),htD ▸ htZ,huD.trans hpZ,
        hparam _ 17 hb (by omega)⟩)
  calc
    _ ≤ 2000006*Z^2 := hshared
    _ = _ := by dsimp only [Z,C]; ring

end IntegerMultBounds.MathlibTM2.Cost
