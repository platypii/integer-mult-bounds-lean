module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellNumericalStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedOriginsStock

/-! The complete ordinary-origin numerical workspace has one shared reserve
and an explicit per-cell native traffic coefficient. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {P₀ U : Type}

noncomputable def cachedOriginsStockPerCell (hQ : SS.states ≤ Q)
    (R p l L t u target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let V := weightWorkspaceWidth (2^15*p) q w t u
  mnProgPush (discardBatchOrigins (P₀ := Empty) (Q := Q) (A := A) (U := U)) * (12*V+9) +
    mnProgPush (cachedGeneratedBatchSetup (P₀ := P₀) (A := A) (U := U) hQ) * (104*(L*w)+15*L+64) +
    stagedCellStockPerCell R cExp (8*p+1) l w L +
    mnProgPush (releaseBatchRuntime (P₀ := Empty) (Q := Q) (A := A) (U := U)) * (96*(L*w)+50*L+21)

theorem cachedOriginsWorkspace_affine (hQ : SS.states ≤ Q)
    (R K p l B L s t u target rhsExp : ℕ) :
    cachedOriginsWorkspace (P₀ := P₀) (A := A) (U := U) hQ R K p l B L s t u target rhsExp =
      cachedOriginsWorkspace (P₀ := P₀) (A := A) (U := U) hQ R K p l 0 L s t u target rhsExp +
        B*cachedOriginsStockPerCell (P₀ := P₀) (A := A) (U := U) hQ R p l L t u target rhsExp := by
  have hw : executionWidth p l target rhsExp = 2*executionPrecision p l target rhsExp+8 := by
    unfold executionWidth executionPrecision
    omega
  unfold cachedOriginsWorkspace cachedClosedWorkspace
  dsimp only
  conv_lhs => rw [cachedSetupWorkspace_affine,stagedCellWorkspace_affine]
  simp only [cachedOriginsStockPerCell,discardBatchOriginsCost,
    releaseBatchRuntimeCost,releaseRuntimePagesCost,swapCellPayloadCost,
    releaseGeneratorPageCost,releaseWeightPageCost,hw]
  ring

private theorem nativeStockTraffic_le (R S C D E L r w V cV : ℕ)
    (hL : 1 ≤ L) (hw : 1 ≤ w) (hV : V ≤ cV*w)
    (hS : S ≤ 8064*(R+1)*(L+r)*w) :
    E*(12*V+9)+C*(104*(L*w)+15*L+64)+S+D*(96*(L*w)+50*L+21) ≤
      (8064*(R+1)+183*C+167*D+(12*cV+9)*E)*(L+r)*w := by
  let x := (L+r)*w
  have hlw : L*w ≤ x := Nat.mul_le_mul_right w (Nat.le_add_right L r)
  have hl : L ≤ x := (Nat.le_mul_of_pos_right L hw).trans hlw
  have hx : 1 ≤ x := hL.trans hl
  have hwidth : w ≤ x := by
    have hh := Nat.mul_le_mul_right w (show 1 ≤ L+r by omega)
    simpa only [one_mul,x] using hh
  have hVx : V ≤ cV*x := hV.trans (Nat.mul_le_mul_left cV hwidth)
  have hpacket := Nat.mul_le_mul_left E (show 12*V+9 ≤ (12*cV+9)*x by nlinarith only [hVx,hx])
  have hsetup := Nat.mul_le_mul_left C (show 104*(L*w)+15*L+64 ≤ 183*x by omega)
  have hrelease := Nat.mul_le_mul_left D (show 96*(L*w)+50*L+21 ≤ 167*x by omega)
  have hS' : S ≤ 8064*(R+1)*x := by simpa only [x,Nat.mul_assoc] using hS
  calc
    _ ≤ (8064*(R+1)+183*C+167*D+(12*cV+9)*E)*x := by
      nlinarith only [hpacket,hsetup,hrelease,hS']
    _ = _ := by dsimp only [x]; ring

noncomputable def cachedOriginsTrafficFactor (hQ : SS.states ≤ Q) (R cV : ℕ) : ℕ :=
  8064*(R+1)+
    183*mnProgPush (cachedGeneratedBatchSetup (P₀ := P₀) (A := A) (U := U) hQ)+
    167*mnProgPush (releaseBatchRuntime (P₀ := Empty) (Q := Q) (A := A) (U := U))+
    (12*cV+9)*mnProgPush (discardBatchOrigins (P₀ := Empty) (Q := Q) (A := A) (U := U))

/-- With linear control-word width, the whole repeated allowance is encoded traffic. -/
theorem cachedOriginsStockPerCell_le (hQ : SS.states ≤ Q)
    (R p l L t u target rhsExp cV : ℕ) (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    cachedOriginsStockPerCell (P₀ := P₀) (A := A) (U := U) hQ R p l L t u target rhsExp ≤
      cachedOriginsTrafficFactor (P₀ := P₀) (A := A) (U := U) hQ R cV *
        (L+2^l)*executionWidth p l target rhsExp := by
  have hw : 1 ≤ executionWidth p l target rhsExp := by unfold executionWidth; omega
  have hshift : sourceExponent l target rhsExp+(8*p+1)+2*l+3 ≤ executionWidth p l target rhsExp := by
    have hh := execution_width_bound p l target rhsExp
    unfold inputExponent at hh
    omega
  exact nativeStockTraffic_le _ _ _ _ _ _ _ _ _ _ hL hw hV
    (stagedCellStockPerCell_le _ _ _ _ _ _ hL hw hshift)

theorem cachedOriginsWorkspace_le_shared_add_traffic (hQ : SS.states ≤ Q)
    (R K p l B L s t u target rhsExp cV : ℕ) (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    cachedOriginsWorkspace (P₀ := P₀) (A := A) (U := U) hQ R K p l B L s t u target rhsExp ≤
      cachedOriginsWorkspace (P₀ := P₀) (A := A) (U := U) hQ R K p l 0 L s t u target rhsExp +
        cachedOriginsTrafficFactor (P₀ := P₀) (A := A) (U := U) hQ R cV *
          B*(L+2^l)*executionWidth p l target rhsExp := by
  rw [cachedOriginsWorkspace_affine]
  have hs := Nat.mul_le_mul_left B
    (cachedOriginsStockPerCell_le (P₀ := P₀) (A := A) (U := U) hQ R p l L t u target rhsExp cV hL hV)
  calc
    _ ≤ _ := Nat.add_le_add_left hs _
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
