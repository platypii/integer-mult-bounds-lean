import IntegerMultBounds.Machine.NativeEndpointCharacterOriginal
import IntegerMultBounds.Machine.NativeEndpointCharacterBudget

/-! Original raw-header character preparation, including the actual role-row
quotient, is paid by the original parent native polynomial volume. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterOriginalBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactNativeRoleTransferBudget (volume)
open ButterflyAxisHeadersArithmetic
variable {s : Shape} {t : ℕ}
attribute [local irreducible] volume NativePolynomialStageHeaders.cost

private theorem scalar_words (v : Stage s) (rows ell p : ℕ) :
    ∀ i,Counter.value (NativeEndpointCharacterCopy.words v rows ell p i)≤
      CompactSpectatorLeafSetupBudget.scalar s rows ell p v.rho v.left v.f v.slots v.right
        v.source.val v.target.val := by
  intro i
  rw [NativeEndpointCharacterCopy.words,RecursiveChildQuotientsConstant.bits_value]
  fin_cases i <;> simp [NativeEndpointCharacterCopy.index,NativeEndpointCharacterPrepare.raw,
    CompactSpectatorLeafSetup.raw]
  all_goals unfold CompactSpectatorLeafSetupBudget.scalar; omega

private theorem copy_bound (v : Stage s) (rows ell p : ℕ)
    (hr : 0<rows) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) (hpay : s.payload=1) :
    FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 15) (NativeEndpointCharacterCopy.words v rows ell p)≤
      2700*volume rows s ell p := by
  have hs := NativePolynomialStageHeaderBudget.scalar_le v rows ell p hr hA hG hK hpay
  have hV : 0<volume rows s ell p := by
    simpa only [volume] using Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have hc := FixedHeaderBankCopy.cost_linear (NativeEndpointCharacterCopy.words v rows ell p)
    (18*volume rows s ell p) (by positivity)
    (fun _ => RecursiveChildQuotientsConstant.bits_canonical _)
    (fun i => (scalar_words v rows ell p i).trans hs)
  nlinarith

private theorem finish_bound (c : ℕ) (v : Stage s) (rows ell p : ℕ) :
    scheduleCost (NativeEndpointCharacterPrepare.finishSchedule c)
      (NativeEndpointCharacterPrepare.prepared v rows ell p)≤
      BinaryDescriptorDivision.cost (RecursiveChildQuotientsConstant.bits rows)
        (RecursiveChildQuotientsConstant.bits c)+1000*(s.payload+rows+ell+p+c+1) := by
  have hl := ActiveRepairRankHeadersCommands.bits_length c
  have hq := Nat.div_le_self rows c
  simp [NativeEndpointCharacterPrepare.finishSchedule,scheduleCost,cost,eval,
    CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    NativeEndpointCharacterPrepare.prepared,NativePolynomialStageHeaders.prepared,
    ActiveRepairRankHeadersCommands.put,CompactSpectatorLeafSetup.raw,Function.update,
    RecursiveChildQuotientsConstant.cost]
  omega

private theorem prepare_bound (c : ℕ) (v : Stage s) (rows ell p : ℕ)
    (hr : 0<rows) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) (hpay : s.payload=1) :
    NativeEndpointCharacterPrepare.cost c v rows ell p≤
      (NativePolynomialStageHeaderBudget.constant+200000+12000*(c+1))*volume rows s ell p := by
  have hn := NativePolynomialStageHeaderBudget.lifecycle_linear v rows ell p hr hA hG hK hpay
  have hn' : NativePolynomialStageHeaders.cost s rows ell p v.rho v.left v.f v.slots v.right
      v.source.val v.target.val≤NativePolynomialStageHeaderBudget.constant*volume rows s ell p := by omega
  clear hn
  have hs := NativePolynomialStageHeaderBudget.scalar_le v rows ell p hr hA hG hK hpay
  have hf := finish_bound c v rows ell p
  have hd := CompactNativeRoleHeaderBudget.quotient_linear rows c hr
  have hl := ActiveRepairRankHeadersCommands.bits_length ell
  have hv := (CompactNativeRoleHeaderBudget.values_le s rows ell p hr).2.2.2.2.2.2.2
  have hV : 0<volume rows s ell p := by
    simpa only [volume] using Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have hcv : c≤c*volume rows s ell p := Nat.le_mul_of_pos_right c hV
  unfold CompactSpectatorLeafSetupBudget.scalar at hs
  have hbasic : s.payload+rows+ell+p+1≤18*volume rows s ell p := by omega
  have hell : ell≤18*volume rows s ell p := by omega
  clear hs
  unfold NativeEndpointCharacterPrepare.cost
  nlinarith only [hn',hbasic,hell,hf,hd,hl,hv,hV,hcv]

def constant (c : ℕ) := NativePolynomialStageHeaderBudget.constant+202704+12000*(c+1)+
  3*NativeEndpointCharacterBudget.constant

theorem cost_linear (c : ℕ) (order : ActivePrefixStageHeadersData.Order)
    (v : Stage s) (parentRows ell p : ℕ)
    (hr : 0<parentRows/c) (hA : 0<s.axes) (hG : 0<s.guard)
    (hGK : s.guard+1≤s.chunk) (hpay : s.payload=1)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order v) :
    NativeEndpointCharacterOriginal.cost (t:=t) c order v parentRows ell p≤
      constant c*volume parentRows s ell p := by
  have hparent : 0<parentRows := lt_of_lt_of_le hr (Nat.div_le_self parentRows c)
  have hK : 0<s.chunk := by omega
  have hcopy := copy_bound v parentRows ell p hparent hA hG hK hpay
  have hprepare := prepare_bound c v parentRows ell p hparent hA hG hK hpay
  let v' := NativePolynomialStageShape.stage v ell p
  let rows := parentRows/c
  have ho' : ActivePrefixStageHeadersSchedule.Ordered order v' := ho
  have hG' : 1≤(NativePolynomialStageShape.shape s ell p).guard := hG
  have hGK' : (NativePolynomialStageShape.shape s ell p).guard+1≤
      (NativePolynomialStageShape.shape s ell p).chunk := hGK
  have hR : 2^ell≤(NativePolynomialStageShape.shape s ell p).payload := by
    change 2^ell≤2*(NativePolynomialStageShape.width s p+1)*2^ell*3
    have h := Nat.mul_le_mul_right (2^ell) (by omega : 1≤2*(NativePolynomialStageShape.width s p+1)*3)
    simpa only [one_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
  have hw : 2^ell*NativePolynomialStageShape.width s p≤
      (NativePolynomialStageShape.shape s ell p).payload := by
    change 2^ell*NativePolynomialStageShape.width s p≤2*(NativePolynomialStageShape.width s p+1)*2^ell*3
    have h := Nat.mul_le_mul_right (2^ell) (by omega : NativePolynomialStageShape.width s p≤2*(NativePolynomialStageShape.width s p+1)*3)
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
  have hm : 0<v.slots := by have := v.source.isLt; omega
  have hphase := NativeEndpointCharacterBudget.cost_linear (t:=t) order v' rows v.slots ell
    (NativePolynomialStageShape.width s p) hG' hGK' ho' hr hm le_rfl
    (NativeEndpointCharacterAddress.span v') (NativePolynomialStageShape.payload_fits s ell p) hR hw
  have hvol := NativePolynomialStageHeaderBudget.expanded_volume s rows ell p
  have hmon : volume rows s ell p≤volume parentRows s ell p := by
    unfold volume
    exact Nat.mul_le_mul_right _ (Nat.div_le_self parentRows c)
  have hphase' : NativeEndpointCharacterLifecycle.cost (t:=t) order v' rows v.slots ell
      (NativePolynomialStageShape.width s p)≤3*NativeEndpointCharacterBudget.constant*volume parentRows s ell p := by
    rw [hvol] at hphase
    exact hphase.trans (by nlinarith)
  have hV : 0<volume parentRows s ell p := by
    simpa only [volume] using Nat.mul_pos hparent (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  unfold NativeEndpointCharacterOriginal.cost NativeEndpointCharacterLifecycle.cost at *
  unfold constant
  dsimp only [v',rows] at *
  nlinarith

end
end IntegerMultBounds.Machine.NativeEndpointCharacterOriginalBudget
