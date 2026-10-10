import IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalOriginal

namespace IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalOriginalBudget
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

private theorem normalization_bound (v : Stage s) (rows ell p : ℕ)
    (hr : 0<rows) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) (hpay : s.payload=1) :
    scheduleCost NativeEndpointCharacterCanonical.schedule
      (NativeEndpointCharacterPrepare.raw v rows ell p)≤4000*volume rows s ell p := by
  have hs := NativePolynomialStageHeaderBudget.scalar_le v rows ell p hr hA hG hK hpay
  have hl := ActiveRepairRankHeadersCommands.bits_length v.source.val
  have ht := ActiveRepairRankHeadersCommands.bits_length v.target.val
  have hzero := ActiveRepairRankHeadersCommands.bits_length 0
  have hone := ActiveRepairRankHeadersCommands.bits_length 1
  have hV : 0<volume rows s ell p := by
    simpa only [volume] using Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  unfold CompactSpectatorLeafSetupBudget.scalar at hs
  simp [NativeEndpointCharacterCanonical.schedule,scheduleCost,cost,eval,
    CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    Function.update,
    NativeEndpointCharacterPrepare.raw,CompactSpectatorLeafSetup.raw,
    RecursiveChildQuotientsConstant.cost]
  omega

def constant (c : ℕ) := NativeEndpointCharacterOriginalBudget.constant c+6701

theorem cost_linear (c : ℕ) (v : Stage s) (rows ell p : ℕ)
    (hr : 0<rows/c) (hA : 0<s.axes) (hG : 0<s.guard)
    (hGK : s.guard+1≤s.chunk) (hpay : s.payload=1) :
    NativeEndpointCharacterCanonicalOriginal.cost (t:=t) c v rows ell p≤
      constant c*volume rows s ell p := by
  have hparent : 0<rows := lt_of_lt_of_le hr (Nat.div_le_self rows c)
  have hK : 0<s.chunk := by omega
  have hcopy := copy_bound v rows ell p hparent hA hG hK hpay
  have hnorm := normalization_bound v rows ell p hparent hA hG hK hpay
  have horiginal := NativeEndpointCharacterOriginalBudget.cost_linear (t:=t) c .early
    (NativeEndpointCharacterCanonical.stage v) rows ell p hr hA hG hGK hpay
    (NativeEndpointCharacterCanonical.ordered v)
  have hV : 0<volume rows s ell p := by
    simpa only [volume] using Nat.mul_pos hparent (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  unfold NativeEndpointCharacterCanonicalOriginal.cost NativeEndpointCharacterOriginal.cost at *
  dsimp only [NativeEndpointCharacterCanonical.stage] at *
  unfold constant
  nlinarith

end
end IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalOriginalBudget
