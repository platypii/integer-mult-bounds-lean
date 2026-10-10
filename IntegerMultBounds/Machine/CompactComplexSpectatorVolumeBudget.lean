import IntegerMultBounds.Machine.CompactComplexSpectatorVolumeHeaders
import IntegerMultBounds.Machine.CompactNativeRoleOriginalBudget

/-! Genuine stream-volume header synthesis and cleanup are bounded by native
volume, and by one complete role stream with a fixed header-count factor. -/
namespace IntegerMultBounds.Machine.CompactComplexSpectatorVolumeBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexSpectatorVolumeHeaders
open ButterflyAxisHeadersArithmetic
open CompactNativeRoleTransferBudget (volume)

def constant (headerCount : ℕ) :=
  CompactNativeRoleHeaderBudget.constant headerCount+3000+100*(headerCount+1)

theorem setup_cleanup_native (sh : Shape)
    (headerCount rows ell metadataP rho left count slots right source target : ℕ)
    (merge : Bool) (hr : 0<rows) (hA : 0<sh.axes) (hG : 0<sh.guard) (hK : 0<sh.chunk) :
    scheduleCost (CompactNativeRoleHeaders.schedule headerCount merge)
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right source target)+
    scheduleCost CompactNativeRoleHeaders.cleanup
      (CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right source target)≤
    constant headerCount*volume rows sh ell metadataP := by
  have hs := CompactNativeRoleHeaderBudget.headers_linear headerCount merge sh rows ell metadataP
    rho left count slots right source target hr hA hG hK
  have hc := CompactNativeRoleOriginalBudget.cleanup_linear headerCount merge sh rows ell metadataP
    rho left count slots right source target hr
  unfold constant
  nlinarith

/-- Even when the outer row count is not divisible, a positive quotient loses
at most a factor two in passing from parent rows to one role's rows. -/
theorem rows_le (headerCount rows : ℕ) (merge : Bool)
    (hc : 0<headerCount) (hq : 0<rows/headerCount) :
    rows≤(2*headerCount)*roleRows headerCount rows merge := by
  cases merge
  · simp only [roleRows,Bool.false_eq_true,ite_false]
    exact Nat.le_mul_of_pos_left _ (by omega)
  · simp only [roleRows,ite_true]
    have hm := Nat.mod_lt rows hc
    have he := Nat.mod_add_div rows headerCount
    have hqmul := Nat.mul_le_mul_left headerCount (by omega : 1≤rows/headerCount)
    nlinarith

theorem native_le_stream (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hc : 0<headerCount) (hq : 0<rows/headerCount) :
    volume rows sh ell metadataP≤(2*headerCount)*streamVolume sh headerCount rows ell metadataP merge := by
  have h := Nat.mul_le_mul_right (CompactNativeRoleOriginal.symbols sh ell metadataP)
    (rows_le headerCount rows merge hc hq)
  simpa only [volume,CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner,
    streamVolume,CompactNativeRoleHeaders.recordWidth,Nat.mul_assoc] using h

def streamConstant (headerCount : ℕ) := constant headerCount*(2*headerCount)

theorem setup_cleanup_stream (sh : Shape)
    (headerCount rows ell metadataP rho left count slots right source target : ℕ)
    (merge : Bool) (hc : 0<headerCount) (hr : 0<rows) (hq : 0<rows/headerCount)
    (hA : 0<sh.axes) (hG : 0<sh.guard) (hK : 0<sh.chunk) :
    scheduleCost (CompactNativeRoleHeaders.schedule headerCount merge)
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right source target)+
    scheduleCost CompactNativeRoleHeaders.cleanup
      (CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right source target)≤
    streamConstant headerCount*streamVolume sh headerCount rows ell metadataP merge := by
  exact (setup_cleanup_native sh headerCount rows ell metadataP rho left count slots right source target
    merge hr hA hG hK).trans (by
      simpa only [streamConstant,Nat.mul_assoc] using
        Nat.mul_le_mul_left (constant headerCount) (native_le_stream sh headerCount rows ell metadataP merge hc hq))

end
end IntegerMultBounds.Machine.CompactComplexSpectatorVolumeBudget
