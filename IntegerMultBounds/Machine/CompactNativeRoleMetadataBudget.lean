import IntegerMultBounds.Machine.CompactNativeRoleMergeCaller
import IntegerMultBounds.Machine.CompactNativeRoleOriginalBudget

/-! Final copied metadata erasure is paid from actual Stage geometry. Combined
arbitrary-result merging includes every source reset, header lifecycle and the
final return to the retained global scalar caller. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleMetadataBudget
noncomputable section
open CompactNativeRoleTransferBudget (volume)
open CompactNativeRoleControllerBudget (controller geometry)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)

def scalarSum (vs : Fin 15 → ℕ) :=
  vs 0+vs 1+vs 2+vs 3+vs 4+vs 5+vs 6+vs 7+vs 8+vs 9+vs 10+vs 11+vs 12+vs 13+vs 14

theorem cleanup_cost_eq (vs : Fin 15 → ℕ) :
    CompactChildHeadersArithmetic.scheduleCost CompactNativeRoleMetadataCleanup.schedule
      (CompactNativeRoleStageCopy.metadata vs)=100*(scalarSum vs+15)+15 := by
  dsimp [CompactNativeRoleMetadataCleanup.schedule,List.map,CompactNativeRoleMetadataCleanup.cmd,
    CompactChildHeadersArithmetic.scheduleCost,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,CompactNativeRoleStageCopy.metadata,Function.update,scalarSum]
  simp only [Option.getD_some]
  ring

theorem cleanup_linear (vs : Fin 15 → ℕ) (V : ℕ) (hV : 0<V) (hv : ∀ i,vs i≤V) :
    CompactChildHeadersArithmetic.scheduleCost CompactNativeRoleMetadataCleanup.schedule
      (CompactNativeRoleStageCopy.metadata vs)≤3015*V := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  have h6 := hv 6
  have h7 := hv 7
  have h8 := hv 8
  have h9 := hv 9
  have h10 := hv 10
  have h11 := hv 11
  have h12 := hv 12
  have h13 := hv 13
  have h14 := hv 14
  rw [cleanup_cost_eq]
  unfold scalarSum
  omega

theorem stage_cleanup {s : Shape} (v : Stage s) (rows ell p : ℕ)
    (hr : 0<rows) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) (hpay : s.payload=1) :
    CompactChildHeadersArithmetic.scheduleCost CompactNativeRoleMetadataCleanup.schedule
      (CompactSpectatorLeafSetup.raw s rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val)≤
      3015*volume rows s ell p := by
  have he : CompactNativeRoleStageCopy.metadata
      (CompactNativeRoleStageCopy.values (geometry s rows ell p v.rho) (controller v))=
      CompactSpectatorLeafSetup.raw s rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val := by
    funext i
    fin_cases i <;> rfl
  rw [←he]
  exact cleanup_linear _ _ (Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p))
    (CompactNativeRoleControllerBudget.values_bounds v rows ell p hr hA hG hK hpay)

def constant (c : ℕ) := CompactNativeRoleOriginalBudget.constant c+4000

theorem merge_linear (n c : ℕ) {s : Shape} (v : Stage s) (ell p : ℕ)
    (hc : 0<c) (hn : 0<n) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) (hpay : s.payload=1) :
    CompactNativeRoleMergeCaller.cost n c s ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val≤
      constant c*volume (n*c) s ell p := by
  have h0 := CompactNativeRoleOriginalBudget.cost_linear true n c s ell p v.rho v.left v.f v.slots v.right
    v.source.val v.target.val hc hn hA hG hK
  have h1 := stage_cleanup v (n*c) ell p (Nat.mul_pos hn hc) hA hG hK hpay
  have hV : 0<volume (n*c) s ell p := Nat.mul_pos (Nat.mul_pos hn hc) (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  unfold CompactNativeRoleMergeCaller.cost constant
  simp only [Nat.add_mul] at *
  omega

end
end IntegerMultBounds.Machine.CompactNativeRoleMetadataBudget
