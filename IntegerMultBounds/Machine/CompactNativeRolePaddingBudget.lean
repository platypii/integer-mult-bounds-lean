import IntegerMultBounds.Machine.CompactNativeRoleScalarBudget
import IntegerMultBounds.Machine.CompactNativeRolePaddingCaller
import IntegerMultBounds.Machine.CompactNativeRoleMetadataBudget

/-! Entire paid reservation, native padding and role preparation/split budget,
with actual Stage controller fields. The reverse arbitrary-result merge includes
copied metadata reclamation and is paid from the original native volume. -/
namespace IntegerMultBounds.Machine.CompactNativeRolePaddingBudget
noncomputable section
open CompactGlobalRowPadding (initialRows)
open CompactReservationNativeRows (shape)
open CompactNativeRoleReservedBridge (precision)
open CompactNativeRoleControllerBudget (controller)
open ActivePrefixStageParameters (Stage)

theorem initial_divisible (c m d K : ℕ) (hc : 0<c) (hK : 0<K)
    (hdepth : 0<CompactGlobalRowPadding.depth m d) : c∣initialRows c m d K :=
  dvd_trans (dvd_pow_self c (by omega)) (CompactGlobalRowPadding.initial_bounds c m d K hc hK).2.2.2

theorem initial_quotient_positive (c m d K : ℕ) (hc : 0<c) (hK : 0<K)
    (hdepth : 0<CompactGlobalRowPadding.depth m d) : 0 < initialRows c m d K/c :=
  Nat.div_pos (Nat.le_of_dvd (CompactGlobalRowPadding.initial_positive c m d K hc hK)
    (initial_divisible c m d K hc hK hdepth)) hc

theorem split_linear (c m D K rho ell q d G : ℕ) (ctrl : Fin 6 → ℕ)
    (hc : 0<c) (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hdepth : 0<CompactGlobalRowPadding.depth m d) :
    CompactNativeRoleOriginal.cost false (initialRows c m d K/c) c (shape c m d D G K)
      ell (precision c m d D K q) rho (ctrl 2) (ctrl 1) (ctrl 0) (ctrl 3) (ctrl 4) (ctrl 5)≤
        (2*CompactNativeRoleOriginalBudget.constant c)*CompactFallbackAxisRun.volume D K ell q := by
  have h0 := CompactNativeRoleOriginalBudget.cost_linear false (initialRows c m d K/c) c
    (shape c m d D G K) ell (precision c m d D K q) rho (ctrl 2) (ctrl 1) (ctrl 0)
    (ctrl 3) (ctrl 4) (ctrl 5) hc (initial_quotient_positive c m d K hc hK hdepth) hd hG hK
  rw [Nat.div_mul_cancel (initial_divisible c m d K hc hK hdepth)] at h0
  have h1 := CompactNativeRoleTransferBudget.reservation_volume c m d D G K ell q hc hK hD
  have h2 := Nat.mul_le_mul_left (CompactNativeRoleOriginalBudget.constant c) h1
  nlinarith

def reservedConstant (c m : ℕ) :=
  CompactNativeRoleScalarBudget.constant c m+2*CompactNativeRoleOriginalBudget.constant c+1

theorem reserved_linear (c m D K ell q d G u : ℕ)
    (v : Stage (shape c m d D G K)) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hdepth : 0<CompactGlobalRowPadding.depth m d) :
    CompactNativeRoleReservedCaller.cost c m D K v.rho ell q d G u (controller v)≤
      reservedConstant c m*CompactFallbackAxisRun.volume D K ell q := by
  have h0 := CompactNativeRoleScalarBudget.producer_linear c m D K ell q d G (1+u) v hc hm hd hG hK hD
  have h1 := split_linear c m D K v.rho ell q d G (controller v) (by omega) hd hG hK hD hdepth
  have hV : 0<CompactFallbackAxisRun.volume D K ell q :=
    ButterflyAxisHeadersInstall.volume_pos _ _ _ (pow_pos (by decide) ell)
  unfold CompactNativeRoleReservedCaller.cost reservedConstant
  simp only [Nat.add_mul] at *
  omega

def constant (c m : ℕ) :=
  CompactReservationNativePaddingBudget.constant c m+reservedConstant c m+1

theorem cost_linear (inverse : Bool) (c m D K ell q d G : ℕ)
    (v : Stage (shape c m d D G K)) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hdepth : 0<CompactGlobalRowPadding.depth m d)
    (f : CompactFallbackAxisRun.Array D K ell) (hw : CompactFallbackAxisRun.Width D K ell q f) :
    CompactNativeRolePaddingCaller.cost inverse c m D K v.rho ell q d G f (controller v)≤
      constant c m*CompactFallbackAxisRun.volume D K ell q*CompactGlobalReservation.reservedAxes c m d G K := by
  have h0 := CompactReservationNativePaddingBudget.cost_linear inverse c m D K v.rho ell q d G hc hm hd hG hK hD f hw
  have h1 := reserved_linear c m D K ell q d G CompactNativeRolePaddingCaller.remainder v hc hm hd hG hK hD hdepth
  have hr := (CompactReservedVolumeBudget.geometry c m D K d G hd hG hK hD).1
  have hV : 0<CompactFallbackAxisRun.volume D K ell q :=
    ButterflyAxisHeadersInstall.volume_pos _ _ _ (pow_pos (by decide) ell)
  have h2 := Nat.le_mul_of_pos_right (CompactFallbackAxisRun.volume D K ell q) hr
  have h3 := Nat.mul_le_mul_left (reservedConstant c m) h2
  change CompactReservationNativePadding.cost inverse c m D K v.rho ell q d G f≤
    CompactReservationNativePaddingBudget.constant c m*CompactFallbackAxisRun.volume D K ell q*
      CompactGlobalReservation.reservedAxes c m d G K at h0
  change CompactFallbackAxisRun.volume D K ell q≤CompactFallbackAxisRun.volume D K ell q*
    CompactGlobalReservation.reservedAxes c m d G K at h2
  change reservedConstant c m*CompactFallbackAxisRun.volume D K ell q≤
    reservedConstant c m*(CompactFallbackAxisRun.volume D K ell q*CompactGlobalReservation.reservedAxes c m d G K) at h3
  unfold CompactNativeRolePaddingCaller.cost constant
  simp only [Nat.add_mul,Nat.mul_assoc] at *
  omega

theorem merge_linear (c m D K ell q d G : ℕ)
    (v : Stage (shape c m d D G K)) (hc : 0<c) (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hdepth : 0<CompactGlobalRowPadding.depth m d) :
    CompactNativeRoleMergeCaller.cost (initialRows c m d K/c) c (shape c m d D G K)
      ell (precision c m d D K q) v.rho v.left v.f v.slots v.right v.source.val v.target.val≤
        (2*CompactNativeRoleMetadataBudget.constant c)*CompactFallbackAxisRun.volume D K ell q := by
  have h0 := CompactNativeRoleMetadataBudget.merge_linear (initialRows c m d K/c) c v ell
    (precision c m d D K q) hc (initial_quotient_positive c m d K hc hK hdepth) hd hG hK rfl
  rw [Nat.div_mul_cancel (initial_divisible c m d K hc hK hdepth)] at h0
  have h1 := CompactNativeRoleTransferBudget.reservation_volume c m d D G K ell q hc hK hD
  have h2 := Nat.mul_le_mul_left (CompactNativeRoleMetadataBudget.constant c) h1
  nlinarith

end
end IntegerMultBounds.Machine.CompactNativeRolePaddingBudget
