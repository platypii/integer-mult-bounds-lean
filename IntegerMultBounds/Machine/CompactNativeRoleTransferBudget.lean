import IntegerMultBounds.Machine.CompactNativeRolePaddingCaller

/-! Uniform genuine-symbol budget for physical normalized role transfer and
all destructive source resets. Header synthesis/copying is accounted separately. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleTransferBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactNativeRoleOriginal (symbols erased transferCost)
open RecursiveChildQuotientsConstant (bits)

def volume (rows : ℕ) (s : Shape) (ell p : ℕ) := rows*symbols s ell p

theorem symbols_pos (s : Shape) (ell p : ℕ) : 0<symbols s ell p := by
  unfold symbols CompactNativeRoleOriginal.inner
  positivity

theorem erased_le (merge : Bool) (n c : ℕ) (s : Shape) (ell p : ℕ) (hc : 0<c) :
    erased merge n c s ell p≤volume (n*c) s ell p := by
  cases merge
  · rfl
  · simp only [erased,ite_true,volume]
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right n hc)

theorem transfer_linear (merge : Bool) (n c : ℕ) (s : Shape) (ell p : ℕ) (hc : 0<c) (hn : 0<n) :
    transferCost merge n c s ell p≤252*volume (n*c) s ell p := by
  have hB := symbols_pos s ell p
  have hV : 0<volume (n*c) s ell p := Nat.mul_pos (Nat.mul_pos hn hc) hB
  have ht := CyclicRowNormalized.cost_linear (symbols s ell p) (bits (symbols s ell p)) (bits n)
    hc hn hB (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
  have he := erased_le merge n c s ell p hc
  have hl := ActiveRepairRankHeadersCommands.bits_length (erased merge n c s ell p)
  have hv : n*(c*symbols s ell p)=volume (n*c) s ell p := by unfold volume; ring
  rw [hv] at ht
  unfold transferCost
  omega

theorem reservation_volume (c m d D G K ell q : ℕ) (hc : 0<c) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    volume (CompactGlobalRowPadding.initialRows c m d K) (CompactReservationNativeRows.shape c m d D G K)
      ell (CompactNativeRoleReservedBridge.precision c m d D K q)≤2*CompactFallbackAxisRun.volume D K ell q := by
  have hr := (CompactGlobalRowPadding.initial_bounds c m d K hc hK).2.2.1
  have hg := CompactReservationNativeRows.cardinality c m d D G K ell hK hD
  have hw := CompactNativeRoleReservedBridge.precision_width c m d D G K q hK hD
  have hs : symbols (CompactReservationNativeRows.shape c m d D G K) ell
      (CompactNativeRoleReservedBridge.precision c m d D K q)=
    2^(CompactReservationNativeRows.shape c m d D G K).bits*2^ell*
      (2*(CompactReservationNativeRows.width D K q+1)) := by
    unfold symbols CompactNativeRoleOriginal.inner
    rw [hw]
  have hh := Nat.mul_le_mul_right (symbols (CompactReservationNativeRows.shape c m d D G K) ell
    (CompactNativeRoleReservedBridge.precision c m d D K q)) hr
  have he : CompactGlobalRowPadding.originalRows c m d K*
      symbols (CompactReservationNativeRows.shape c m d D G K) ell
        (CompactNativeRoleReservedBridge.precision c m d D K q)=CompactFallbackAxisRun.volume D K ell q := by
    rw [hs]
    calc
      _ = (CompactGlobalRowPadding.originalRows c m d K*
        2^(CompactReservationNativeRows.shape c m d D G K).bits*2^ell)*
          (2*(CompactReservationNativeRows.width D K q+1)) := by ring
      _ = 2^(D*K)*2^ell*(2*(CompactReservationNativeRows.width D K q+1)) := by rw [hg]
      _ = _ := by
        unfold CompactFallbackAxisRun.volume ButterflyAxisHeadersBudget.logicalVolume ButterflyAxisHeadersData.recordLength
          ButterflyAxisHeadersData.width CompactFallbackHeaders.reservation CompactFallbackHeaders.polynomials
          CompactFallbackHeaders.bits CompactReservationNativeRows.width
        simp only [ButterflyGuard.width,ButterflyGuard.halfWidth,CompactFallbackHeaders.reservation,CompactFallbackHeaders.bits]
        ring
  simpa only [volume,Nat.mul_assoc,he] using hh

theorem reservation_transfer (merge : Bool) (c m d D G K ell q : ℕ) (hc : 0<c) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hd : c ∣ CompactGlobalRowPadding.initialRows c m d K) :
    transferCost merge (CompactGlobalRowPadding.initialRows c m d K/c) c
      (CompactReservationNativeRows.shape c m d D G K) ell
      (CompactNativeRoleReservedBridge.precision c m d D K q)≤504*CompactFallbackAxisRun.volume D K ell q := by
  have hr := CompactGlobalRowPadding.initial_positive c m d K hc hK
  have hn := Nat.div_pos (Nat.le_of_dvd hr hd) hc
  have hh := transfer_linear merge (CompactGlobalRowPadding.initialRows c m d K/c) c
    (CompactReservationNativeRows.shape c m d D G K) ell
    (CompactNativeRoleReservedBridge.precision c m d D K q) hc hn
  rw [Nat.div_mul_cancel hd] at hh
  have hv := reservation_volume c m d D G K ell q hc hK hD
  omega

end
end IntegerMultBounds.Machine.CompactNativeRoleTransferBudget
