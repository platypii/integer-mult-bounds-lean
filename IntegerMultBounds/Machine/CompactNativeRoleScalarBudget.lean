import IntegerMultBounds.Machine.CompactNativeRoleControllerBudget
import IntegerMultBounds.Machine.CompactReservationPaddingHeaderBudget

/-! Physical corrected-precision and reservation-shape scalar synthesis have a
uniform original native-volume budget. The two genuine binary divisions are
absorbed through the existing original dimension-square volume inequality. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleScalarBudget
noncomputable section
open RecursiveChildQuotientsConstant (bits)
open CompactReservedHeaderBudget (scalar)
open CompactGlobalRowPadding (rowAxes)
open CompactChildHeadersArithmetic

theorem shape_cost (c m D K rho ell q d G : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    scheduleCost CompactNativeRoleScalarHeaders.schedule (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)≤
      300000*(scalar c m D K d G)^2 := by
  let S := scalar c m D K d G
  have hS : 0<S := by dsimp [S,scalar]; omega
  have hH : d*G≤S := by dsimp [S,scalar]; omega
  have hKS : K≤S := by dsimp [S,scalar]; omega
  have hDS : D≤S := by dsimp [S,scalar]; omega
  have hrow : rowAxes c m d≤S := by dsimp [S,scalar]; omega
  have hq0 := CompactReservedHeaderBudget.division_cost (d*G+(K-1)) K S hS (by omega) (by omega)
  have hq1 := CompactReservedHeaderBudget.division_cost (d*G+d*G+(K-1)) K S hS (by omega) (by omega)
  have hg : G*d=d*G := Nat.mul_comm G d
  have he : d*G+(K-1)=d*G+K-1 := by omega
  have hf : d*G+d*G+(K-1)=2*(d*G)+K-1 := by omega
  have hback : (d*G+(K-1))/K≤D := by
    rw [he]
    change CompactGadgetReservationCapacity.backChunks d G K≤D
    have h := hD
    unfold CompactGlobalReservation.reservedAxes at h
    omega
  have hfront : (d*G+d*G+(K-1))/K≤D := by
    rw [hf]
    change CompactGadgetReservationCapacity.frontChunks d G K≤D
    have h := hD
    unfold CompactGlobalReservation.reservedAxes at h
    omega
  have hsquare : S≤S^2 := by nlinarith
  have hKm := Nat.sub_le K 1
  dsimp [CompactNativeRoleScalarHeaders.schedule,CompactNativeRoleScalarHeaders.cmd,CompactNativeRoleScalarHeaders.product,
    scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    CompactNativeRolePrecisionHeaders.prepared,CompactReservationPaddingHeaders.prepared,CompactReservedHeaders.initial,
    RecursiveChildQuotientsConstant.cost,Function.update]
  have hone : (bits 1).length=1 := rfl
  simp only [Option.getD_some,hg,hone]
  change _≤300000*S^2
  nlinarith only [hq0,hq1,hS,hH,hKS,hDS,hrow,hback,hfront,hsquare,hKm]

theorem shape_cleanup_cost (c m D K rho ell q d G : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    scheduleCost CompactNativeRoleScalarHeaders.cleanup (CompactNativeRoleScalarHeaders.prepared c m D K rho ell q d G)≤
      10000*(scalar c m D K d G)^2 := by
  let S := scalar c m D K d G
  have hS : 0<S := by dsimp [S,scalar]; omega
  have hH : d*G≤S := by dsimp [S,scalar]; omega
  have hKS : K≤S := by dsimp [S,scalar]; omega
  have hDS : D≤S := by dsimp [S,scalar]; omega
  have hback : CompactGadgetReservationCapacity.backChunks d G K≤D := by
    unfold CompactGlobalReservation.reservedAxes at hD
    omega
  have hfront : CompactGadgetReservationCapacity.frontChunks d G K≤D := by
    unfold CompactGlobalReservation.reservedAxes at hD
    omega
  have hsquare : S≤S^2 := by nlinarith
  have hKm := Nat.sub_le K 1
  have hdiff := Nat.sub_le D (CompactGlobalReservation.reservedAxes c m d G K)
  simp [CompactNativeRoleScalarHeaders.cleanup,CompactNativeRoleScalarHeaders.cmd,scheduleCost,cost,eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,CompactNativeRoleScalarHeaders.prepared,Function.update]
  change _≤10000*S^2
  nlinarith only [hS,hH,hKS,hDS,hback,hfront,hsquare,hKm,hdiff,hD]

theorem shape_linear (c m D K rho ell q d G : ℕ) (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    scheduleCost CompactNativeRoleScalarHeaders.schedule (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)+
      scheduleCost CompactNativeRoleScalarHeaders.cleanup (CompactNativeRoleScalarHeaders.prepared c m D K rho ell q d G)≤
        7750000*CompactFallbackAxisRun.volume D K ell q := by
  have h0 := shape_cost c m D K rho ell q d G hK hD
  have h1 := shape_cleanup_cost c m D K rho ell q d G hK hD
  have h2 := CompactReservedVolumeBudget.scalar_square_le c m D K ell q d G hd hG hK hD
  omega


theorem precision_extra_cost (c m D K rho ell q d G : ℕ) :
    CompactGlobalRowHeaderOps.scheduleCost CompactNativeRolePrecisionHeaders.extra
      (CompactReservationPaddingHeaders.prepared c m D K rho ell q d G)=
        100*(5*q+7*(D*K)+3*(rowAxes c m d*K)+5)+5 := by
  dsimp [CompactNativeRolePrecisionHeaders.extra,CompactReservationPaddingHeaders.cmd,
    CompactGlobalRowHeaderOps.scheduleCost,CompactGlobalRowHeaderOps.cost,CompactGlobalRowHeaderOps.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,CompactReservationPaddingHeaders.prepared,
    CompactReservedHeaders.initial,Function.update]
  simp only [Option.getD_some]
  ring

theorem precision_cleanup_cost (c m D K rho ell q d G : ℕ) :
    CompactGlobalRowHeaderOps.scheduleCost CompactNativeRolePrecisionHeaders.cleanup
      (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)=
    CompactGlobalRowHeaderOps.scheduleCost CompactReservationPaddingHeaders.cleanup
      (CompactReservationPaddingHeaders.prepared c m D K rho ell q d G)+
        100*CompactNativeRoleReservedBridge.precision c m d D K q+101 := by
  dsimp [CompactNativeRolePrecisionHeaders.cleanup,CompactReservationPaddingHeaders.cleanup,List.append,List.map,
    CompactReservationPaddingHeaders.cmd,CompactGlobalRowHeaderOps.scheduleCost,CompactGlobalRowHeaderOps.cost,
    CompactGlobalRowHeaderOps.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    CompactNativeRolePrecisionHeaders.prepared,CompactReservationPaddingHeaders.prepared,CompactReservedHeaders.initial,Function.update]
  simp only [Option.getD_some]
  ring

theorem q_le_volume (D K ell q : ℕ) : q≤CompactFallbackAxisRun.volume D K ell q := by
  have hp : 0<2^(D*K) := pow_pos (by decide) _
  have hR : 0<2^ell := pow_pos (by decide) _
  have h0 := Nat.le_mul_of_pos_left (ButterflyAxisHeadersData.recordLength (D*K) (q+2*(D*K))) (Nat.mul_pos hp hR)
  have h1 : q≤ButterflyAxisHeadersData.recordLength (D*K) (q+2*(D*K)) := by
    unfold ButterflyAxisHeadersData.recordLength ButterflyAxisHeadersData.width
    omega
  exact h1.trans h0

theorem precision_linear (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    CompactGlobalRowHeaderOps.scheduleCost (CompactNativeRolePrecisionHeaders.schedule c m)
      (CompactReservedHeaders.initial D K rho ell q d G)+
    CompactGlobalRowHeaderOps.scheduleCost CompactNativeRolePrecisionHeaders.cleanup
      (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)≤
        (CompactReservationPaddingHeaderBudget.constant c m+3000)*CompactFallbackAxisRun.volume D K ell q := by
  have h0 := CompactReservationPaddingHeaderBudget.cost_linear c m D K rho ell q d G hc hm hd hG hK hD
  have hq := q_le_volume D K ell q
  have hsq := CompactReservedVolumeBudget.dimension_square_le D K ell q
  have hB : D*K≤CompactFallbackAxisRun.volume D K ell q := by
    change (D*K+1)^2≤_ at hsq
    nlinarith
  have hrow : rowAxes c m d≤D := by unfold CompactGlobalReservation.reservedAxes at hD; omega
  have hrowB := Nat.mul_le_mul_right K hrow
  have hV : 0<CompactFallbackAxisRun.volume D K ell q :=
    ButterflyAxisHeadersInstall.volume_pos _ _ _ (pow_pos (by decide) ell)
  rw [CompactNativeRolePrecisionHeaders.schedule,CompactGlobalRowHeaderOps.scheduleCost_append,
    CompactReservationPaddingHeaders.execute_eq c m D K rho ell q d G (by omega),precision_extra_cost,precision_cleanup_cost]
  unfold CompactNativeRoleReservedBridge.precision
  simp only [Nat.add_mul]
  omega

def constant (c m : ℕ) := CompactReservationPaddingHeaderBudget.constant c m+7753304

theorem producer_linear (c m D K ell q d G u : ℕ)
    (v : ActivePrefixStageParameters.Stage (CompactReservationNativeRows.shape c m d D G K))
    (hc : 2≤c) (hm : 2≤m) (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    CompactNativeRoleScalarProducer.cost c m D K v.rho ell q d G u
      (CompactNativeRoleControllerBudget.controller v)≤
        constant c m*CompactFallbackAxisRun.volume D K ell q := by
  have h0 := shape_linear c m D K v.rho ell q d G hd hG hK hD
  have h1 := precision_linear c m D K v.rho ell q d G hc hm hd hG hK hD
  have h2 := CompactNativeRoleControllerBudget.actual_copy_linear c m D K ell q d G u v
    (by omega) hd hG hK hD
  have hV : 0<CompactFallbackAxisRun.volume D K ell q :=
    ButterflyAxisHeadersInstall.volume_pos _ _ _ (pow_pos (by decide) ell)
  unfold CompactNativeRoleScalarProducer.cost constant
  simp only [Nat.add_mul] at *
  omega

end
end IntegerMultBounds.Machine.CompactNativeRoleScalarBudget

