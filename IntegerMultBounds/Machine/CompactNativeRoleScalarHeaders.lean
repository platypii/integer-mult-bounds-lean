import IntegerMultBounds.Machine.CompactNativeRolePrecisionHeaders

/-! Original reservation scalars physically generate the role shape, current
root row count and corrected precision. Recursive controller fields remain
separate retained runtime words on an explicit six-port interface. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleScalarHeaders
noncomputable section
open ActiveRepairRankHeadersCommands (State)
open CompactChildHeadersArithmetic
open CompactGadgetReservationCapacity (backChunks frontChunks)
open CompactNativeRoleReservedBridge (precision)
open CompactGlobalRowPadding (initialRows rowAxes)

abbrev cmd (op : ActiveRepairRankHeadersCommands.Command) : Op := .existing (.command op)
abbrev product (f : Fin 3 → Fin 28) (hf : Function.Injective f) : Op := .existing (.product f hf)

def schedule : List Op := [product ![6,7,20] (by decide),.constant 21 1,
  cmd (.difference 1 21 22 (by decide)),cmd (.copy 20 23 (by decide)),cmd (.add 23 22 (by decide)),
  .quotient ![23,1,24] (by decide),cmd (.copy 20 25 (by decide)),cmd (.add 25 20 (by decide)),
  cmd (.add 25 22 (by decide)),.quotient ![25,1,26] (by decide),cmd (.copy 8 27 (by decide)),
  cmd (.add 27 24 (by decide)),cmd (.add 27 26 (by decide)),cmd (.erase 20),cmd (.difference 0 27 20 (by decide))]

def prepared (c m D K rho ell q d G : ℕ) : State := fun i => match i.val with
  | 20 => some (D-CompactGlobalReservation.reservedAxes c m d G K) | 21 => some 1 | 22 => some (K-1)
  | 23 => some (d*G+(K-1)) | 24 => some (backChunks d G K) | 25 => some (d*G+d*G+(K-1))
  | 26 => some (frontChunks d G K) | 27 => some (CompactGlobalReservation.reservedAxes c m d G K)
  | _ => CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G i

def cleanup : List Op := ([20,21,22,23,24,25,26,27] : List (Fin 28)).map (fun i => cmd (.erase i))

theorem execute_eq (c m D K rho ell q d G : ℕ) (hK : 0<K) :
    execute schedule (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)=prepared c m D K rho ell q d G := by
  have hg : G*d=d*G := Nat.mul_comm G d
  have he : d*G+(K-1)=d*G+K-1 := by omega
  have hf : d*G+d*G+(K-1)=2*(d*G)+K-1 := by omega
  funext i
  fin_cases i <;> simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,prepared,CompactNativeRolePrecisionHeaders.prepared,
    CompactReservationPaddingHeaders.prepared,CompactReservedHeaders.initial,Function.update,
    CompactGlobalReservation.reservedAxes,backChunks,frontChunks,CompactGadgetReservationCapacity.chunks,
    CompactGadgetReservationCapacity.capacity,hg,he,hf]
  all_goals omega

theorem valid (c m D K rho ell q d G : ℕ) (hK : 0<K) (hd : 0<d) (hG : 0<G)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    validSchedule schedule (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G) := by
  have hp : 0<d*G := Nat.mul_pos hd hG
  have hg : G*d=d*G := Nat.mul_comm G d
  have he : d*G+(K-1)=d*G+K-1 := by omega
  have hf : d*G+d*G+(K-1)=2*(d*G)+K-1 := by omega
  simp [schedule,validSchedule,CompactChildHeadersArithmetic.valid,eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,CompactNativeRolePrecisionHeaders.prepared,
    CompactReservationPaddingHeaders.prepared,CompactReservedHeaders.initial,Function.update,hg,he,hf]
  unfold CompactGlobalReservation.reservedAxes backChunks frontChunks CompactGadgetReservationCapacity.chunks
    CompactGadgetReservationCapacity.capacity at hD
  omega

theorem runs (c m D K rho ell q d G : ℕ) (hK : 0<K) (hd : 0<d) (hG : 0<G)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    HoareTime (compile (a:=2) schedule).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared c m D K rho ell q d G))
      (scheduleCost schedule (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G)) := by
  have hh := schedule_runs (a:=2) schedule _ (valid c m D K rho ell q d G hK hd hG hD)
  rwa [execute_eq c m D K rho ell q d G hK] at hh

theorem cleanup_eval (c m D K rho ell q d G : ℕ) :
    execute cleanup (prepared c m D K rho ell q d G)=CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G := by
  funext i
  fin_cases i <;> simp [cleanup,cmd,execute,eval,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    prepared,CompactNativeRolePrecisionHeaders.prepared,ActiveRepairRankHeadersCommands.put,
    CompactReservationPaddingHeaders.prepared,CompactReservedHeaders.initial,Function.update]

theorem cleanup_runs (c m D K rho ell q d G : ℕ) :
    HoareTime (compile (a:=2) cleanup).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared c m D K rho ell q d G))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (CompactNativeRolePrecisionHeaders.prepared c m D K rho ell q d G))
      (scheduleCost cleanup (prepared c m D K rho ell q d G)) := by
  have hv : validSchedule cleanup (prepared c m D K rho ell q d G) := by
    simp [cleanup,cmd,validSchedule,CompactChildHeadersArithmetic.valid,eval,ActivePrefixStageHeadersOps.valid,
      ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
      prepared,Function.update]
  have hh := schedule_runs (a:=2) cleanup _ hv
  rwa [cleanup_eval] at hh

def values (c m D K rho ell q d G : ℕ) : Fin 9 → ℕ :=
  ![K,d,G,D-CompactGlobalReservation.reservedAxes c m d G K,initialRows c m d K,1,rho,ell,precision c m d D K q]
def sources : Fin 9 → Fin 43 := ![1,6,7,20,13,21,2,3,19]

theorem sources_ready (c m D K rho ell q d G : ℕ) : ∀ j,
    (ActiveRepairRankHeadersCommands.bank (a:=2) (prepared c m D K rho ell q d G)).head (sources j)=1 ∧
      (ActiveRepairRankHeadersCommands.bank (a:=2) (prepared c m D K rho ell q d G)).tape (sources j)=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (values c m D K rho ell q d G j)) := by
  intro j
  fin_cases j <;> constructor <;> rfl

end
end IntegerMultBounds.Machine.CompactNativeRoleScalarHeaders
