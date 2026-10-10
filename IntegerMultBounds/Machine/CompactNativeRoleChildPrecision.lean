import IntegerMultBounds.Machine.CompactNativeRoleChildHeadersPorts
import IntegerMultBounds.Machine.CompactSpectatorLeafGuardOriginal

/-! Guarded descendants use baseline p-2*bits, retaining the corrected original
p physically at private21. Actual reservation proves this subtraction exact;
the existing signed word is never resized or reserved a second time. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleChildPrecision
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open CompactSpectatorLeafSetup (raw)
open ActiveRepairRankHeadersCommands (State put)
open CompactNativeRoleChildHeadersPorts (placement active extra)
open CompactNativeRoleSourcePorts (external)

abbrev cmd (op : ActiveRepairRankHeadersCommands.Command) : Op := .base (.existing (.command op))
def prepare : List Op := CompactSpectatorLeafSetup.geometry++
  [cmd (.copy 16 19 (by decide)),cmd (.add 19 16 (by decide)),cmd (.copy 18 21 (by decide)),
   cmd (.difference 18 19 20 (by decide)),cmd (.erase 18),cmd (.copy 20 18 (by decide))]++
  ([13,14,15,16,19,20] : List (Fin 28)).map (fun i => cmd (.erase i))
def baseline (s : Shape) (rows ell p rho left count slots right src dst : ℕ) : State :=
  put (raw s rows ell (p-2*s.bits) rho left count slots right src dst) 21 p

theorem prepare_eval (s : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    execute prepare (raw s rows ell p rho left count slots right src dst)=
      baseline s rows ell p rho left count slots right src dst := by
  rw [prepare,CompactNativeRoleHeaders.execute_append,CompactNativeRoleHeaders.execute_append,
    CompactSpectatorLeafSetup.geometry_eval s rows ell p rho left count slots right src dst (Nat.mul_pos hA hG) hK]
  funext i
  fin_cases i <;> simp [execute,eval,cmd,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,CompactSpectatorLeafSetup.state,baseline,raw,Function.update,two_mul]

theorem prepare_valid (s : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) (hp : 2*s.bits≤p) :
    validSchedule prepare (raw s rows ell p rho left count slots right src dst) := by
  rw [prepare,CompactNativeRoleHeaders.validSchedule_append,CompactNativeRoleHeaders.validSchedule_append]
  have hg := CompactSpectatorLeafSetup.geometry_valid s rows ell p rho left count slots right src dst hG hA hK
  rw [CompactNativeRoleHeaders.execute_append,
    CompactSpectatorLeafSetup.geometry_eval s rows ell p rho left count slots right src dst (Nat.mul_pos hA hG) hK]
  constructor
  · exact ⟨hg,by
      simp [validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
        ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
        ActiveRepairRankHeadersCommands.eval,put,CompactSpectatorLeafSetup.state,Function.update]
      omega⟩
  · simp [validSchedule,valid,execute,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
      ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
      ActiveRepairRankHeadersCommands.eval,put,CompactSpectatorLeafSetup.state,Function.update]

theorem prepare_runs (s : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) (hp : 2*s.bits≤p) :
    HoareTime (compile (a:=2) prepare).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw s rows ell p rho left count slots right src dst))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (baseline s rows ell p rho left count slots right src dst))
      (scheduleCost prepare (raw s rows ell p rho left count slots right src dst)) := by
  have h := schedule_runs (a:=2) prepare _ (prepare_valid s rows ell p rho left count slots right src dst hG hA hK hp)
  rwa [prepare_eval s rows ell p rho left count slots right src dst hG hA hK] at h

def restore : List Op := [cmd (.erase 18),cmd (.copy 21 18 (by decide)),cmd (.erase 21)]

theorem restore_runs (s : Shape) (rows ell p rho left count slots right src dst : ℕ) :
    HoareTime (compile (a:=2) restore).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (baseline s rows ell p rho left count slots right src dst))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw s rows ell p rho left count slots right src dst))
      (scheduleCost restore (baseline s rows ell p rho left count slots right src dst)) := by
  have hv : validSchedule restore (baseline s rows ell p rho left count slots right src dst) := by
    simp [restore,baseline,raw,cmd,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,
      CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,Function.update]
  have he : execute restore (baseline s rows ell p rho left count slots right src dst)=
      raw s rows ell p rho left count slots right src dst := by
    funext i
    fin_cases i <;> simp [restore,baseline,raw,cmd,execute,eval,CompactChildHeadersArithmetic.eval,
      ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,put,Function.update]
  have h := schedule_runs (a:=2) restore _ hv
  rwa [he] at h

/-- Corrected original precision already pays two guards for the retained bits. -/
theorem actual_precision (c m d D G K q : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    2*(CompactReservationNativeRows.shape c m d D G K).bits≤
      CompactNativeRoleReservedBridge.precision c m d D K q ∧
    CompactNativeRoleReservedBridge.precision c m d D K q-
      2*(CompactReservationNativeRows.shape c m d D G K).bits=q+4*(CompactGlobalRowPadding.rowAxes c m d*K) := by
  have hb := CompactGlobalReservation.original_bits c m d D G K 1 hK hD
  have hrow : CompactGlobalRowPadding.rowAxes c m d≤D := by
    unfold CompactGlobalReservation.reservedAxes at hD
    omega
  have hmul := Nat.mul_le_mul_right K hrow
  have he := congrArg (fun x => x*K) (Nat.add_sub_of_le hrow)
  simp only [Nat.add_mul] at he
  change CompactGlobalRowPadding.rowAxes c m d*K+(CompactReservationNativeRows.shape c m d D G K).bits=D*K at hb
  unfold CompactNativeRoleReservedBridge.precision
  omega

theorem stored_width (s : Shape) (p : ℕ) (hp : 2*s.bits≤p) :
    CompactNativeRoleHeaders.recordWidth s p=
      ButterflyAxisHeadersData.width s.bits (ButterflyIndependentGuardHeaders.reservation s.bits (p-2*s.bits)) := by
  unfold CompactNativeRoleHeaders.recordWidth ButterflyAxisHeadersData.width ButterflyGuard.width
    ButterflyGuard.halfWidth ButterflyIndependentGuardHeaders.reservation
  omega

def program (ops : List Op) (t c : ℕ) := Placement.placed (compile (a:=2) ops).2 (placement t c)

private theorem framed {t c : ℕ} (ops : List Op) (old : Tapes t 2) (ht : 43<t)
    (st su : State) (payload : Tapes (1+c) 2) (cost : ℕ)
    (h : HoareTime (compile (a:=2) ops).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank st)
      (fun v => v=ActiveRepairRankHeadersCommands.bank su) cost) :
    HoareTime (program ops t c) (fun v => v=external old ht st payload)
      (fun v => v=external old ht su payload) cost := by
  have hh := Placement.hoare_at h (placement t c) (external old ht st payload) (active old ht st payload)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,extra old ht st su payload,←active old ht su payload,Placement.view]

theorem actual_prepare {t c : ℕ} (old : Tapes t 2) (ht : 43<t)
    (m d D G K q rows ell rho left count slots right src dst : ℕ)
    (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (payload : Tapes (1+c) 2) :
    let s := CompactReservationNativeRows.shape c m d D G K
    let p := CompactNativeRoleReservedBridge.precision c m d D K q
    HoareTime (program prepare t c)
      (fun v => v=external old ht (raw s rows ell p rho left count slots right src dst) payload)
      (fun v => v=external old ht (baseline s rows ell p rho left count slots right src dst) payload)
      (scheduleCost prepare (raw s rows ell p rho left count slots right src dst)) :=
  framed _ old ht _ _ payload _ (prepare_runs _ _ _ _ _ _ _ _ _ _ _ hG hd hK (actual_precision c m d D G K q hK hD).1)

theorem actual_restore {t c : ℕ} (old : Tapes t 2) (ht : 43<t) (s : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (payload : Tapes (1+c) 2) :
    HoareTime (program restore t c)
      (fun v => v=external old ht (baseline s rows ell p rho left count slots right src dst) payload)
      (fun v => v=external old ht (raw s rows ell p rho left count slots right src dst) payload)
      (scheduleCost restore (baseline s rows ell p rho left count slots right src dst)) :=
  framed _ old ht _ _ payload _ (restore_runs s rows ell p rho left count slots right src dst)

end
end IntegerMultBounds.Machine.CompactNativeRoleChildPrecision
