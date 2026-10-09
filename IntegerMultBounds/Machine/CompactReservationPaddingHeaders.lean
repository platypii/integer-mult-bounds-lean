import IntegerMultBounds.Machine.CompactReservedHeaders
import IntegerMultBounds.Machine.CompactGlobalReservation

/-! Paid global reservation-to-native-padding caller metadata, derived from
original D,K,rho,ell,q,d,G. Original scalars are retained and generated metadata
is erased after the one global pad; no descendant invokes this adapter. -/
namespace IntegerMultBounds.Machine.CompactReservationPaddingHeaders
noncomputable section
open CompactGlobalRowHeaderOps
open CompactReservedHeaders (initial rowState rowOps)
open CompactGlobalRowPadding
open ActiveRepairRankHeadersCommands (State put)

abbrev cmd (op : ActiveRepairRankHeadersCommands.Command) : Op := .ordinary (.command op)
abbrev product (f : Fin 3 → Fin 28) (hf : Function.Injective f) : Op := .ordinary (.product f hf)
def width (D K q : ℕ) := q+4*(D*K)+4

def rest (c m : ℕ) : List Op :=
  [.logarithm m ![6,9] (by decide),.power c ![9,10] (by decide),
    product ![8,1,11] (by decide),.power 2 ![11,12] (by decide),
    .ordinary (.round ![12,10,13] (by decide)),cmd (.difference 0 8 14 (by decide)),
    product ![1,14,15] (by decide),product ![0,1,16] (by decide),
    cmd (.copy 4 17 (by decide)),cmd (.add 17 16 (by decide)),cmd (.add 17 16 (by decide)),
    cmd (.add 17 16 (by decide)),cmd (.add 17 16 (by decide)),.constant 4 18,cmd (.add 17 18 (by decide))]
def schedule (c m : ℕ) := rowOps c m++rest c m

def prepared (c m D K rho ell q d G : ℕ) : State := fun i => match i.val with
  | 8 => some (rowAxes c m d) | 9 => some (depth m d) | 10 => some (c^depth m d)
  | 11 => some (rowAxes c m d*K) | 12 => some (originalRows c m d K)
  | 13 => some (initialRows c m d K) | 14 => some (D-rowAxes c m d)
  | 15 => some ((D-rowAxes c m d)*K) | 16 => some (D*K)
  | 17 => some (width D K q) | 18 => some 4 | _ => initial D K rho ell q d G i

theorem rest_eval (c m D K rho ell q d G : ℕ) (hc : 2≤c) : execute (rest c m) (rowState c m D K rho ell q d G)=
    prepared c m D K rho ell q d G := by
  have hround := CompactRowPaddingRound.rounded_eq (originalRows c m d K) (c^depth m d)
    (pow_pos (by decide) _) (pow_pos (by omega) _)
  simp only [originalRows,depth,Nat.mul_comm] at hround
  funext i
  fin_cases i
  all_goals simp [rest,execute,eval,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,put,
    initial,rowState,prepared,Function.update,depth,originalRows,initialRows,width]
  all_goals simp only [Nat.mul_comm]
  all_goals first | exact hround | ring

theorem execute_eq (c m D K rho ell q d G : ℕ) (hc : 2≤c) : execute (schedule c m) (initial D K rho ell q d G)=
    prepared c m D K rho ell q d G := by
  rw [schedule,execute_append,CompactReservedHeaders.row_executes,rest_eval c m D K rho ell q d G hc]

theorem rest_valid (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hD : rowAxes c m d≤D) (hDp : 0<D) :
    validSchedule (rest c m) (rowState c m D K rho ell q d G) := by
  have hlc := CompactGlobalRowHeaders.logc_positive c hc
  have hlog : 0<Nat.clog m (2*d) := by
    have hh := Nat.le_pow_clog (by omega : 1<m) (2*d)
    by_contra hz
    have he : Nat.clog m (2*d)=0 := by omega
    rw [he,pow_zero] at hh
    omega
  have hrow : 0<rowAxes c m d := Nat.mul_pos hlc hlog
  have hpow : 0<c^Nat.clog m d := pow_pos (by omega) _
  simp [rest,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,initial,rowState,
    Function.update,hc,hm,hd,hK,hrow,hD,hDp,hpow]

private theorem validSchedule_append (as bs : List Op) (st : State) :
    validSchedule (as++bs) st ↔ validSchedule as st ∧ validSchedule bs (execute as st) := by
  induction as generalizing st with
  | nil => simp [validSchedule,execute]
  | cons op as ih => simp only [List.cons_append,validSchedule,execute,ih,and_assoc]

theorem valid (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hD : rowAxes c m d≤D) (hDp : 0<D) :
    validSchedule (schedule c m) (initial D K rho ell q d G) := by
  rw [schedule,validSchedule_append,CompactReservedHeaders.row_executes]
  exact ⟨CompactReservedHeaders.row_valid c m D K rho ell q d G hc hm hd,
    rest_valid c m D K rho ell q d G hc hm hd hK hD hDp⟩

theorem runs (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hD : rowAxes c m d≤D) (hDp : 0<D) :
    HoareTime (compile (a:=2) (schedule c m)).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial D K rho ell q d G))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared c m D K rho ell q d G))
      (scheduleCost (schedule c m) (initial D K rho ell q d G)) := by
  have hh := schedule_runs (a:=2) (schedule c m) _ (valid c m D K rho ell q d G hc hm hd hK hD hDp)
  rwa [execute_eq c m D K rho ell q d G hc] at hh

def cleanup : List Op := ([8,9,10,11,12,13,14,15,16,17,18] : List (Fin 28)).map (fun i => cmd (.erase i))
theorem cleanup_eval (c m D K rho ell q d G : ℕ) : execute cleanup (prepared c m D K rho ell q d G)=
    initial D K rho ell q d G := by
  funext i
  fin_cases i
  all_goals simp [cleanup,execute,eval,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    initial,prepared,Function.update]

theorem cleanup_runs (c m D K rho ell q d G : ℕ) :
    HoareTime (compile (a:=2) cleanup).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared c m D K rho ell q d G))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial D K rho ell q d G))
      (scheduleCost cleanup (prepared c m D K rho ell q d G)) := by
  have hh := schedule_runs (a:=2) cleanup (prepared c m D K rho ell q d G) (by
    simp [cleanup,cmd,validSchedule,CompactGlobalRowHeaderOps.valid,eval,ActivePrefixStageHeadersOps.valid,
      ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,prepared])
  rwa [cleanup_eval] at hh

theorem width_eq (D K q : ℕ) : width D K q=
    ButterflyGuard.width (CompactFallbackHeaders.reservation D K q) (CompactFallbackHeaders.bits D K) := by
  unfold width ButterflyGuard.width ButterflyGuard.halfWidth CompactFallbackHeaders.reservation CompactFallbackHeaders.bits
  omega

/-- The retained original scalars derive the complete unchanged serialized
address dimension after removing only the original high row bits. -/
theorem remaining_bits (c m d D G K : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    (D-rowAxes c m d)*K=(CompactGlobalReservation.shape c m d D G K 1).bits := by
  have hh := CompactGlobalReservation.original_bits c m d D G K 1 hK hD
  have hr : rowAxes c m d≤D := by unfold CompactGlobalReservation.reservedAxes at hD; omega
  have he := congrArg (fun n => n*K) (Nat.sub_add_cancel hr)
  simp only [Nat.add_mul] at he
  omega

end
end IntegerMultBounds.Machine.CompactReservationPaddingHeaders
