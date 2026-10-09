import IntegerMultBounds.Machine.ButterflyInverseAxisCorrect

/-! Physically reserve an independent two-pass guard from original D and actual
input precision q. The temporary width parameter q+2D is computed by two charged
additions and restored by charged subtraction and erasure. No prebuilt enlarged
precision header is assumed, and the mathematical precision remains q. -/
namespace IntegerMultBounds.Machine.ButterflyIndependentGuardHeaders
noncomputable section
open ActiveRepairRankHeadersCommands
open ButterflyAxisHeadersData (initial)
variable {a : ℕ}

def reservation (D q : ℕ) := q+2*D

def reserve : List Command := [.add 3 0 (by decide),.add 3 0 (by decide)]
def restore : List Command := [.difference 3 0 4 (by decide),.difference 4 0 5 (by decide),
  .erase 3,.copy 5 3 (by decide),.erase 4,.erase 5]
def reset : List Command := [.erase 1,.zero 1]

theorem reserve_eval (D t R q : ℕ) : execute reserve (initial D t R q)=initial D t R (reservation D q) := by
  funext i
  fin_cases i <;> simp [reserve,execute,eval,put,initial,reservation,Function.update]
  omega

theorem restore_eval (D t R q : ℕ) : execute restore (initial D t R (reservation D q))=initial D t R q := by
  funext i
  fin_cases i <;> simp [restore,execute,eval,put,initial,reservation,Function.update]
  omega

theorem reset_eval (D t R p : ℕ) : execute reset (initial D t R p)=initial D 0 R p := by
  funext i
  fin_cases i <;> simp [reset,execute,eval,put,initial,Function.update]

theorem reserve_valid (D t R q : ℕ) : validSchedule reserve (initial D t R q) := by
  simp [reserve,validSchedule,valid,eval,put,initial,Function.update]

theorem restore_valid (D t R q : ℕ) : validSchedule restore (initial D t R (reservation D q)) := by
  simp [restore,validSchedule,valid,eval,put,initial,reservation,Function.update]
  omega

theorem reset_valid (D t R p : ℕ) : validSchedule reset (initial D t R p) := by
  simp [reset,validSchedule,valid,eval,initial,Function.update]

theorem reserve_runs (D t R q : ℕ) :
    HoareTime (compile (a:=a) reserve).2 (fun v => v=bank (initial D t R q))
      (fun v => v=bank (initial D t R (reservation D q))) (202*(reservation D q+1)) := by
  have hh := schedule_runs (a:=a) reserve (initial D t R q) (reserve_valid D t R q)
  rw [reserve_eval] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by
    simp [reserve,scheduleCost,cost,eval,put,initial,reservation,Function.update]
    omega)

theorem restore_runs (D t R q : ℕ) :
    HoareTime (compile (a:=a) restore).2 (fun v => v=bank (initial D t R (reservation D q)))
      (fun v => v=bank (initial D t R q)) (1000*(reservation D q+1)) := by
  have hh := schedule_runs (a:=a) restore (initial D t R (reservation D q)) (restore_valid D t R q)
  rw [restore_eval] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by
    simp [restore,scheduleCost,cost,eval,put,initial,reservation,Function.update]
    omega)

theorem reset_runs (D t R p : ℕ) :
    HoareTime (compile (a:=a) reset).2 (fun v => v=bank (initial D t R p))
      (fun v => v=bank (initial D 0 R p)) (202*(t+1)) := by
  have hh := schedule_runs (a:=a) reset (initial D t R p) (reset_valid D t R p)
  rw [reset_eval] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by
    simp [reset,scheduleCost,cost,initial]
    omega)

theorem width_eq (D q : ℕ) : ButterflyGuard.width (reservation D q) D=q+4*D+4 := by
  unfold ButterflyGuard.width ButterflyGuard.halfWidth reservation
  omega

end
end IntegerMultBounds.Machine.ButterflyIndependentGuardHeaders
