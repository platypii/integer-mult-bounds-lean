import IntegerMultBounds.Machine.CompactFallbackAxisPorts

/-! A sparse individual-axis call starts from original chunk count, chunk
width, selected bit, polynomial exponent, actual precision and chunk ordinal.
Its binary dimension, selected coordinate, polynomial count and independent
signed-width reservation are all computed by an actual header schedule. -/
namespace IntegerMultBounds.Machine.CompactFallbackHeaders
noncomputable section
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd product)
open ActiveRepairRankHeadersCommands (State put)

def bits (D K : ℕ) := D*K
def selected (K rho i : ℕ) := rho+i*K
def polynomials (ell : ℕ) := 2^ell
def reservation (D K q : ℕ) := q+2*bits D K

def initial (D K rho ell q i : ℕ) (s : Fin 28) : Option ℕ :=
  match s.val with
  | 0 => some D | 1 => some K | 2 => some rho | 3 => some ell | 4 => some q | 5 => some i | _ => none

def prepared (D K rho ell q i shift : ℕ) (s : Fin 28) : Option ℕ :=
  match s.val with
  | 0 => some D | 1 => some K | 2 => some rho | 3 => some ell | 4 => some q | 5 => some i
  | 6 => some (bits D K) | 7 => some (selected K rho i+shift)
  | 8 => some (polynomials ell) | 9 => some (reservation D K q) | 10 => some 1 | _ => none

def setup : List Op := [product ![0,1,6] (by decide),product ![1,5,7] (by decide),
  cmd (.add 7 2 (by decide)),.power ![3,8] (by decide),cmd (.copy 4 9 (by decide)),
  cmd (.add 9 6 (by decide)),cmd (.add 9 6 (by decide)),.base (.constant 10 1)]
def cleanup : List Op := [cmd (.add 5 10 (by decide)),cmd (.erase 6),cmd (.erase 7),
  cmd (.erase 8),cmd (.erase 9),cmd (.erase 10)]

theorem setup_eval (D K rho ell q i : ℕ) : execute setup (initial D K rho ell q i)=prepared D K rho ell q i 0 := by
  funext s
  fin_cases s <;> simp [setup,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,prepared,bits,selected,polynomials,reservation,Function.update]
  all_goals ring

theorem cleanup_eval (D K rho ell q i : ℕ) : execute cleanup (prepared D K rho ell q i 1)=initial D K rho ell q (i+1) := by
  funext s
  fin_cases s <;> simp [cleanup,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,initial,prepared,Function.update]

theorem setup_valid (D K rho ell q i : ℕ) (hD : 0<D) (hK : 0<K) : validSchedule setup (initial D K rho ell q i) := by
  simp [setup,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,initial,Function.update,hD,hK]

theorem cleanup_valid (D K rho ell q i : ℕ) : validSchedule cleanup (prepared D K rho ell q i 1) := by
  simp [cleanup,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,put,prepared,Function.update]

theorem setup_runs (D K rho ell q i : ℕ) (hD : 0<D) (hK : 0<K) :
    HoareTime (compile (a:=2) setup).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial D K rho ell q i))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared D K rho ell q i 0))
      (scheduleCost setup (initial D K rho ell q i)) := by
  have hh := schedule_runs (a:=2) setup _ (setup_valid D K rho ell q i hD hK)
  rwa [setup_eval] at hh

theorem cleanup_runs (D K rho ell q i : ℕ) :
    HoareTime (compile (a:=2) cleanup).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared D K rho ell q i 1))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial D K rho ell q (i+1)))
      (scheduleCost cleanup (prepared D K rho ell q i 1)) := by
  have hh := schedule_runs (a:=2) cleanup _ (cleanup_valid D K rho ell q i)
  rwa [cleanup_eval] at hh

theorem selected_lt (D K rho i : ℕ) (_hK : 0<K) (hr : rho<K) (hi : i<D) : selected K rho i<bits D K := by
  have hh := Nat.mul_le_mul_right K (show i+1≤D by omega)
  unfold selected bits
  nlinarith

end
end IntegerMultBounds.Machine.CompactFallbackHeaders
