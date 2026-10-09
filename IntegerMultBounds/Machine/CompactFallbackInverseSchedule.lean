import IntegerMultBounds.Machine.CompactFallbackInverseAxis

/-! A fixed original-dimension loop visits one inverse selected bit in each original
chunk, physically regenerating rho+i*K from the retained ordinal. Its count is
D, not D*K; all other chunk bits remain spectators in the same native stream. -/
namespace IntegerMultBounds.Machine.CompactFallbackInverseSchedule
noncomputable section
open CompactFallbackHeaders
open CompactFallbackAxisRun (Array Width bank word volume)
open CompactFallbackInverseAxis (applyAxis)

def step (D K rho ell q i : ℕ) (f : Array D K ell) : Array D K ell :=
  if ht : selected K rho i<bits D K then applyAxis D K rho ell q i ht f else f

def run (D K rho ell q start : ℕ) : ℕ → Array D K ell → Array D K ell
  | 0,f => f
  | n+1,f => step D K rho ell q (start+n) (run D K rho ell q start n f)

theorem width_run (D K rho ell q start n : ℕ) (f : Array D K ell) (hw : Width D K ell q f) :
    Width D K ell q (run D K rho ell q start n f) := by
  induction n with
  | zero => exact hw
  | succ n ih =>
    unfold run step
    split_ifs with ht
    · exact ButterflyInverseAxisArray.width_apply _ _ _ _ ht _ ih
    · exact ih

def endpoint (D K rho ell q start n : ℕ) (f : Array D K ell) :=
  bank (initial D K rho ell q (start+n)) (word (run D K rho ell q start n f))

theorem body_runs (D K rho ell q start i : ℕ) (hK : 0<K) (hr : rho<K) (hi : start+i<D)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime CompactFallbackInverseAxis.program
      (fun v => v=endpoint D K rho ell q start i f)
      (fun v => v=endpoint D K rho ell q start (i+1) f)
      (CompactFallbackAxisBudget.constant*volume D K ell q) := by
  have hh := CompactFallbackInverseAxis.runs_linear D K rho ell q (start+i) hK hr hi
    (run D K rho ell q start i f) (width_run D K rho ell q start i f hw)
  simpa only [endpoint,run,step,dite_eq_left (selected_lt D K rho (start+i) hK hr hi),Nat.add_assoc] using hh

def allProgram := CountedLoopHeaderClean.program CompactFallbackInverseAxis.program 0
def allBank (D K rho ell q n : ℕ) (f : Array D K ell) := CountedLoopHeaderClean.bank (endpoint D K rho ell q 0 n f)

theorem all_runs (D K rho ell q : ℕ) (hK : 0<K) (hr : rho<K)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime allProgram (fun v => v=allBank D K rho ell q 0 f)
      (fun v => v=allBank D K rho ell q D f)
      (D*(CompactFallbackAxisBudget.constant*volume D K ell q)+6*D+
        11*(RecursiveChildQuotientsConstant.bits D).length+35) := by
  have hh := CountedLoopHeaderClean.runs CompactFallbackInverseAxis.program 0
    (RecursiveChildQuotientsConstant.bits D) D (fun i => endpoint D K rho ell q 0 i f)
    (fun _ => CompactFallbackAxisBudget.constant*volume D K ell q)
    (by constructor <;> rfl) (RecursiveChildQuotientsConstant.bits_value D)
    (fun i hi => body_runs D K rho ell q 0 i hK hr (by omega) f hw)
  simpa only [allProgram,allBank,CountedLoopHeaderClean.cost,
    Finset.sum_const,Finset.card_range,smul_eq_mul] using hh

def constant := CompactFallbackAxisBudget.constant+63

theorem all_runs_linear (D K rho ell q : ℕ) (hD : 0<D) (hK : 0<K) (hr : rho<K)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime allProgram (fun v => v=allBank D K rho ell q 0 f)
      (fun v => v=allBank D K rho ell q D f) (constant*volume D K ell q*D) := by
  have hV := ButterflyAxisHeadersInstall.volume_pos (bits D K) (polynomials ell) (reservation D K q)
    (pow_pos (by decide) ell)
  have hl := ActiveRepairRankHeadersCommands.bits_length D
  have hm := Nat.mul_le_mul_left (63*D) (show 1≤volume D K ell q by exact hV)
  exact (all_runs D K rho ell q hK hr f hw).consequence (fun _ h => h) (fun _ h => h) (by
    unfold constant
    nlinarith)

end
end IntegerMultBounds.Machine.CompactFallbackInverseSchedule
