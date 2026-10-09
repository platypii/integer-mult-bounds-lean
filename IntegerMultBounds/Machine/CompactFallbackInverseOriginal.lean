import IntegerMultBounds.Machine.CompactFallbackInverseSchedule
import IntegerMultBounds.Machine.CompactFallbackOriginal

/-! Sparse inverse execution reuses the same paid original ordinal lifecycle
and unchanged original chunk geometry, polynomial count and guard reservation. -/
namespace IntegerMultBounds.Machine.CompactFallbackInverseOriginal
noncomputable section
open CompactFallbackHeaders
open CompactFallbackAxisRun (Array Width word volume)
open ButterflyAxisHeadersArithmetic
open CompactFallbackOriginal (original seed finalize headerProgram bank)

def program := seq (seq (headerProgram seed) CompactFallbackInverseSchedule.allProgram) (headerProgram finalize)
abbrev constant := CompactFallbackOriginal.constant

theorem seeds (D K rho ell q : ℕ) (f : Array D K ell) :
    HoareTime (headerProgram seed) (fun v => v=bank D K rho ell q f)
      (fun v => v=CompactFallbackInverseSchedule.allBank D K rho ell q 0 f) 101 :=
  CompactFallbackOriginal.seeds D K rho ell q f

theorem finalizes (D K rho ell q : ℕ) (f : Array D K ell) :
    HoareTime (headerProgram finalize) (fun v => v=CompactFallbackInverseSchedule.allBank D K rho ell q D f)
      (fun v => v=bank D K rho ell q (CompactFallbackInverseSchedule.run D K rho ell q 0 D f)) (100*(D+1)+1) := by
  have hv : validSchedule finalize (initial D K rho ell q D) := by
    simp [finalize,validSchedule,valid,CompactChildHeadersArithmetic.valid,ActivePrefixStageHeadersOps.valid,
      ActiveRepairRankHeadersCommands.valid,initial]
  have he : execute finalize (initial D K rho ell q D)=original D K rho ell q := by
    funext i
    fin_cases i <;> simp [finalize,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,original,initial,Function.update]
  have hh := schedule_runs (a:=2) finalize (initial D K rho ell q D) hv
  rw [he] at hh
  have hc : scheduleCost finalize (initial D K rho ell q D)=100*(D+1)+1 := by rfl
  rw [hc] at hh
  have hr := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hh
    (CountedLoopReuseAlphabet.one (word (CompactFallbackInverseSchedule.run D K rho ell q 0 D f)) 0))
    (SharedBank.empty CompactFallbackAxisPorts.count 2)) (SharedBank.empty 2 2)
  simpa only [CompactFallbackInverseSchedule.allBank,CompactFallbackInverseSchedule.endpoint,Nat.zero_add,headerProgram,CompactFallbackAxisRun.headerProgram,bank,CompactFallbackAxisRun.bank,CompactFallbackAxisRun.common,CountedLoopHeaderClean.bank] using hr

theorem runs_linear (D K rho ell q : ℕ) (hD : 0<D) (hK : 0<K) (hr : rho<K)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime program (fun v => v=bank D K rho ell q f)
      (fun v => v=bank D K rho ell q (CompactFallbackInverseSchedule.run D K rho ell q 0 D f))
      (constant*volume D K ell q*D) := by
  have h0 := seeds D K rho ell q f
  have h1 := CompactFallbackInverseSchedule.all_runs_linear D K rho ell q hD hK hr f hw
  have h2 := finalizes D K rho ell q f
  have hV := ButterflyAxisHeadersInstall.volume_pos (bits D K) (polynomials ell) (reservation D K q)
    (pow_pos (by decide) ell)
  have hm : D≤volume D K ell q*D := Nat.le_mul_of_pos_left D hV
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold constant CompactFallbackOriginal.constant CompactFallbackInverseSchedule.constant CompactFallbackSchedule.constant; nlinarith)

end
end IntegerMultBounds.Machine.CompactFallbackInverseOriginal
