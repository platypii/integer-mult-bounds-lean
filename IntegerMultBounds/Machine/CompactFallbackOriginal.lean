import IntegerMultBounds.Machine.CompactFallbackSchedule

/-! The full small-dimension fallback starts with only five original numeric
headers and its native stream. It physically seeds the chunk ordinal,
counts the original dimension D, visits exactly rho+i*K once per chunk and
erases the ordinal. All derived descriptors and private storage return blank. -/
namespace IntegerMultBounds.Machine.CompactFallbackOriginal
noncomputable section
open CompactFallbackHeaders CompactFallbackAxisRun
open ButterflyAxisHeadersArithmetic
open ActiveRepairRankHeadersCommands (State)

def original (D K rho ell q : ℕ) : State := Function.update (initial D K rho ell q 0) 5 none

def seed : List Op := [ButterflyAxisHeadersData.cmd (.zero 5)]
def finalize : List Op := [ButterflyAxisHeadersData.cmd (.erase 5)]
def headerProgram (ops : List Op) := extend (CompactFallbackAxisRun.headerProgram ops) 2

def bank (D K rho ell q : ℕ) (f : Array D K ell) :=
  CountedLoopHeaderClean.bank (CompactFallbackAxisRun.bank (original D K rho ell q) (word f))

def program := seq (seq (headerProgram seed) CompactFallbackSchedule.allProgram) (headerProgram finalize)

theorem seeds (D K rho ell q : ℕ) (f : Array D K ell) :
    HoareTime (headerProgram seed) (fun v => v=bank D K rho ell q f)
      (fun v => v=CompactFallbackSchedule.allBank D K rho ell q 0 f) 101 := by
  have hv : validSchedule seed (original D K rho ell q) := by
    simp [seed,validSchedule,valid,CompactChildHeadersArithmetic.valid,ActivePrefixStageHeadersOps.valid,
      ActiveRepairRankHeadersCommands.valid,original]
  have he : execute seed (original D K rho ell q)=initial D K rho ell q 0 := by
    funext i
    fin_cases i <;> simp [seed,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,original,initial,Function.update]
  have hh := schedule_runs (a:=2) seed (original D K rho ell q) hv
  rw [he] at hh
  exact hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hh (CountedLoopReuseAlphabet.one (word f) 0))
    (SharedBank.empty CompactFallbackAxisPorts.count 2)) (SharedBank.empty 2 2)

theorem finalizes (D K rho ell q : ℕ) (f : Array D K ell) :
    HoareTime (headerProgram finalize) (fun v => v=CompactFallbackSchedule.allBank D K rho ell q D f)
      (fun v => v=bank D K rho ell q (CompactFallbackSchedule.run D K rho ell q 0 D f)) (100*(D+1)+1) := by
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
    (CountedLoopReuseAlphabet.one (word (CompactFallbackSchedule.run D K rho ell q 0 D f)) 0))
    (SharedBank.empty CompactFallbackAxisPorts.count 2)) (SharedBank.empty 2 2)
  simpa only [CompactFallbackSchedule.allBank,CompactFallbackSchedule.endpoint,Nat.zero_add,headerProgram,CompactFallbackAxisRun.headerProgram,bank,CompactFallbackAxisRun.bank,CompactFallbackAxisRun.common,CountedLoopHeaderClean.bank] using hr

def constant := CompactFallbackSchedule.constant+305

theorem runs_linear (D K rho ell q : ℕ) (hD : 0<D) (hK : 0<K) (hr : rho<K)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime program (fun v => v=bank D K rho ell q f)
      (fun v => v=bank D K rho ell q (CompactFallbackSchedule.run D K rho ell q 0 D f))
      (constant*volume D K ell q*D) := by
  have h0 := seeds D K rho ell q f
  have h1 := CompactFallbackSchedule.all_runs_linear D K rho ell q hD hK hr f hw
  have h2 := finalizes D K rho ell q f
  have hV := ButterflyAxisHeadersInstall.volume_pos (bits D K) (polynomials ell) (reservation D K q)
    (pow_pos (by decide) ell)
  have hm : D≤volume D K ell q*D := Nat.le_mul_of_pos_left D hV
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold constant; nlinarith)

end
end IntegerMultBounds.Machine.CompactFallbackOriginal
