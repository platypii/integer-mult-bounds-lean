import IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersAtomic

/-! Complete physical highest-pair header synthesis and cleanup. All five
original words survive, and every temporary power/product word is erased. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersRun
noncomputable section
open ActiveTargetHighestPairData ActiveTargetHighestPairHeadersData
open ActiveTargetHighestPairHeadersAtomic ActiveRepairRankHeadersCommands
variable {a : ℕ}

def arithmeticProgram := (compile (a := a) arithmeticSchedule).2
def scratchProgram := (compile (a := a) scratchCleanup).2
def cleanupProgram := (compile (a := a) outputCleanup).2

def program := seq (seq (seq (seq (seq (seq (seq (seedProgram (a := a) 9) arithmeticProgram)
  (powerProgram 1 14 (by decide))) (powerProgram 0 16 (by decide)))
  (productProgram 16 3 13 (by decide))) (powerProgram 2 15 (by decide)))
  (productProgram 15 4 12 (by decide))) scratchProgram

def cost (g : Geometry) := 9+scheduleCost arithmeticSchedule (seeded g)+
  FixedBasePowerDescriptor.constant 2*gap g+FixedBasePowerDescriptor.constant 2*2^g.L+
  (53*P g+28)+FixedBasePowerDescriptor.constant 2*2^g.K+(53*suffix g+28)+
  scheduleCost scratchCleanup (multipliedB g)+7
def cleanupCost (g : Geometry) := scheduleCost outputCleanup (finished g)

theorem arithmetic_runs (g : Geometry) :
    HoareTime (arithmeticProgram (a := a)) (fun v => v=bank (seeded g))
      (fun v => v=bank (arithmetic g)) (scheduleCost arithmeticSchedule (seeded g)) := by
  have h := schedule_runs (a := a) arithmeticSchedule (seeded g) (arithmetic_valid g)
  rwa [arithmetic_eq] at h

theorem powerG_runs (g : Geometry) :
    HoareTime (powerProgram (a := a) 1 14 (by decide)) (fun v => v=bank (arithmetic g))
      (fun v => v=bank (poweredG g)) (FixedBasePowerDescriptor.constant 2*gap g) :=
  power (arithmetic g) 1 14 (by decide) g.G (by simp [arithmetic,originalValues]) (by simp [arithmetic])

theorem powerL_runs (g : Geometry) :
    HoareTime (powerProgram (a := a) 0 16 (by decide)) (fun v => v=bank (poweredG g))
      (fun v => v=bank (poweredL g)) (FixedBasePowerDescriptor.constant 2*2^g.L) :=
  power (poweredG g) 0 16 (by decide) g.L (by simp [poweredG,put,arithmetic,originalValues,Function.update])
    (by simp [poweredG,put,arithmetic,Function.update])

theorem productP_runs (g : Geometry) :
    HoareTime (productProgram (a := a) 16 3 13 (by decide)) (fun v => v=bank (poweredL g))
      (fun v => v=bank (multipliedP g)) (53*P g+28) := by
  have h := product (a := a) (poweredL g) 16 3 13 (by decide) (2^g.L) g.rows (by positivity)
    (by simp [poweredL,put])
    (by simp [poweredL,poweredG,put,arithmetic,originalValues,Function.update])
    (by simp [poweredL,poweredG,put,arithmetic,Function.update])
  simpa only [Nat.mul_comm g.rows,P,multipliedP] using h

theorem powerK_runs (g : Geometry) :
    HoareTime (powerProgram (a := a) 2 15 (by decide)) (fun v => v=bank (multipliedP g))
      (fun v => v=bank (poweredK g)) (FixedBasePowerDescriptor.constant 2*2^g.K) :=
  power (multipliedP g) 2 15 (by decide) g.K
    (by simp [multipliedP,poweredL,poweredG,put,arithmetic,originalValues,Function.update])
    (by simp [multipliedP,poweredL,poweredG,put,arithmetic,Function.update])

theorem productB_runs (g : Geometry) :
    HoareTime (productProgram (a := a) 15 4 12 (by decide)) (fun v => v=bank (poweredK g))
      (fun v => v=bank (multipliedB g)) (53*suffix g+28) :=
  product (poweredK g) 15 4 12 (by decide) (2^g.K) g.payload (by positivity)
    (by simp [poweredK,put])
    (by simp [poweredK,multipliedP,poweredL,poweredG,put,arithmetic,originalValues,Function.update])
    (by simp [poweredK,multipliedP,poweredL,poweredG,put,arithmetic,Function.update])

theorem runs (g : Geometry) :
    HoareTime (program (a := a)) (fun v => v=bank (initial g))
      (fun v => v=bank (finished g)) (cost g) := by
  have h₀ := seed (a := a) (initial g) 9 (by simp [initial])
  have h₇ := schedule_runs (a := a) scratchCleanup (multipliedB g) (scratch_valid g)
  rw [scratch_eq] at h₇
  exact (((((((h₀.seq (arithmetic_runs g)).seq (powerG_runs g)).seq (powerL_runs g)).seq
    (productP_runs g)).seq (powerK_runs g)).seq (productB_runs g)).seq h₇).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem cleans (g : Geometry) :
    HoareTime (cleanupProgram (a := a)) (fun v => v=bank (finished g))
      (fun v => v=bank (initial g)) (cleanupCost g) := by
  have h := schedule_runs (a := a) outputCleanup (finished g) (cleanup_valid g)
  rwa [cleanup_eq] at h

end
end IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersRun
