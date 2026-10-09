import IntegerMultBounds.Machine.CompactReservedSchedule

/-! Every interval boundary is paid: preparation computes the counts, switching
loads the derived high start, and finalization erases all generated controls. -/
namespace IntegerMultBounds.Machine.CompactReservedLifecycle
noncomputable section
open CompactReservedHeaders
open CompactReservedSchedule (bank)
open CompactChildHeadersArithmetic

def headerProgram (ops : List Op) :=
  extend (extend (extend (compile (a:=2) ops).2 1) CompactReservedAxisPorts.count) 2

def setup (c m : ℕ) := extend (extend (extend (CompactReservedHeaders.program c m) 1)
  CompactReservedAxisPorts.count) 2

theorem setup_runs (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m) (hd : 0<d) (hK : 0<K)
    (hD : reserved c m d G K≤D) (f : ℤ → Fin 6) :
    HoareTime (setup c m) (fun v => v=bank (initial D K rho ell q d G) f)
      (fun v => v=bank (prepared c m D K rho ell q d G 0) f)
      (CompactReservedHeaders.cost c m D K rho ell q d G) :=
  hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (CompactReservedHeaders.runs c m D K rho ell q d G hc hm hd hK hD)
    (CountedLoopReuseAlphabet.one f 0)) (SharedBank.empty CompactReservedAxisPorts.count 2)) (SharedBank.empty 2 2)

def switch : List Op := [.existing (.command (.erase 5)),.existing (.command (.copy 11 5 (by decide)))]
def cleanup : List Op := ([5,9,10,11] : List (Fin 28)).map (fun i => .existing (.command (.erase i)))

theorem switch_runs (c m D K rho ell q d G i : ℕ) (f : ℤ → Fin 6) :
    HoareTime (headerProgram switch) (fun v => v=bank (prepared c m D K rho ell q d G i) f)
      (fun v => v=bank (prepared c m D K rho ell q d G (D-high c m d G K)) f)
      (scheduleCost switch (prepared c m D K rho ell q d G i)) := by
  have hv : validSchedule switch (prepared c m D K rho ell q d G i) := by
    simp [switch,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
      prepared,Function.update]
  have he : execute switch (prepared c m D K rho ell q d G i)=
      prepared c m D K rho ell q d G (D-high c m d G K) := by
    funext s
    fin_cases s <;> simp [switch,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,prepared,Function.update]
  have hh := schedule_runs (a:=2) switch _ hv
  rw [he] at hh
  exact hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hh (CountedLoopReuseAlphabet.one f 0))
    (SharedBank.empty CompactReservedAxisPorts.count 2)) (SharedBank.empty 2 2)

theorem cleanup_runs (c m D K rho ell q d G i : ℕ) (f : ℤ → Fin 6) :
    HoareTime (headerProgram cleanup) (fun v => v=bank (prepared c m D K rho ell q d G i) f)
      (fun v => v=bank (initial D K rho ell q d G) f)
      (scheduleCost cleanup (prepared c m D K rho ell q d G i)) := by
  have hv : validSchedule cleanup (prepared c m D K rho ell q d G i) := by
    simp [cleanup,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
      prepared,Function.update]
  have he : execute cleanup (prepared c m D K rho ell q d G i)=initial D K rho ell q d G := by
    funext s
    fin_cases s <;> simp [cleanup,execute,eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,prepared,initial,Function.update]
  have hh := schedule_runs (a:=2) cleanup _ hv
  rw [he] at hh
  exact hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hh (CountedLoopReuseAlphabet.one f 0))
    (SharedBank.empty CompactReservedAxisPorts.count 2)) (SharedBank.empty 2 2)

end
end IntegerMultBounds.Machine.CompactReservedLifecycle
