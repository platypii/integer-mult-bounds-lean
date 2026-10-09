import IntegerMultBounds.Machine.CompactReservedAxisRun

/-! Both reserved intervals use a fixed counted program reading their generated
count descriptors; no repetition count enters finite control. -/
namespace IntegerMultBounds.Machine.CompactReservedSchedule
noncomputable section
open CompactReservedHeaders
open CompactFallbackAxisRun (Array Width word volume)
open CompactReservedAxisRun (width_run)

def endpoint (inverse : Bool) (c m D K rho ell q d G start n : ℕ) (f : Array D K ell) :=
  CompactReservedAxisRun.bank (prepared c m D K rho ell q d G (start+n))
    (word (CompactReservedAxisRun.run inverse D K rho ell q start n f))
def bank (st : ActiveRepairRankHeadersCommands.State) (f : ℤ → Fin 6) :=
  CountedLoopHeaderClean.bank (CompactReservedAxisRun.bank st f)
def program (inverse : Bool) (src : Fin 28) :=
  CountedLoopHeaderClean.program (CompactReservedAxisRun.code inverse).2
    (Fin.castAdd CompactReservedAxisPorts.count (Fin.castAdd 1 (Fin.castAdd 15 src)))
def cost (D K ell q n : ℕ) :=
  n*(CompactFallbackAxisBudget.constant*volume D K ell q)+6*n+
    11*(RecursiveChildQuotientsConstant.bits n).length+35

theorem runs (inverse : Bool) (c m D K rho ell q d G start n : ℕ) (src : Fin 28)
    (hc : prepared c m D K rho ell q d G start src=some n)
    (hK : 0<K) (hr : rho<K) (hfit : start+n≤D)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime (program inverse src)
      (fun v => v=bank (prepared c m D K rho ell q d G start) (word f))
      (fun v => v=bank (prepared c m D K rho ell q d G (start+n))
        (word (CompactReservedAxisRun.run inverse D K rho ell q start n f))) (cost D K ell q n) := by
  have hh := CountedLoopHeaderClean.runs (CompactReservedAxisRun.code inverse).2
    (Fin.castAdd CompactReservedAxisPorts.count (Fin.castAdd 1 (Fin.castAdd 15 src)))
    (RecursiveChildQuotientsConstant.bits n) n (fun i => endpoint inverse c m D K rho ell q d G start i f)
    (fun _ => CompactFallbackAxisBudget.constant*volume D K ell q)
    (by simp [endpoint,CompactReservedAxisRun.run,CompactReservedAxisRun.bank,CompactReservedAxisRun.common,
      ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,
      ActiveRepairRankHeadersCommands.caller,hc])
    (RecursiveChildQuotientsConstant.bits_value n) (by
      intro i hi
      have hb := CompactReservedAxisRun.runs inverse c m D K rho ell q d G (start+i) hK hr (by omega)
        (CompactReservedAxisRun.run inverse D K rho ell q start i f) (width_run inverse D K rho ell q start i f hw)
      simpa only [endpoint,CompactReservedAxisRun.run,Nat.add_assoc] using hb)
  simpa only [program,bank,endpoint,CompactReservedAxisRun.run,Nat.add_zero,cost,CountedLoopHeaderClean.cost,
    Finset.sum_const,Finset.card_range,smul_eq_mul] using hh

end
end IntegerMultBounds.Machine.CompactReservedSchedule
