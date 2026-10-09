import IntegerMultBounds.Machine.ButterflyIndependentGuardHeaders

/-! Paid guard-header preparation, restoration and selected-axis reset on the
actual counted-axis bank. The coefficient stream is framed literally, so these
operations perform no uncharged re-encoding or record-width changes. -/
namespace IntegerMultBounds.Machine.ButterflyIndependentGuardBank
noncomputable section
open ButterflyIndependentGuardHeaders
open ButterflyAxisHeadersData (initial)
open ActiveRepairRankHeadersCommands (Command)

def bank (D t R q : ℕ) (f : ℤ → Fin 6) :=
  CountedLoopHeaderClean.bank (ButterflyAxisOriginal.bank D t R q f)

def program (cs : List Command) :=
  extend (extend (extend (extend (ActiveRepairRankHeadersCommands.compile (a:=2) cs).2 1) 8)
    ButterflyAxisPorts.count) 2

theorem lift_runs (cs : List Command) (D t u R p q cost : ℕ) (f : ℤ → Fin 6)
    (h : HoareTime (ActiveRepairRankHeadersCommands.compile (a:=2) cs).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial D t R p))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial D u R q)) cost) :
    HoareTime (program cs) (fun v => v=bank D t R p f) (fun v => v=bank D u R q f) cost :=
  hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq h
    (CountedLoopReuseAlphabet.one f 0)) (SharedBank.empty 8 2))
    (SharedBank.empty ButterflyAxisPorts.count 2)) (SharedBank.empty 2 2)

theorem reserves (D t R q : ℕ) (f : ℤ → Fin 6) :
    HoareTime (program reserve) (fun v => v=bank D t R q f)
      (fun v => v=bank D t R (reservation D q) f) (202*(reservation D q+1)) :=
  lift_runs reserve D t t R q (reservation D q) _ f (reserve_runs D t R q)

theorem restores (D t R q : ℕ) (f : ℤ → Fin 6) :
    HoareTime (program restore) (fun v => v=bank D t R (reservation D q) f)
      (fun v => v=bank D t R q f) (1000*(reservation D q+1)) :=
  lift_runs restore D t t R (reservation D q) q _ f (restore_runs D t R q)

theorem resets (D t R p : ℕ) (f : ℤ → Fin 6) :
    HoareTime (program reset) (fun v => v=bank D t R p f)
      (fun v => v=bank D 0 R p f) (202*(t+1)) :=
  lift_runs reset D t 0 R p p _ f (reset_runs D t R p)

end
end IntegerMultBounds.Machine.ButterflyIndependentGuardBank
