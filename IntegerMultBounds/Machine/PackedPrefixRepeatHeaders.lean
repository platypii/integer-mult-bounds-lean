import IntegerMultBounds.Machine.CompactGadgetReservationHeadersSchedule

/-! Paid prefix-source repetition geometry. The actual gap and role-count
words come from the earlier reservation-header stage; this fixed program reads
d/globalGuard/n/q/b and them to construct L, retaining K=roleRows on its port.
No repetition count or repeated-offset word is supplied to this constructor. -/
namespace IntegerMultBounds.Machine.PackedPrefixRepeatHeaders
noncomputable section
open CompactGadgetReservationHeadersWords
open CompactGadgetReservationHeadersOps
variable {a : ℕ}

def values (d G n q b gap rows : ℕ) : Fin 7 → ℕ := ![d,G,n,q,b,gap,rows]
def repetitions (d G n q b gap : ℕ) := 2^(d*G-n*q)*2^(n*b)*gap

def initial (hs : Fin 7 → List Bool) : Words :=
  Fin.addCases (m := 7) (n := 18) (fun i => some (hs i)) (fun _ => none)
def construction : List Op := [
  .product ![1,0,7] (by decide),
  .product ![3,2,8] (by decide),
  .difference ![7,8,9] (by decide),
  .power ![9,10] (by decide),
  .product ![4,2,11] (by decide),
  .power ![11,12] (by decide),
  .product ![10,12,13] (by decide),
  .product ![13,5,14] (by decide)]
def eraseSlots : List (Fin 25) := [7,8,9,10,11,12,13]
def schedule := construction++eraseSlots.map Op.erase

def finished (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) : Words :=
  fun i => if h : i.val<7 then some (hs ⟨i.val,h⟩) else if i=14 then
    some (RecursiveChildQuotientsConstant.bits (repetitions d G n q b gap)) else none

def program := CompactGadgetReservationHeadersOps.program (a := a) schedule

theorem ready (hs : Fin 7 → List Bool) (d G n q b gap rows : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values d G n q b gap rows i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hG : 0<G) (hq : 0<q) (hb : 0<b) (hcap : n*q≤d*G) :
    ReadyList schedule (initial hs) := by
  simp [schedule,construction,eraseSlots,ReadyList,Ready,transform,Source,install,
    initial,Fin.addCases,value,word,hv,hc,values,
    RecursiveChildQuotientsConstant.bits_value,RecursiveChildQuotientsConstant.bits_canonical]
  exact ⟨hG,hq,hcap,hb⟩

theorem executes (hs : Fin 7 → List Bool) (d G n q b gap rows : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values d G n q b gap rows i) :
    execute schedule (initial hs)=finished hs d G n q b gap := by
  funext i; fin_cases i
  all_goals simp [schedule,construction,eraseSlots,execute,transform,install,initial,
    Fin.addCases,value,word,hv,values,finished,repetitions,
    RecursiveChildQuotientsConstant.bits_value,Nat.mul_comm]

theorem constructs (hs : Fin 7 → List Bool) (d G n q b gap rows : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values d G n q b gap rows i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hG : 0<G) (hq : 0<q) (hb : 0<b) (hcap : n*q≤d*G) :
    HoareTime (program (a := a))
      (fun v => v=bank (initial hs)) (fun v => v=bank (finished hs d G n q b gap))
      (bound schedule (initial hs)) := by
  have h := CompactGadgetReservationHeadersOps.runs (a := a) schedule (initial hs)
    (ready hs d G n q b gap rows hv hc hG hq hb hcap)
  rwa [executes hs d G n q b gap rows hv] at h

/-- The role count K is the same literal original upstream word, not a new
oracle or a value-dependent control parameter. -/
theorem output_values (hs : Fin 7 → List Bool) (d G n q b gap rows : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values d G n q b gap rows i) :
    value (finished hs d G n q b gap) 14=repetitions d G n q b gap ∧
      value (finished hs d G n q b gap) 6=rows := by
  simp [finished,value,word,hv,values,RecursiveChildQuotientsConstant.bits_value]


def cleanupProgram := (CompactGadgetReservationHeadersOps.code (a := a) (.erase 14)).2

theorem cleared (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) :
    transform (.erase 14) (finished hs d G n q b gap)=initial hs := by
  funext i; fin_cases i <;> simp [transform,finished,initial,Fin.addCases]

theorem cleans (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) :
    HoareTime (cleanupProgram (a := a))
      (fun v => v=bank (finished hs d G n q b gap)) (fun v => v=bank (initial hs))
      (2*(RecursiveChildQuotientsConstant.bits (repetitions d G n q b gap)).length+4) := by
  have h := CompactGadgetReservationHeadersOps.one (a := a) (.erase 14)
    (finished hs d G n q b gap)
    (by simp [Ready,Source,finished,word,RecursiveChildQuotientsConstant.bits_canonical])
  rw [cleared] at h
  simpa [cleanupProgram,cost,word,finished] using h

end
end IntegerMultBounds.Machine.PackedPrefixRepeatHeaders
