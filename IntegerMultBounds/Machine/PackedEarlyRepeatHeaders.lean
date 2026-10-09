import IntegerMultBounds.Machine.PackedPrefixRepeatHeadersReserved

/-! Shared physical repetition metadata for all four early loads. The gap-source
loads use the retained H factor and actual upstream control gap; the prefix-source
loads use L. Both factors are produced by one schedule and physically erased. -/
namespace IntegerMultBounds.Machine.PackedEarlyRepeatHeaders
noncomputable section
open CompactGadgetReservationHeadersWords
open CompactGadgetReservationHeadersOps
open PackedPrefixRepeatHeaders (initial construction values repetitions)
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersCarvedData (gap)
variable {a : ℕ}

def beforeSource (d G n q : ℕ) := 2^(d*G-n*q)
def eraseSlots : List (Fin 25) := [7,8,9,11,12,13]
def schedule := construction++eraseSlots.map Op.erase
def cleanup : List Op := [.erase 10,.erase 14]
def finished (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) : Words :=
  fun i => if h : i.val<7 then some (hs ⟨i.val,h⟩)
    else if i=10 then some (RecursiveChildQuotientsConstant.bits (beforeSource d G n q))
    else if i=14 then some (RecursiveChildQuotientsConstant.bits (repetitions d G n q b gap))
    else none
def program := CompactGadgetReservationHeadersOps.program (a := a) schedule
def cleanupProgram := CompactGadgetReservationHeadersOps.program (a := a) cleanup

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
    Fin.addCases,value,word,hv,values,finished,repetitions,beforeSource,
    RecursiveChildQuotientsConstant.bits_value,Nat.mul_comm]

theorem constructs (hs : Fin 7 → List Bool) (d G n q b gap rows : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values d G n q b gap rows i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hG : 0<G) (hq : 0<q) (hb : 0<b) (hcap : n*q≤d*G) :
    HoareTime (program (a := a)) (fun v => v=bank (initial hs))
      (fun v => v=bank (finished hs d G n q b gap)) (bound schedule (initial hs)) := by
  have h := CompactGadgetReservationHeadersOps.runs (a := a) schedule (initial hs)
    (ready hs d G n q b gap rows hv hc hG hq hb hcap)
  rwa [executes hs d G n q b gap rows hv] at h

theorem clears (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) :
    execute cleanup (finished hs d G n q b gap)=initial hs := by
  funext i; fin_cases i <;> simp [execute,cleanup,transform,finished,initial,Fin.addCases]

theorem cleans (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) :
    HoareTime (cleanupProgram (a := a)) (fun v => v=bank (finished hs d G n q b gap))
      (fun v => v=bank (initial hs)) (bound cleanup (finished hs d G n q b gap)) := by
  have hr : ReadyList cleanup (finished hs d G n q b gap) := by
    simp [cleanup,ReadyList,Ready,Source,finished,word,transform,
      RecursiveChildQuotientsConstant.bits_canonical]
  have h := CompactGadgetReservationHeadersOps.runs (a := a) cleanup
    (finished hs d G n q b gap) hr
  rwa [clears] at h

/-- The two gap-source factors use the same actual control-gap word as the
prefix-source factor. This identity changes no source ordering or array cell. -/
theorem gap_factorization (s : Shape) (n q b : ℕ) (hb : n*b≤s.H) :
    gap s (n*q) .temp=beforeSource s.axes s.guard n q*2^(n*b)*gap s (n*b) .control := by
  change 2^((s.H-n*q)+s.H+s.F+s.active*s.chunk)=
    2^(s.H-n*q)*2^(n*b)*2^((s.H-n*b)+s.F+s.active*s.chunk)
  rw [←pow_add,←pow_add]
  congr 1
  omega

end
end IntegerMultBounds.Machine.PackedEarlyRepeatHeaders
