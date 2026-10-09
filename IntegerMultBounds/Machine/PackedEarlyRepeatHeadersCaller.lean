import IntegerMultBounds.Machine.PackedEarlyRepeatHeadersBudget
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedCaller

/-! Original row/width descriptors supply the actual carved control gap and
role count; that paid endpoint supplies both early repetition factors. No gap,
role-row or repetition word is assumed on the original caller. -/
namespace IntegerMultBounds.Machine.PackedEarlyRepeatHeadersCaller
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersCarvedData (gap)
open CompactGadgetReservationHeadersCaller (headerWords originals permanent)
open CompactGadgetReservationHeadersCarvedCaller (prepared setupProgram headerCost)
open CompactGadgetReservationData (rowCount)
open Networks.Shared50ModularControl (prime)
open RecursiveChildQuotientsConstant (bits)
variable {t : ℕ}

def focus (Q B : Fin t) : Fin 9 → Fin ((25+t)+15) :=
  ![Fin.castAdd 15 (Fin.castAdd t 1),Fin.castAdd 15 (Fin.castAdd t 2),
    Fin.castAdd 15 (Fin.castAdd t 3),Fin.castAdd 15 (Fin.natAdd 25 Q),
    Fin.castAdd 15 (Fin.natAdd 25 B),Fin.castAdd 15 (Fin.castAdd t 23),
    Fin.castAdd 15 (Fin.castAdd t 5),Fin.castAdd 15 (Fin.castAdd t 7),
    Fin.castAdd 15 (Fin.castAdd t 8)]
theorem focus_injective (Q B : Fin t) (hQB : Q≠B) : Function.Injective (focus Q B) := by
  intro i j h
  have hval := congrArg Fin.val h
  have hqb : Q.val≠B.val := fun he => hQB (Fin.ext he)
  fin_cases i <;> fin_cases j
  all_goals simp_all [focus,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd]
  all_goals omega

def inputs (hs : Fin 6 → List Bool) (qs bs : List Bool) (s : Shape) (n b r c : ℕ) : Fin 7 → List Bool :=
  ![hs 1,hs 2,hs 3,qs,bs,bits (gap s (n*b) .control),bits (rowCount r c)]

theorem input_values (hs : Fin 6 → List Bool) (qs bs : List Bool) (s : Shape) (n q b r c : ℕ)
    (hv : ∀ i,Counter.value (hs i)=originals s n i)
    (hvq : Counter.value qs=q) (hvb : Counter.value bs=b) :
    ∀ i,Counter.value (inputs hs qs bs s n b r c i)=
      PackedPrefixRepeatHeaders.values s.axes s.guard n q b (gap s (n*b) .control) (rowCount r c) i := by
  intro i; fin_cases i <;> simp [inputs,PackedPrefixRepeatHeaders.values,hv,originals,hvq,hvb,
    RecursiveChildQuotientsConstant.bits_value]

theorem input_canonical (hs : Fin 6 → List Bool) (qs bs : List Bool) (s : Shape) (n b r c : ℕ)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (cq : GrowingCounterData.Canonical qs) (cb : GrowingCounterData.Canonical bs) :
    ∀ i,GrowingCounterData.Canonical (inputs hs qs bs s n b r c i) := by
  intro i; fin_cases i <;> simp [inputs,hc,cq,cb,RecursiveChildQuotientsConstant.bits_canonical]

theorem input_payload (hs : Fin 6 → List Bool) (spectators : Tapes t prime) (Q B : Fin t)
    (qs bs : List Bool) (s : Shape) (n b r c : ℕ)
    (htQ : spectators.tape Q=RadixZeroFill.encodedBinary qs) (hhQ : spectators.head Q=1)
    (htB : spectators.tape B=RadixZeroFill.encodedBinary bs) (hhB : spectators.head B=1) :
    SharedBank.payload (prepared hs s n r c (n*b) .control spectators) (focus Q B)=
      PackedEarlyRepeatHeadersPlaced.inputPayload (inputs hs qs bs s n b r c) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp only [prepared,focus,
    PackedEarlyRepeatHeadersPlaced.ports,inputs,CompactGadgetReservationHeadersRouting.bank,
    CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,Tapes.append,
    CompactGadgetReservationHeadersWords.bank]
  all_goals simp [CompactGadgetReservationHeadersWords.common,
    CompactGadgetReservationHeadersWords.head,CompactGadgetReservationHeadersWords.tape,
    CompactGadgetReservationHeadersCarvedSchedule.finished,headerWords,
    PackedPrefixRepeatHeaders.initial,htQ,hhQ,htB,hhB]
  all_goals rfl

def repeatProgram (Q B : Fin t) (hQB : Q≠B) :=
  PackedEarlyRepeatHeadersPlaced.program (a := prime) (focus Q B) (focus_injective Q B hQB)
def program (c : ℕ) (R Q B : Fin t) (hQB : Q≠B) :=
  seq (extend (setupProgram c R B .control) 40) (repeatProgram Q B hQB)
def output (hs : Fin 6 → List Bool) (s : Shape) (n q b r c : ℕ)
    (spectators : Tapes t prime) (Q B : Fin t) :=
  PackedEarlyRepeatHeadersPlaced.result (prepared hs s n r c (n*b) .control spectators)
    (focus Q B) s.axes s.guard n q b (gap s (n*b) .control)

theorem runs (hs : Fin 6 → List Bool) (spectators : Tapes t prime) (R Q B : Fin t) (hQB : Q≠B)
    (rs qs bs : List Bool) (r c n q b : ℕ) (s : Shape)
    (hvR : Counter.value rs=r) (cr : GrowingCounterData.Canonical rs) (hr : 0<r) (hc : 0<c)
    (htR : spectators.tape R=RadixZeroFill.encodedBinary rs) (hhR : spectators.head R=1)
    (hvQ : Counter.value qs=q) (cq : GrowingCounterData.Canonical qs) (hq : 0<q)
    (htQ : spectators.tape Q=RadixZeroFill.encodedBinary qs) (hhQ : spectators.head Q=1)
    (hvB : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs) (hb : 0<b)
    (htB : spectators.tape B=RadixZeroFill.encodedBinary bs) (hhB : spectators.head B=1)
    (hv : ∀ i,Counter.value (hs i)=originals s n i)
    (hcan : ∀ i,GrowingCounterData.Canonical (hs i))
    (hK : 0<s.chunk) (hd : 0<s.axes) (hG : 0<s.guard) (hp : 0<s.payload)
    (hwq : n*q≤s.H) (hwb : n*b≤s.H) :
    HoareTime (program c R Q B hQB)
      (fun v => v=CleanSubbank.bank (s := 40) (CompactGadgetReservationHeadersCore.bank (permanent hs spectators)))
      (fun v => v=CleanSubbank.bank (s := 40) (output hs s n q b r c spectators Q B))
      (CompactGadgetReservationHeadersRows.cost r c+1+(53*(n*b)+28)+1+
        headerCost hs r c (n*b) .control+1+
        14*CompactGadgetReservationHeadersCost.coefficient*(rowCount r c*s.recordWidth)) := by
  have hsetup := hoare_extend_eq (CompactGadgetReservationHeadersCarvedCaller.setup_runs hs spectators
    R B rs bs r c n b s .control hvR cr hr hc htR hhR hvB cb hb htB hhB hv hcan hK hd hG hwb)
    (SharedBank.empty 40 prime)
  have hrepeat := PackedEarlyRepeatHeadersPlaced.constructs
    (prepared hs s n r c (n*b) .control spectators) (focus Q B) (focus_injective Q B hQB)
    (inputs hs qs bs s n b r c) s.axes s.guard n q b (gap s (n*b) .control) (rowCount r c)
    (input_values hs qs bs s n q b r c hv hvQ hvB) (input_canonical hs qs bs s n b r c hcan cq cb)
    hG hq hb hwq (input_payload hs spectators Q B qs bs s n b r c htQ hhQ htB hhB)
  have hbound := PackedEarlyRepeatHeadersBudget.construction_bound
    (inputs hs qs bs s n b r c) s n q b (rowCount r c)
    (input_values hs qs bs s n q b r c hv hvQ hvB) (input_canonical hs qs bs s n b r c hcan cq cb)
    hG hq hb hwq hwb (CompactGadgetReservationData.rowCount_pos hc hr) hp
  exact hsetup.seq (hrepeat.consequence (fun _ h => h) (fun _ h => h) hbound)

end
end IntegerMultBounds.Machine.PackedEarlyRepeatHeadersCaller
