import IntegerMultBounds.Machine.CompactGadgetReservationHeadersOps
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedData

/-! Actual finite descriptor schedule from seven retained original headers
and the physically installed carved width. The complete caller constructs
that width from original n and packing-width descriptors. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedSchedule
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersCarvedData
open CompactGadgetReservationHeadersData (roundFront roundBack)
open CompactGadgetReservationHeadersWords
open CompactGadgetReservationHeadersOps
variable {a : ℕ}

def originalValues (s : Shape) (n rows : ℕ) : Fin 7 → ℕ :=
  ![s.chunk,s.axes,s.guard,n,s.active,rows,s.payload]
def initial (hs : Fin 7 → List Bool) (w : ℕ) : Words :=
  Function.update (CompactGadgetReservationHeadersSchedule.initial hs) 10
    (some (RecursiveChildQuotientsConstant.bits w))
def gapSource : Front → Fin 25 | .temp => 12 | .control => 14
def prefixSource : Front → Fin 25 | .temp => 22 | .control => 8

def construction (f : Front) : List Op := [
  .constant 2 7,
  .product ![2,1,8] (by decide),
  .product ![7,8,9] (by decide),
  .product ![0,4,11] (by decide),
  .round ![9,0,12] (by decide),
  .round ![8,0,13] (by decide),
  .difference ![12,8,14] (by decide),
  .difference ![gapSource f,10,15] (by cases f <;> decide),
  .difference ![13,10,16] (by decide),
  .constant 0 22,
  .power ![prefixSource f,17] (by cases f <;> decide),
  .power ![11,18] (by decide),
  .power ![15,19] (by decide),
  .power ![16,20] (by decide),
  .product ![17,5,21] (by decide),
  .product ![18,19,23] (by decide),
  .product ![20,6,24] (by decide)]

def eraseSlots : List (Fin 25) := [7,8,9,11,12,13,14,15,16,17,18,19,20,22]
def cleanup : List Op := eraseSlots.map Op.erase
def schedule (f : Front) := construction f++cleanup
def program (f : Front) := CompactGadgetReservationHeadersOps.program (a := a) (schedule f)
def outputSlots : Fin 4 → Fin 25 := ![21,23,24,10]
def finished (hs : Fin 7 → List Bool) (s : Shape) (_n rows w : ℕ) (f : Front) : Words :=
  fun i => if h : i.val < 7 then some (hs ⟨i.val,h⟩) else
    if i = 21 then some (RecursiveChildQuotientsConstant.bits (s.prefixRange rows f)) else
    if i = 23 then some (RecursiveChildQuotientsConstant.bits (gap s w f)) else
    if i = 24 then some (RecursiveChildQuotientsConstant.bits (suffix s w)) else
    if i = 10 then some (RecursiveChildQuotientsConstant.bits w) else none

theorem ready (hs : Fin 7 → List Bool) (s : Shape) (n rows w : ℕ) (f : Front)
    (hv : ∀ i, Counter.value (hs i) = originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hw : w ≤ s.H) :
    ReadyList (schedule f) (initial hs w) := by
  have hH : 0 < s.H := Nat.mul_pos hd hG
  have hF := RoundedRowDescriptor.rows_le (2*s.H) s.chunk (by omega) hK
  have hB := RoundedRowDescriptor.rows_le s.H s.chunk hH hK
  simp only [Shape.H,CompactGadgetReservationCapacity.capacity] at hH hw hF hB
  have hF' := hF
  rw [Nat.mul_comm 2] at hF'
  cases f <;>
    simp [schedule,construction,cleanup,eraseSlots,ReadyList,Ready,transform,Source,install,
      initial,Fin.addCases,value,word,hv,hc,originalValues,CompactGadgetReservationHeadersSchedule.initial,gapSource,prefixSource,
      RecursiveChildQuotientsConstant.bits_value,RecursiveChildQuotientsConstant.bits_canonical,
      ] <;> omega

theorem executes (hs : Fin 7 → List Bool) (s : Shape) (n rows w : ℕ) (f : Front)
    (hv : ∀ i, Counter.value (hs i) = originalValues s n rows i)
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hw : w ≤ s.H) :
    execute (schedule f) (initial hs w) = finished hs s n rows w f := by
  have hH : 0 < s.H := Nat.mul_pos hd hG
  have hg := gap_range s w hw f hH hK
  have hb := suffix_exponent s w hw hH hK
  funext i
  fin_cases i
  all_goals simp [schedule,construction,cleanup,eraseSlots,execute,transform,install,
    initial,Fin.addCases,value,word,hv,originalValues,CompactGadgetReservationHeadersSchedule.initial,gapSource,prefixSource,finished,
    RecursiveChildQuotientsConstant.bits_value]
  all_goals cases f <;> simp_all [Shape.prefixRange,Shape.prefixBits,gap,suffix,gapBits,afterBits,
    Shape.H,CompactGadgetReservationCapacity.capacity,gapExponent,suffixExponent,
    roundFront,roundBack,RecursiveChildQuotientsConstant.bits_value,Nat.mul_comm]

theorem constructs (hs : Fin 7 → List Bool) (s : Shape) (n rows w : ℕ) (f : Front)
    (hv : ∀ i, Counter.value (hs i) = originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hw : w ≤ s.H) :
    HoareTime (program (a := a) f)
      (fun v => v = CompactGadgetReservationHeadersWords.bank (initial hs w))
      (fun v => v = CompactGadgetReservationHeadersWords.bank (finished hs s n rows w f))
      (bound (schedule f) (initial hs w)) := by
  have h := CompactGadgetReservationHeadersOps.runs (a := a) (schedule f) (initial hs w)
    (ready hs s n rows w f hv hc hK hd hG hw)
  rwa [executes hs s n rows w f hv hK hd hG hw] at h

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedSchedule
