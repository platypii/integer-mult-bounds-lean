import IntegerMultBounds.Machine.BinaryPackedEarlyRunBank

/-! Actual first and third child runs on the common unchanged role word.
The offset producer, swap/rotation/swap, and offset erasure are all executed. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyRunGap
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape
open BinaryPackedEarlyGeometry
open BinaryPackedEarlyRunBank

 def values (s : Shape) (q b n rows : ℕ) : Fin 7 → ℕ :=
  ![q,b,n,rows,targetTail s q n,controlGap s b n,
    BinaryPackedEarlyPrefixAction.repeatLength (targetTail s q n) (n*b) (controlGap s b n)]
 def first := Placement.placed BinarySelectedOffsetLoad.program
  (CleanSubbank.placement gapNative gapPorts gap_injective)
 def third := Placement.placed BinaryCorrectionOffsetLoad.program
  (CleanSubbank.placement gapNative gapPorts gap_injective)
 def firstCost (s : Shape) (q b n rows : ℕ) (st : Fin 4 → List Bool) (hs : Fin 7 → List Bool)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  BinarySelectedOffsetLoad.cost (gapHeaders hs) Z st q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*q)) hb hbq
 def thirdCost (s : Shape) (q b n rows : ℕ) (st : Fin 4 → List Bool) (hs : Fin 7 → List Bool)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryCorrectionOffsetLoad.cost (gapHeaders hs) Z st q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*q)) hb hbq

 theorem first_runs (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (st sc : Fin 4 → List Bool) (hs : Fin 7 → List Bool) (Z : List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hr : 0<rows) (hp : 0<s.payload)
    (hv : ∀ i, Counter.value (hs i)=values s q b n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n)
    (hst : ∀ i, Counter.value (st i)=BinaryRadixRangePrepare.values rows (tempGap s q b n) (suffix s (n*q)) (n*q) i)
    (hct : ∀ i, GrowingCounterData.Canonical (st i))
    (x : Fin (rows*s.recordWidth) → Bool) :
    HoareTime first (fun z => z=BinaryPackedEarlyRunBank.input (store (bank st sc hs Z) x))
      (fun z => z=BinaryPackedEarlyRunBank.input (store (bank st sc hs Z) (BinaryPackedEarlyArray.first s q b n rows hq hw Z hb hbq x)))
      (firstCost s q b n rows st hs Z hb hbq) := by
  have h := BinarySelectedOffsetLoad.runs (gapCaller (bank st sc hs Z)) (gapHeaders hs) Z st
    q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*q)) hb hbq hr
    (by unfold targetTail; positivity) (by unfold controlGap tempTail middle; positivity)
    (by unfold suffix; positivity) (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5)
    (by intro i; fin_cases i <;> exact hc _) hZ
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
    (by constructor
        · intro i; fin_cases i <;> exact (CountedLoopReuseAlphabet.encoding_binary _).symm
        · intro i; fin_cases i <;> rfl)
    hst hct (BinaryPackedEarlyArray.asTemp s q b n rows hq hw x)
  apply gap_lift (temp_volume s q b n rows hq hw) _ (bank st sc hs Z) x _ _
  exact h

 theorem third_runs (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (st sc : Fin 4 → List Bool) (hs : Fin 7 → List Bool) (Z : List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hr : 0<rows) (hp : 0<s.payload)
    (hv : ∀ i, Counter.value (hs i)=values s q b n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n)
    (hst : ∀ i, Counter.value (st i)=BinaryRadixRangePrepare.values rows (tempGap s q b n) (suffix s (n*q)) (n*q) i)
    (hct : ∀ i, GrowingCounterData.Canonical (st i))
    (x : Fin (rows*s.recordWidth) → Bool) :
    HoareTime third (fun z => z=BinaryPackedEarlyRunBank.input (store (bank st sc hs Z) x))
      (fun z => z=BinaryPackedEarlyRunBank.input (store (bank st sc hs Z) (BinaryPackedEarlyArray.third s q b n rows hq hw Z hb hbq x)))
      (thirdCost s q b n rows st hs Z hb hbq) := by
  have h := BinaryCorrectionOffsetLoad.runs (gapCaller (bank st sc hs Z)) (gapHeaders hs) Z st
    q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*q)) hb hbq hr
    (by unfold targetTail; positivity) (by unfold controlGap tempTail middle; positivity)
    (by unfold suffix; positivity) (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5)
    (by intro i; fin_cases i <;> exact hc _) hZ
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
    (by constructor
        · intro i; fin_cases i <;> exact (CountedLoopReuseAlphabet.encoding_binary _).symm
        · intro i; fin_cases i <;> rfl)
    hst hct (BinaryPackedEarlyArray.asTemp s q b n rows hq hw x)
  apply gap_lift (temp_volume s q b n rows hq hw) _ (bank st sc hs Z) x _ _
  exact h

end
end IntegerMultBounds.Machine.BinaryPackedEarlyRunGap
