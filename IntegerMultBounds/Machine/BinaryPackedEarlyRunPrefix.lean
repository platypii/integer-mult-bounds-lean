import IntegerMultBounds.Machine.BinaryPackedEarlyRunGap

/-! Actual second and fourth child runs on the common unchanged role word.
The offset producer, swap/rotation/swap, and offset erasure are all executed. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyRunPrefix
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape
open BinaryPackedEarlyGeometry
open BinaryPackedEarlyRunBank
open BinaryPackedEarlyRunGap (values)

 def second := Placement.placed BinaryPackedEarlyPrefixParityLoad.program
  (CleanSubbank.placement prefixNative prefixPorts prefix_injective)
 def fourth := Placement.placed BinaryPackedEarlyPrefixNegativeLoad.program
  (CleanSubbank.placement prefixNative prefixPorts prefix_injective)
 def secondCost (s : Shape) (q b n rows : ℕ) (sc : Fin 4 → List Bool) (hs : Fin 7 → List Bool)
    (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryPackedEarlyPrefixParityLoad.cost (prefixHeaders hs) sc q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*b)) hb hbq
 def fourthCost (s : Shape) (q b n rows : ℕ) (sc : Fin 4 → List Bool) (hs : Fin 7 → List Bool)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryPackedEarlyPrefixNegativeLoad.cost (prefixHeaders hs) Z sc q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*b)) hb hbq

 theorem second_runs (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (st sc : Fin 4 → List Bool) (hs : Fin 7 → List Bool) (Z : List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hr : 0<rows) (hp : 0<s.payload)
    (hv : ∀ i, Counter.value (hs i)=values s q b n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hsc : ∀ i, Counter.value (sc i)=BinaryRadixRangePrepare.values (controlPrefix s q n rows) (controlGap s b n) (suffix s (n*b)) (n*b) i)
    (hcc : ∀ i, GrowingCounterData.Canonical (sc i))
    (x : Fin (rows*s.recordWidth) → Bool) :
    HoareTime second (fun z => z=BinaryPackedEarlyRunBank.input (store (bank st sc hs Z) x))
      (fun z => z=BinaryPackedEarlyRunBank.input (store (bank st sc hs Z) (BinaryPackedEarlyArray.second s q b n rows hq hw hb hbq x)))
      (secondCost s q b n rows sc hs hb hbq) := by
  have h := BinaryPackedEarlyPrefixParityLoad.runs (prefixCaller (bank st sc hs Z)) (prefixHeaders hs) Z sc
    q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*b)) hb hbq hr
    (by unfold targetTail; positivity) (by unfold controlGap tempTail middle; positivity)
    (by unfold suffix; positivity) (hv 0) (hv 1) (hv 2) (hv 6) (hv 3)
    (by intro i; fin_cases i <;> exact hc _)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
    (by constructor
        · intro i; fin_cases i <;> exact (CountedLoopReuseAlphabet.encoding_binary _).symm
        · intro i; fin_cases i <;> rfl)
    hsc hcc (BinaryPackedEarlyArray.asControl s q b n rows hq hw x)
  apply prefix_lift (control_volume s q b n rows hq hw) _ (bank st sc hs Z) x _ _
  exact h

 theorem fourth_runs (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (st sc : Fin 4 → List Bool) (hs : Fin 7 → List Bool) (Z : List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hr : 0<rows) (hp : 0<s.payload)
    (hv : ∀ i, Counter.value (hs i)=values s q b n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n)
    (hsc : ∀ i, Counter.value (sc i)=BinaryRadixRangePrepare.values (controlPrefix s q n rows) (controlGap s b n) (suffix s (n*b)) (n*b) i)
    (hcc : ∀ i, GrowingCounterData.Canonical (sc i))
    (x : Fin (rows*s.recordWidth) → Bool) :
    HoareTime fourth (fun z => z=BinaryPackedEarlyRunBank.input (store (bank st sc hs Z) x))
      (fun z => z=BinaryPackedEarlyRunBank.input (store (bank st sc hs Z) (BinaryPackedEarlyArray.fourth s q b n rows hq hw Z hb hbq x)))
      (fourthCost s q b n rows sc hs Z hb hbq) := by
  have h := BinaryPackedEarlyPrefixNegativeLoad.runs (prefixCaller (bank st sc hs Z)) (prefixHeaders hs) Z sc
    q b n rows (targetTail s q n) (controlGap s b n) (suffix s (n*b)) hb hbq hr
    (by unfold targetTail; positivity) (by unfold controlGap tempTail middle; positivity)
    (by unfold suffix; positivity) (hv 0) (hv 1) (hv 2) (hv 6) (hv 3)
    (by intro i; fin_cases i <;> exact hc _) hZ
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
    (by constructor
        · intro i; fin_cases i <;> exact (CountedLoopReuseAlphabet.encoding_binary _).symm
        · intro i; fin_cases i <;> rfl)
    hsc hcc (BinaryPackedEarlyArray.asControl s q b n rows hq hw x)
  apply prefix_lift (control_volume s q b n rows hq hw) _ (bank st sc hs Z) x _ _
  exact h

end
end IntegerMultBounds.Machine.BinaryPackedEarlyRunPrefix
