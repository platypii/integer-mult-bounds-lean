import IntegerMultBounds.Machine.BinaryPackedEarlyRunPrefix

/-! Actual four-load packed-early execution on one unchanged serialized role.
Every offset is constructed from original controls and the current source field;
all four machines share blank workspace and erase their own offset table. The
retained shape/repetition words are explicit paid-upstream stage interfaces. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyRun
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape
open BinaryPackedEarlyGeometry
open BinaryPackedEarlyRunBank (bank store Work)
open BinaryPackedEarlyRunGap (values firstCost thirdCost)
open BinaryPackedEarlyRunPrefix (secondCost fourthCost)

 def program := seq (seq (seq BinaryPackedEarlyRunGap.first BinaryPackedEarlyRunPrefix.second)
    BinaryPackedEarlyRunGap.third) BinaryPackedEarlyRunPrefix.fourth
 def input := BinaryPackedEarlyRunBank.input
 def cost (s : Shape) (q b n rows : ℕ) (st sc : Fin 4 → List Bool) (hs : Fin 7 → List Bool)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  firstCost s q b n rows st hs Z hb hbq+secondCost s q b n rows sc hs hb hbq+
  thirdCost s q b n rows st hs Z hb hbq+fourthCost s q b n rows sc hs Z hb hbq+3

 theorem runs (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (st sc : Fin 4 → List Bool) (hs : Fin 7 → List Bool) (Z : List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hr : 0<rows) (hp : 0<s.payload)
    (hv : ∀ i, Counter.value (hs i)=values s q b n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n)
    (hst : ∀ i, Counter.value (st i)=BinaryRadixRangePrepare.values rows (tempGap s q b n) (suffix s (n*q)) (n*q) i)
    (hct : ∀ i, GrowingCounterData.Canonical (st i))
    (hsc : ∀ i, Counter.value (sc i)=BinaryRadixRangePrepare.values (controlPrefix s q n rows) (controlGap s b n) (suffix s (n*b)) (n*b) i)
    (hcc : ∀ i, GrowingCounterData.Canonical (sc i))
    (x : Fin (rows*s.recordWidth) → Bool) :
    HoareTime program (fun z => z=input (store (bank st sc hs Z) x))
      (fun z => z=input (store (bank st sc hs Z) (BinaryPackedEarlyArray.run s q b n rows hq hw Z hb hbq x)))
      (cost s q b n rows st sc hs Z hb hbq) := by
  let x1 := BinaryPackedEarlyArray.first s q b n rows hq hw Z hb hbq x
  let x2 := BinaryPackedEarlyArray.second s q b n rows hq hw hb hbq x1
  let x3 := BinaryPackedEarlyArray.third s q b n rows hq hw Z hb hbq x2
  have h1 := BinaryPackedEarlyRunGap.first_runs s q b n rows hq hw st sc hs Z hb hbq hr hp hv hc hZ hst hct x
  have h2 := BinaryPackedEarlyRunPrefix.second_runs s q b n rows hq hw st sc hs Z hb hbq hr hp hv hc hsc hcc x1
  have h3 := BinaryPackedEarlyRunGap.third_runs s q b n rows hq hw st sc hs Z hb hbq hr hp hv hc hZ hst hct x2
  have h4 := BinaryPackedEarlyRunPrefix.fourth_runs s q b n rows hq hw st sc hs Z hb hbq hr hp hv hc hZ hsc hcc x3
  exact (((h1.seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

/-- The exact output of the physical program has packedEarly address semantics
on every cell of the complete reservation, including bad/dirty addresses. -/
 theorem output_semantics (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hw : n*b≤s.H)
    (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n)
    (x : Fin (rows*s.recordWidth) → Bool) (a : BinaryPackedEarlyLayout.Address s q b n rows) :
    ∃ (v : BinaryPackedEarlyData.Target q n) (w : BinaryPackedEarlyData.Temp b n),
      ((v.val : ℤ),(w.val : ℤ))=
        Compact.packedEarly ((2 : ℤ)^q) ((2 : ℤ)^b) (Z.map Compact.PowerTwo.ctrl) a.1.val a.2.1.val ∧
      BinaryPackedEarlyArray.run s q b n rows hq hw Z hb hbq x
        (BinaryPackedEarlyLayout.index s q b n rows hq hw (v,w,a.2.2))=
          x (BinaryPackedEarlyLayout.index s q b n rows hq hw a) :=
  BinaryPackedEarlyCorrect.packed_entry s q b n rows hq hw Z hb hbq hZ x a

end
end IntegerMultBounds.Machine.BinaryPackedEarlyRun
