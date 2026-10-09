import IntegerMultBounds.Machine.CountedRankSplitRun

/-! Direct endpoint for the actual short growing counter used by RepairScan.
All copied high bits come from physical blank cells, with charged movement. -/
namespace IntegerMultBounds.Machine.CountedRankSplitEndpoint
noncomputable section
open CountedRankSplitBank

def counterBase : ℤ → Fin 5 :=
  fun j => PartitionMarked.encoding.encode (GrowingCounter.emptyTape j)

theorem encoded_bits (f : ℤ → Fin 4) (p : ℤ) (cs : List Bool) :
    (fun j => PartitionMarked.encoding.encode (putBits f p cs j)) =
      putWord (fun j => PartitionMarked.encoding.encode (f j)) p
        (cs.map bitSymbol) := by
  induction cs generalizing p with
  | nil => rfl
  | cons b cs ih =>
    funext j
    by_cases hj : j = p
    · subst j
      simp only [putBits, List.map_cons, putWord, Function.update_self]
      cases b <;> rfl
    · simp only [putBits, List.map_cons, putWord, Function.update_of_ne hj]
      exact congrFun (ih (p+1)) j

theorem counter_word (cs : List Bool) :
    RepairScan.ctrTape cs = putWord counterBase 1 (cs.map bitSymbol) :=
  encoded_bits GrowingCounter.emptyTape 1 cs

theorem counter_tail (cs : List Bool) (z : ℤ) (hz : 1+cs.length ≤ z) :
    counterBase z = blank := by
  have hne : z ≠ 0 := by omega
  simp only [counterBase, GrowingCounter.emptyTape, hne, ↓reduceIte]
  rfl

/-- One fixed program splits the actual scan counter. Original counter cells,
q/b/n words and heads are exact; every generated header/private tape is blank.
There is no lower bound on the stored counter length. -/
theorem runs (g h : ℤ → Fin 5) (v w : ℤ) (cs : List Bool)
    (hs : Fin 3 → List Bool) (q b n : ℕ) (hq : 0 < q) (hb : 0 < b)
    (hv : ∀ i, Counter.value (hs i) = values q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (CountedRankSplitRun.program (a := 1))
      (fun u => u = bank (RepairScan.ctrTape cs) g h 1 v w hs none none)
      (fun u => u = bank (RepairScan.ctrTape cs)
        (putWord g v ((Gather.field cs 0 (n*q)).map bitSymbol))
        (putWord h w ((Gather.field cs (n*q) (n*b)).map bitSymbol))
        1 v w hs none none)
      (CountedRankSplitRun.budget n q b) := by
  simpa only [counter_word] using
    CountedRankSplitRun.runs counterBase g h v w cs hs q b n hq hb hv hc
      (counter_tail cs)

theorem runs_linear (g h : ℤ → Fin 5) (v w : ℤ) (cs : List Bool)
    (hs : Fin 3 → List Bool) (q b n : ℕ) (hq : 0 < q) (hb : 0 < b)
    (hv : ∀ i, Counter.value (hs i) = values q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (CountedRankSplitRun.program (a := 1))
      (fun u => u = bank (RepairScan.ctrTape cs) g h 1 v w hs none none)
      (fun u => u = bank (RepairScan.ctrTape cs)
        (putWord g v ((Gather.field cs 0 (n*q)).map bitSymbol))
        (putWord h w ((Gather.field cs (n*q) (n*b)).map bitSymbol))
        1 v w hs none none)
      (400*((n+1)*(q+b+1))) :=
  (runs g h v w cs hs q b n hq hb hv hc).consequence
    (fun _ h => h) (fun _ h => h) (CountedRankSplitRun.budget_linear n q b)

/-- The two literal output words reconstruct the original in-range rank. -/
theorem reconstructs (cs : List Bool) (q b n : ℕ)
    (hv : Counter.value cs < 2^(n*q+n*b)) :
    Counter.value (Gather.field cs 0 (n*q)) +
      2^(n*q)*Counter.value (Gather.field cs (n*q) (n*b)) = Counter.value cs :=
  CountedRankSplitData.value_decomposition cs q b n hv

end
end IntegerMultBounds.Machine.CountedRankSplitEndpoint
