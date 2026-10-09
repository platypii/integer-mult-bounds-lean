import IntegerMultBounds.Machine.CountedLateRankRun

/-! Actual short RepairScan counter to the three literal late-address words.
No full-width counter assumption, derived-width input, or free head reset. -/
namespace IntegerMultBounds.Machine.CountedLateRankEndpoint
noncomputable section
open CountedLateRankBank
open CountedRankSplitBank (values)
open CountedRankSplitEndpoint (counterBase counter_word counter_tail)

theorem runs (v w u : ℤ → Fin 5) (pv pw pu : ℤ) (cs : List Bool)
    (hs : Fin 3 → List Bool) (q b n : ℕ) (hq : 0 < q) (hb : 0 < b)
    (hv : ∀ i, Counter.value (hs i) = values q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (CountedLateRankRun.program (a := 1))
      (fun z => z = bank (RepairScan.ctrTape cs) v w u 1 pv pw pu hs none none)
      (fun z => z = bank (RepairScan.ctrTape cs)
        (putWord v pv ((Gather.field cs 0 (n*q)).map bitSymbol))
        (putWord w pw ((Gather.field cs (n*q) (n*b)).map bitSymbol))
        (putWord u pu ((Gather.field cs (n*q+n*b) (n*b)).map bitSymbol))
        1 pv pw pu hs none none) (CountedLateRankRun.budget n q b) := by
  have h := CountedLateRankRun.runs_raw (RepairScan.ctrTape cs) v w u 1 pv pw pu hs q b n hq hb hv hc
  rw [counter_word] at h
  have h0 := CountedRankSplitData.cells_word counterBase cs (counter_tail cs) 0 (n*q)
  have h1 := CountedRankSplitData.cells_word counterBase cs (counter_tail cs) (n*q) (n*b)
  have h2 := CountedRankSplitData.cells_word counterBase cs (counter_tail cs) (n*q+n*b) (n*b)
  simp only [Nat.cast_zero,add_zero] at h0
  have he : ((1 : ℤ)+(n*q : ℕ))+(n*b : ℕ) = 1+((n*q+n*b : ℕ) : ℤ) := by push_cast; ring
  simpa only [counter_word,h0,h1,he,h2] using h

theorem runs_linear (v w u : ℤ → Fin 5) (pv pw pu : ℤ) (cs : List Bool)
    (hs : Fin 3 → List Bool) (q b n : ℕ) (hq : 0 < q) (hb : 0 < b)
    (hv : ∀ i, Counter.value (hs i) = values q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (CountedLateRankRun.program (a := 1))
      (fun z => z = bank (RepairScan.ctrTape cs) v w u 1 pv pw pu hs none none)
      (fun z => z = bank (RepairScan.ctrTape cs)
        (putWord v pv ((Gather.field cs 0 (n*q)).map bitSymbol))
        (putWord w pw ((Gather.field cs (n*q) (n*b)).map bitSymbol))
        (putWord u pu ((Gather.field cs (n*q+n*b) (n*b)).map bitSymbol))
        1 pv pw pu hs none none) (600*((n+1)*(q+b+1))) :=
  (runs v w u pv pw pu cs hs q b n hq hb hv hc).consequence
    (fun _ h => h) (fun _ h => h) (CountedLateRankRun.budget_linear n q b)

end
end IntegerMultBounds.Machine.CountedLateRankEndpoint
