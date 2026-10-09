import IntegerMultBounds.Machine.CountedRankSplitPosition

/-! Paid runtime positioning in either direction, with actual blank-clock
initialization and cleanup. Blank counter-tail cells are traversed literally. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankFieldsPosition
noncomputable section
variable {a : ℕ}

def program (m : Move) := seq (seq (CountedRankSplitPosition.setup (a := a))
  (CountedPosition.program m)) CountedRankSplitPosition.cleanup

theorem runs (m : Move) (f : ℤ → Fin (a+4)) (p : ℤ) (bs : List Bool)
    (n : ℕ) (hv : Counter.value bs=n) :
    HoareTime (program (a := a) m) (fun v => v=CountedRankSplitPosition.bank f p bs)
      (fun v => v=CountedRankSplitPosition.bank f (p+n*m.offset) bs)
      (7*n+7*bs.length+28) := by
  have h := ((CountedRankSplitPosition.sets_up f p bs).seq
    (CountedPosition.position_hoare m f p bs n hv)).seq
    (CountedRankSplitPosition.cleans f (p+n*m.offset) bs)
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ActiveRepairRankFieldsPosition
