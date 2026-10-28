module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallRoundHeaders
public import IntegerMultBounds.MathlibTM2.Node.TopWord

/-! Generated rounding counters meet the word-pass contract at linear total size. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem roundHeaderCost_eq {T : ℕ} (W w q p j E : ℕ) (ports : Fin 4 → Fin T)
    (hsize : q-p+j+(p+E+5) ≤ w) :
    unaryCopiesCost W (roundHeaderValues w q p j E)
      ((List.finRange 4).map (fun i => (i,ports i))) = 12*w+44*W+25 := by
  simp [unaryCopiesCost,roundHeaderValues,List.finRange_succ]
  omega

theorem roundHeaders_ready {T A : ℕ} (w q p j E : ℕ) (ports : Fin 4 → Fin T)
    (tmp sp sg cy : Fin T) (S : Stacks T A)
    (hheaders : ∀ i, S.R (ports i) = List.replicate (roundHeaderValues w q p j E i) tick)
    (htmp : S.R tmp = []) (hsp : S.R sp = []) (hsg : S.R sg = []) (hcy : S.R cy = []) :
    topShiftG tmp (ports 0) (ports 1) (ports 2) (ports 3) sp sg cy
      w (q-p+j) (p+E+5) S.R := by
  simp only [topShiftG,hheaders,List.length_replicate,roundHeaderValues,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,htmp,hsp,hsg,hcy,and_self]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
