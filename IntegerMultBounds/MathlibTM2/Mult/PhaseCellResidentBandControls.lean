module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClippedBandControls
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledBandControls

/-! Prepare the collector's controls from the retained geometry and folded-column index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def residentBandWidth : Pr P 151 Q A U :=
  .seq (umul 12 124 94 135) (.act (.push (.rt 94) (fun _ => tick) .done))

theorem residentBandWidth_exec (band : ℕ) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hband : (S.R 124).length = band) (h94 : S.R 94 = []) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧ Exec body residentBandWidth (mk v S) (4*band+5)
      (mk v' {S with R := Function.update S.R 94 (List.replicate (12*band+1) tick)}) := by
  simpa only [residentBandWidth,scaledBandWidth] using
    scaledBandWidth_exec (body := body) 12 band v S hband h94 h135

def residentBandControls : Pr P 151 Q A U :=
  .seq residentBandWidth (.seq (clippedBandControls 0 94 116 137 138 136 135)
    (.seq (uclear 94) (uclear 0)))

def residentBandControlsCost (n band rowCount : ℕ) : ℕ :=
  (4*band+5)+(clippedBandControlsCost n (12*band+1) rowCount+
    ((2*(12*band+1)+2)+(2*n+2)))

theorem residentBandControls_exec (n band rowCount : ℕ) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hn : (S.R 0).length = n) (hband : (S.R 124).length = band)
    (hrows : (S.R 116).length = rowCount)
    (hfresh : ∀ k ∈ [(94 : Fin 151),135,136,137,138], S.R k = []) :
    ∃ v', v'.user = v.user ∧ Exec body residentBandControls (mk v S)
      (residentBandControlsCost n band rowCount)
      (mk v' {S with R := (Function.update (Function.update (Function.update S.R 0 [])
        137 (List.replicate (n-(12*band+1)) tick))
        138 (List.replicate (min rowCount (n+(12*band+1)+1)-(n-(12*band+1))) tick))}) := by
  simpa only [residentBandControls,scaledBandControls,residentBandWidth,scaledBandWidth,
    residentBandControlsCost,scaledBandControlsCost] using
    scaledBandControls_exec (body := body) 12 n band rowCount v S hn hband hrows hfresh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
