module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildMaskedGatheredRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalCouplingRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellZeroPadLocalPrefix

/-! The existing generated mask machine accepts a zero-padded local payload.
No ambient cyclic source tape is part of this local execution contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Fast

theorem buildMaskedLocalRibbon_exec {P U : Type} {Q A V s t band a b origin N : ℕ} [NeZero s]
    {body : P → Pr P 168 Q A U} (boundary : Bool) (value : Fin 168 → ℕ)
    (hs : value 145 = s) (ht : value 146 = t) (hband : value 147 = band)
    (ha : value 149 = a) (hb : value 151 = b) (hindex : value 155 = origin)
    (hcount : value 164 = origin+(N+2*band))
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hfit : origin+N ≤ s)
    (hfitV : origin+(N+2*band)+s < 2^V) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (ribbonMaskBankSource i) < 2^V) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hV : (S.R 163).length = V)
    (hmeta : ∀ i, S.R (ribbonMaskBankSource i) = binSyms V (value (ribbonMaskBankSource i)))
    (hblank : ∀ r, S.R (ribbonTableReg r) = [])
    (hlocalOrigin : origin = a) (hlocalEnd : b = a+N) (hsep : N+band ≤ s)
    (C : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4))) (hA : 4 ≤ A)
    (hrows : (S.R 166).length = N+2*band) (hw : (S.R 94).length = w)
    (hsrc : S.R 160 = cstream A w (localCouplingRibbon band a N C)++tail)
    (h158 : S.R 158 = []) (h108 : S.R 108 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (h135 : S.R 135 = []) (h167 : S.R 167 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72)+
        maskCouplingSourceCost (N+2*band) w ∧
      Exec body (buildMaskedGatheredRibbon boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 141
          (cstream A w (couplingSourceInterval boundary t band a b origin N C)++S.R 141))})
 := by
  have hfitA : a+N ≤ s := by simpa only [hlocalOrigin] using hfit
  exact buildMaskedGatheredRibbon_data_exec (body := body) boundary value hs ht hband ha hb hindex hcount
    hst haS hbS hbandS hfit hfitV hwide hbound v S hV hmeta hblank
    (localCouplingRibbon band a N C) (couplingSourceInterval boundary t band a b origin N C)
    (localCouplingRibbon_length C hfitA)
    (by simpa only [hlocalOrigin,hlocalEnd] using maskedLine_localCouplingRibbon boundary t band a N C hfitA hsep)
    w tail hA hrows hw hsrc h158 h108 h104 h105 h135 h167 h143

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
