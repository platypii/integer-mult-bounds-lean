module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryRibbonMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskGatheredCouplingRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRibbonMaskSemantics

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast

def buildMaskedGatheredRibbon {P U : Type} {Q A : ℕ} (boundary : Bool) : Pr P 168 Q A U :=
  .seq (.seq loadRibbonMaskBank (ribbonMaskHost boundary)) maskGatheredCouplingRibbon

theorem buildMaskedGatheredRibbon_data_exec {P U : Type} {Q A V s t band a b origin N : ℕ} [NeZero s]
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
    (xs ys : List GaussianInt) (hxs : xs.length = N+2*band)
    (hdata : maskedLine (couplingRibbonFlags (s := s) boundary t band a b origin N) xs = ys)
    (w : ℕ) (tail : List (Fin (A+4))) (hA : 4 ≤ A)
    (hrows : (S.R 166).length = N+2*band) (hw : (S.R 94).length = w)
    (hsrc : S.R 160 = cstream A w xs++tail)
    (h158 : S.R 158 = []) (h108 : S.R 108 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (h135 : S.R 135 = []) (h167 : S.R 167 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72)+
        maskCouplingSourceCost (N+2*band) w ∧
      Exec body (buildMaskedGatheredRibbon boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 141
          (cstream A w ys++S.R 141))})
 := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := binaryRibbonMask_exec (body := body) boundary value hs ht hband ha hb hindex hcount
    hst haS hbS hbandS hfit hfitV hwide hbound v S hV hmeta hblank
  let flags := couplingRibbonFlags (s := s) boundary t band a b origin N
  have hflags : flags.length = N+2*band := by
    dsimp only [flags]
    rw [couplingRibbonFlags_eq_map boundary hst band a b origin N hbS hbandS hfit]
    simp
  have hlen : xs.length = flags.length := by rw [hflags]; exact hxs
  let B : Stacks 168 A := {S with R := (Function.update S.R 158
    (flags.map (fun flag => pairSym A flag flag)++S.R 158))}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := maskGatheredCouplingRibbon_exec (body := body) hA flags
    xs w hlen tail v₁ B
    (by simpa [B,hflags] using hrows) (by simpa [B] using hw)
    (by simpa [B] using hsrc) (by simp [B,h158])
    (by simpa [B] using h108) (by simpa [B] using h104) (by simpa [B] using h105)
    (by simpa [B] using h135) (by simpa [B] using h167) (by simpa [B] using h143)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · rw [hflags] at hm₂
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h1 : r = 158 <;> by_cases h2 : r = 141 <;>
      simp [B,flags,hdata,h1,h2,h158]


theorem buildMaskedGatheredRibbon_exec {P U : Type} {Q A V s t band a b origin N : ℕ} [NeZero s]
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
    (C : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4))) (hA : 4 ≤ A)
    (hrows : (S.R 166).length = N+2*band) (hw : (S.R 94).length = w)
    (hsrc : S.R 160 = cstream A w (rawCouplingRibbon band origin N C)++tail)
    (h158 : S.R 158 = []) (h108 : S.R 108 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (h135 : S.R 135 = []) (h167 : S.R 167 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72)+
        maskCouplingSourceCost (N+2*band) w ∧
      Exec body (buildMaskedGatheredRibbon boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 141
          (cstream A w (couplingSourceInterval boundary t band a b origin N C)++S.R 141))})
 := by
  have hxs := rawCouplingRibbon_length band origin N C hfit
  exact buildMaskedGatheredRibbon_data_exec (body := body) boundary value hs ht hband ha hb hindex hcount
    hst haS hbS hbandS hfit hfitV hwide hbound v S hV hmeta hblank
    (rawCouplingRibbon band origin N C) (couplingSourceInterval boundary t band a b origin N C)
    hxs (maskedLine_couplingRibbon boundary t band a b origin N C) w tail hA hrows hw hsrc
    h158 h108 h104 h105 h135 h167 h143

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
