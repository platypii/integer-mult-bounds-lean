module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildMaskedGatheredRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRibbonLength
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskGatheredCouplingRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRibbonMaskSemantics

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast

def prepareMaskedGatheredRibbon {P U : Type} {Q A : ℕ} (boundary : Bool) : Pr P 168 Q A U :=
  .seq prepareRibbonLength (.seq (buildMaskedGatheredRibbon boundary) (uclear 166))

theorem prepareMaskedGatheredRibbon_exec {P U : Type} {Q A V s t band a b origin N : ℕ} [NeZero s]
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
    (h166 : S.R 166 = [])
    (h165 : S.R 165 = binSyms V N) (h100 : (S.R 100).length = band) (h109 : S.R 109 = []) (hw : (S.R 94).length = w)
    (hsrc : S.R 160 = cstream A w (rawCouplingRibbon band origin N C)++tail)
    (h158 : S.R 158 = []) (h108 : S.R 108 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (h135 : S.R 135 = []) (h167 : S.R 167 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 8*N+8*band+11*V+12+(152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72)+
        maskCouplingSourceCost (N+2*band) w) ∧
      Exec body (prepareMaskedGatheredRibbon boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 141
          (cstream A w (couplingSourceInterval boundary t band a b origin N C)++S.R 141))})
 := by
  have hsmall (i : Fin 18) : S.R (ribbonTableReg (.v i)) = [] := hblank (.v i)
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareRibbonLength_exec (body := body) V N band (by omega) v S
    h165 h166 h100 h109 (hsmall 0) (hsmall 1) (hsmall 2)
  let B : Stacks 168 A := {S with R := Function.update S.R 166 (List.replicate (N+2*band) tick)}
  have hmf (i : Fin 18) : ribbonMaskBankSource i ≠ 166 := by
    simp only [ribbonMaskBankSource]; split_ifs <;> decide
  have hbf (r : TblR 18) : ribbonTableReg r ≠ 166 := by
    intro he
    have hr := ribbonTableReg_range r
    have hv := congrArg (fun k : Fin 168 => k.val) he
    norm_num at hv; omega
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := buildMaskedGatheredRibbon_exec (body := body) boundary value
    hs ht hband ha hb hindex hcount hst haS hbS hbandS hfit hfitV hwide hbound v₁ B
    (by simpa [B] using hV)
    (by intro i; simpa only [B,Function.update_of_ne (hmf i)] using hmeta i)
    (by intro r; simpa only [B,Function.update_of_ne (hbf r)] using hblank r)
    C w tail hA (by simp [B]) (by simpa [B] using hw) (by simpa [B] using hsrc)
    (by simpa [B] using h158) (by simpa [B] using h108) (by simpa [B] using h104)
    (by simpa [B] using h105) (by simpa [B] using h135) (by simpa [B] using h167)
    (by simpa [B] using h143)
  let F : Stacks 168 A := {B with R := (Function.update B.R 141
    (cstream A w (couplingSourceInterval boundary t band a b origin N C)++B.R 141))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 166 v₂ F
  have hlen : (F.R 166).length = N+2*band := by simp [F,B]
  refine ⟨v₃,m₁+(m₂+(2*(N+2*band)+2)),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hlen]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h1 : r = 166 <;> by_cases h2 : r = 141 <;> simp [F,B,h1,h2,h166]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
