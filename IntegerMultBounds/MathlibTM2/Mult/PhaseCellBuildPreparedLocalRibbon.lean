module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildMaskedLocalRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareLocalCouplingRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease

/-! Build a masked local ribbon from the retained local result, then release
its unmasked padding and count. The source and every borrowed suffix survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Fast

def buildPreparedLocalRibbon {P U : Type} {Q A : ℕ} (boundary : Bool) : Pr P 168 Q A U :=
  .seq prepareLocalCouplingRibbon
    (.seq (buildMaskedGatheredRibbon boundary)
      (.seq (releaseFromDimensions 166 94 108 160 167 104 105) (uclear 166)))

theorem buildPreparedLocalRibbon_exec {P U : Type} {Q A V s t band a b origin N : ℕ} [NeZero s]
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
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (h127 : S.R 127 = []) (h109 : S.R 109 = []) (h100 : (S.R 100).length = band)
    (hw : (S.R 94).length = w)
    (hsrc : S.R 132 = cstream A w (packedInterval a N C)++tail)
    (h158 : S.R 158 = []) (h108 : S.R 108 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (h135 : S.R 135 = []) (h167 : S.R 167 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (16*N*w+21*N+14*band*w+13*band+11*V+46)+(152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72)+
        maskCouplingSourceCost (N+2*band) w)+(12*((N+2*band)*w)+11*(N+2*band)+14) ∧
      Exec body (buildPreparedLocalRibbon boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 141
          (cstream A w (couplingSourceInterval boundary t band a b origin N C)++S.R 141))})
 := by
  have hfitA : a+N ≤ s := by simpa only [hlocalOrigin] using hfit
  have hsmall (i : Fin 18) : S.R (ribbonTableReg (.v i)) = [] := hblank (.v i)
  have hclean : ∀ k ∈ [(0 : Fin 168),1,2,104,105,108,109,127,158,166], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsmall 0
    · exact hsmall 1
    · exact hsmall 2
    · exact h104
    · exact h105
    · exact h108
    · exact h109
    · exact h127
    · exact h158
    · exact h166
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareLocalCouplingRibbon_exec (body := body) V N band w (by omega)
    (packedInterval a N C) (packedInterval_length C hfitA) tail v S h165 h100 hw hsrc hclean
  let B : Stacks 168 A := {S with R := (Function.update (Function.update S.R 160
    (cstream A w (localCouplingRibbon band a N C)++S.R 160)) 166 (List.replicate (N+2*band) tick))}
  have hmoff (i : Fin 18) : ribbonMaskBankSource i ≠ 160 ∧ ribbonMaskBankSource i ≠ 166 := by
    simp only [ribbonMaskBankSource]; split_ifs <;> constructor <;> decide
  have hboff (r : TblR 18) : ribbonTableReg r ≠ 160 ∧ ribbonTableReg r ≠ 166 := by
    have hr := ribbonTableReg_range r
    constructor <;> intro he <;> have hv := congrArg (fun k : Fin 168 => k.val) he <;> norm_num at hv <;> omega
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := buildMaskedLocalRibbon_exec (body := body) boundary value
    hs ht hband ha hb hindex hcount hst haS hbS hbandS hfit hfitV hwide hbound v₁ B
    (by simpa [B] using hV)
    (by intro i; simpa only [B,Function.update_of_ne (hmoff i).1,Function.update_of_ne (hmoff i).2] using hmeta i)
    (by intro r; simpa only [B,Function.update_of_ne (hboff r).1,Function.update_of_ne (hboff r).2] using hblank r)
    hlocalOrigin hlocalEnd hsep C w (S.R 160) hA (by simp [B]) (by simpa [B] using hw) (by simp [B])
    (by simpa [B] using h158) (by simpa [B] using h108) (by simpa [B] using h104)
    (by simpa [B] using h105) (by simpa [B] using h135) (by simpa [B] using h167) (by simpa [B] using h143)
  let D : Stacks 168 A := {B with R := (Function.update B.R 141
    (cstream A w (couplingSourceInterval boundary t band a b origin N C)++B.R 141))}
  let raw := cstream A w (localCouplingRibbon band a N C)
  have hraw : raw.length = (N+2*band)*w := by simp [raw,localCouplingRibbon_length C hfitA]
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := releaseFromDimensions_exec (body := body)
    (a := 166) (b := 94) (count := 108) (src := 160) (saved := 167) (buf := 104) (tmp := 105)
    (by decide) v₂ D raw (S.R 160) (by simp [D,B,raw])
    (by simpa [D,B,hw] using hraw)
    (by simpa [D,B] using h108) (by simpa [D,B] using h167)
    (by simpa [D,B] using h104) (by simpa [D,B] using h105)
  let F : Stacks 168 A := {D with R := Function.update D.R 160 (S.R 160)}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 166 v₃ F
  have hlen : (F.R 166).length = N+2*band := by simp [F,D,B]
  have hm₃' : m₃ ≤ 12*((N+2*band)*w)+9*(N+2*band)+12 := by simpa [D,B,hraw] using hm₃
  refine ⟨v₄,m₁+(m₂+(m₃+(2*(N+2*band)+2))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),by omega,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [hlen]) ?_⟩
  apply congrArg (mk v₄)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h160 : k = 160 <;> by_cases h166' : k = 166 <;> by_cases h141 : k = 141 <;>
    simp [F,D,B,h160,h166',h141,h166]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
