module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildMaskedLocalRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedGatheredRibbon
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

def cachedPreparedLocalRibbon {P U : Type} {Q A : ℕ} (cache : Fin 168) : Pr P 168 Q A U :=
  .seq prepareLocalCouplingRibbon
    (.seq (cachedGatheredRibbon cache)
      (.seq (releaseFromDimensions 166 94 108 160 167 104 105) (uclear 166)))

theorem cachedPreparedLocalRibbon_exec {P U : Type} {Q A V s t band a b origin N : ℕ} [NeZero s]
    {body : P → Pr P 168 Q A U} (boundary : Bool) (cache : Fin 168)
    (hreg : [cache,158,0,1].Nodup) (hc141 : cache ≠ 141) (hc160 : cache ≠ 160) (hc166 : cache ≠ 166)
    (hst : s < t) (hbS : b ≤ s) (hbandS : band ≤ s) (hfit : origin+N ≤ s)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hcache : S.R cache = (couplingRibbonFlags (s := s) boundary t band a b origin N).map
      (fun flag => pairSym A flag flag))
    (hclean : ∀ k ∈ ([(0 : Fin 168),1,2,104,105,108,109,127,158,166]), S.R k = [])
    (hlocalOrigin : origin = a) (hlocalEnd : b = a+N) (hsep : N+band ≤ s)
    (C : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4))) (hA : 4 ≤ A)
    (hNV : N < 2^V) (h165 : S.R 165 = binSyms V N)
    (h100 : (S.R 100).length = band)
    (hw : (S.R 94).length = w)
    (hsrc : S.R 132 = cstream A w (packedInterval a N C)++tail)
    (h135 : S.R 135 = []) (h167 : S.R 167 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (16*N*w+21*N+14*band*w+13*band+11*V+46)+(cachedGatheredRibbonCost (N+2*band) w)+(12*((N+2*band)*w)+11*(N+2*band)+14) ∧
      Exec body (cachedPreparedLocalRibbon cache) (mk v S) m
        (mk v' {S with R := (Function.update S.R 141
          (cstream A w (couplingSourceInterval boundary t band a b origin N C)++S.R 141))})
 := by
  have h166 := hclean 166 (by simp)
  have h158 := hclean 158 (by simp)
  have h108 := hclean 108 (by simp)
  have h104 := hclean 104 (by simp)
  have h105 := hclean 105 (by simp)
  have hfitA : a+N ≤ s := by simpa only [hlocalOrigin] using hfit
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareLocalCouplingRibbon_exec (body := body) V N band w (by omega)
    (packedInterval a N C) (packedInterval_length C hfitA) tail v S h165 h100 hw hsrc hclean
  let B : Stacks 168 A := {S with R := (Function.update (Function.update S.R 160
    (cstream A w (localCouplingRibbon band a N C)++S.R 160)) 166 (List.replicate (N+2*band) tick))}
  let flags := couplingRibbonFlags (s := s) boundary t band a b origin N
  have hflags : flags.length = N+2*band := by
    dsimp only [flags]
    rw [couplingRibbonFlags_eq_map boundary hst band a b origin N hbS hbandS hfit]
    simp
  have hdata : maskedLine flags (localCouplingRibbon band a N C) =
      couplingSourceInterval boundary t band a b origin N C := by
    simpa only [flags,hlocalOrigin,hlocalEnd] using
      maskedLine_localCouplingRibbon boundary t band a N C hfitA hsep
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂,_⟩ := cachedGatheredRibbon_exec_within (body := body) cache hreg hc141 hA
    flags (localCouplingRibbon band a N C) w
    ((localCouplingRibbon_length C hfitA).trans hflags.symm) (S.R 160) v₁ B
    (by simpa [B,flags,hc160,hc166] using hcache)
    (by simp [B,hflags]) (by simpa [B] using hw) (by simp [B])
    (by simpa [B] using hclean 0 (by simp)) (by simpa [B] using hclean 1 (by simp))
    (by simpa [B] using h158) (by simpa [B] using h108) (by simpa [B] using h104)
    (by simpa [B] using h105) (by simpa [B] using h135) (by simpa [B] using h167) (by simpa [B] using h143)
  rw [hflags] at hm₂
  have he₂' := (he₂ 0).toExec
  rw [hdata] at he₂'
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
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by rw [hlen]) ?_⟩
  apply congrArg (mk v₄)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h160 : k = 160 <;> by_cases h166' : k = 166 <;> by_cases h141 : k = 141 <;>
    simp [F,D,B,h160,h166',h141,h166]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
