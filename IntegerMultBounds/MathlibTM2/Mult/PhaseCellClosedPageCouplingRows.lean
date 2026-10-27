module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunCachedPageCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCouplingPageCache

/-! A closed setup/read/release pass: every retained coefficient and guard is generated and paid. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def closedPageCouplingRows (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq buildCouplingPageCache (.seq (runCachedPageCouplingRows hQ) releaseCouplingPageCache)

def closedPageCouplingRowsCost (boundary : Bool) (P q w s t u band a b : ℕ) : ℕ :=
  let N := (couplingCoefficientPage P q s t u band a b s).length
  buildCouplingPageCacheCost P q w s t u band a b+
    runCachedPageCouplingRowsCost boundary q w s t band a b N+releaseCouplingPageCacheCost s N (2*band+1) w

theorem closedPageCouplingRows_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hP : 13 ≤ P) (ha : a ≤ s) (hb : b ≤ s)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail rhsTail raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hsource : S.R 141 = cstream A w (cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band)++tail)
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h135 : S.R 135 = []) (h139 : S.R 139 = []) (h140 : S.R 140 = []) (h143 : S.R 143 = [])
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ closedPageCouplingRowsCost boundary P q w s t u band a b ∧
      Exec body (closedPageCouplingRows hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 113
          (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  let page := couplingCoefficientPage P q s t u band a b s
  let flags := couplingGuardSymbols true A s t band a b
  let ys := guardedCouplingRowWords P q t u band a b boundary C 0 rhs
  obtain ⟨vB,mB,huB,hmB,heB⟩ := buildCouplingPageCache_exec (body := body)
    (by omega) hst hP ha hb raw v S hready hindex h135 h139 h140 h143
  let B : Stacks 144 A := {S with R := (Function.update (Function.update (Function.update (Function.update S.R 138
    (cstream A w page++S.R 138)) 139 (List.replicate page.length tick)) 140 (List.replicate (2*band+1) tick)) 135 flags)}
  have hreadyB : CouplingReady P q w s t u band a b raw (embStk groupReg B) := by
    have hview : embStk groupReg B = embStk groupReg S := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      have h135k := groupReg_off 135 (by decide) k
      have h138 := groupReg_off 138 (by decide) k
      have h139k := groupReg_off 139 (by decide) k
      have h140k := groupReg_off 140 (by decide) k
      simp [B,embStk,Function.comp_def,h135k,h138,h139k,h140k]
    rw [hview]; exact hready
  obtain ⟨vR,mR,huR,hmR,heR⟩ := runCachedPageCouplingRows_exec (body := body)
    hQ boundary hA hw5 hqw hst C rhs hlen tail (S.R 138) rhsTail raw vB B hreadyB
    (by simpa [B] using hsource) (by simp [B,flags]) (by simpa [B] using hindex)
    (by simpa [B] using hrhs) (by simpa [B] using h143) (by simp [B])
    (by simp [B,page]) (by simp [B,page]) hxs has
  let R : Stacks 144 A := {B with R := (Function.update (Function.update B.R 93 rhsTail) 113 (cstream A w ys++S.R 113))}
  obtain ⟨vF,mF,huF,hmF,heF⟩ := releaseCouplingPageCache_exec (body := body)
    s w (2*band+1) page (S.R 138) vR R (by simp [R,B,flags]) (by simp [R,B])
    (by simp [R,B]) (by simpa [R,B,embStk,groupReg] using hready.width) (by simp [R,B])
    (by simpa [R,B,embStk,groupReg] using hready.fresh 109 (by simp))
    (by simpa [R,B,embStk,groupReg] using hready.fresh 104 (by simp))
    (by simpa [R,B,embStk,groupReg] using hready.fresh 105 (by simp))
  have heR' : Exec body (runCachedPageCouplingRows hQ) (mk vB B) mR (mk vR R) := by simpa [R,B,ys] using heR
  refine ⟨vF,mB+(mR+mF),huF.trans (huR.trans huB),?_,(Exec.seq heB (Exec.seq heR' heF)).cast rfl ?_⟩
  · dsimp only [closedPageCouplingRowsCost]
    dsimp only [page] at hmF
    omega
  · apply congrArg (mk vF)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h135k : k = 135
    · subst k; simp [R,B,h135]
    by_cases h138 : k = 138
    · subst k; simp [R,B]
    by_cases h139k : k = 139
    · subst k; simp [R,B,h139]
    by_cases h140k : k = 140
    · subst k; simp [R,B,h140]
    simp [R,B,h135k,h138,h139k,h140k,ys,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
