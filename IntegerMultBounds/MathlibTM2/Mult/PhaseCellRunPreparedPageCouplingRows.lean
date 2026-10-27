module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPageSpatialCouplingRowLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversePrefixInPlace

/-! Generate the whole-line row clock, execute every coupling row and publish
in natural coordinate order, releasing the clock and current index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def runPreparedPageCouplingRows (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (ucopy 97 143 104) (.seq (pageSpatialCouplingRowLoop hQ)
    (.seq restoreCouplingCoefficientPage (.seq restoreSpatialCouplingCursor
      (.seq (reversePrefixInPlace 97 104 94 113 115 105 106 108 109) (uclear 107)))))

def runPreparedPageCouplingRowsCost (boundary : Bool) (q w s t band a b Nwords : ℕ) : ℕ :=
  pageSpatialGuardedLoopCost boundary q w s t band a b s+32*s*w+34*s+28+
    transferCountedLineCost s w+transferCountedLineCost Nwords w

theorem runPreparedPageCouplingRows_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail pageTail maskTail rhsTail raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hsource : S.R 141 = cstream A w (cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band)++tail)
    (hmask : S.R 136 = couplingGuardSymbols boundary A s t band a b++maskTail)
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = [])
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPage P q s t u band a b s)++pageTail)
    (hwordCount : (S.R 139).length = (couplingCoefficientPage P q s t u band a b s).length)
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ runPreparedPageCouplingRowsCost boundary q w s t band a b
      (couplingCoefficientPage P q s t u band a b s).length ∧
      Exec (body) (runPreparedPageCouplingRows hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 136 maskTail) 93 rhsTail)
          113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  have hs : (S.R 97).length = s := hready.axis
  have hwS : (S.R 94).length = w := hready.width
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body)
    (show (97 : Fin 144) ≠ 143 by decide) (show (97 : Fin 144) ≠ 104 by decide)
    (show (143 : Fin 144) ≠ 104 by decide) v S (hready.fresh 104 (by simp))
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 143 (List.replicate s tick)}
  have he₁' : Exec (body) (ucopy 97 143 104) (mk v S) (4*s+4) (mk v₁ S₁) := by
    simpa [S₁,hs,h143] using he₁
  have hready₁ : CouplingReady P q w s t u band a b raw (embStk groupReg S₁) := by
    rw [show embStk groupReg S₁ = embStk groupReg S from groupProject_updateR S 143 _ (by decide)]
    exact hready
  have htake : (couplingGuardSymbols boundary A s t band a b).take s = couplingGuardSymbols boundary A s t band a b :=
    List.take_of_length_le (by simp)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := pageSpatialCouplingRowLoop_exec (body := body) hQ boundary hA hw5 hqw
    hst C rhs (by omega) tail pageTail maskTail rhsTail raw v₁ S₁ hready₁
    (by simpa [S₁] using hsource) (by simpa [S₁] using hrows) (by simpa [S₁,hlen] using hpage) (by simpa [S₁,hlen,htake] using hmask) (by simpa [S₁] using hindex)
    (by simpa [S₁] using hrhs) (by simp [S₁,hlen])
    (by simpa only [hlen] using hxs) (by simpa only [hlen] using has)
  let F := fun j : ZMod s => if j ∈
    (if boundary then haloBoundary s t band a b else haloInterior s t band a b) then C j else 0
  let source := cyclicPaddedLine F band
  let ys := guardedCouplingRowWords P q t u band a b boundary C 0 rhs
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update S₁.R 136 maskTail) 138 pageTail) 137
    ((cstream A w (couplingCoefficientPage P q s t u band a b s)).reverse++S.R 137))
    93 rhsTail) 107 (List.replicate s tick)) 113 (cstream A w ys.reverse++S₁.R 113)) 143 [])
    141 (cstream A w (source.drop s)++tail))
    142 ((cstream A w (source.take s)).reverse++S.R 142))}
  have he₂' : Exec (body) (pageSpatialCouplingRowLoop hQ) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,ys,hlen,S₁,hindex,source,F] using he₂
  let page := couplingCoefficientPage P q s t u band a b s
  obtain ⟨vC,mC,huC,hmC,heC⟩ := restoreCouplingCoefficientPage_exec (body := body)
    w page (S.R 137) v₂ S₂ (by simpa [S₂,S₁,page] using hwordCount)
    (by simpa [S₂,S₁] using hwS) (by simp [S₂,page])
    (by simpa [S₂,S₁] using (show S.R 109 = [] from hready.fresh 109 (by simp)))
    (by simpa [S₂,S₁] using (show S.R 104 = [] from hready.fresh 104 (by simp)))
    (by simpa [S₂,S₁] using (show S.R 105 = [] from hready.fresh 105 (by simp)))
  let SC : Stacks 144 A := {S₂ with R := (Function.update (Function.update S₂.R 137 (S.R 137)) 138 (S.R 138))}
  have heC' : Exec body restoreCouplingCoefficientPage (mk v₂ S₂) mC (mk vC SC) := by
    simpa [SC,S₂,page,hpage] using heC
  obtain ⟨vR,mR,huR,hmR,heR⟩ := restoreSpatialCouplingCursor_at (body := body) F band s w (by omega)
    tail (S.R 142) vC SC (by simp [SC,S₂]) (by simpa [SC,S₂,S₁] using hwS)
    (by simp [SC,S₂,source]) (by simp [SC,S₂,source])
    (by simpa [SC,S₂,S₁] using (show S.R 109 = [] from hready.fresh 109 (by simp)))
    (by simpa [SC,S₂,S₁] using (show S.R 104 = [] from hready.fresh 104 (by simp)))
    (by simpa [SC,S₂,S₁] using (show S.R 105 = [] from hready.fresh 105 (by simp)))
  let SR : Stacks 144 A := {SC with R := (Function.update (Function.update SC.R 142 (S.R 142))
    141 (cstream A w source++tail))}
  have hys : ys.length = s := by simp [ys,hlen]
  have hfresh : ∀ k ∈ [(104 : Fin 144),115,105,106,108,109], SR.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | simpa [SR,SC,S₂,S₁,embStk,groupReg] using hready.fresh 104 (by simp)
    | simpa [SR,SC,S₂,S₁,embStk,groupReg] using hready.fresh 115 (by simp)
    | simpa [SR,SC,S₂,S₁,embStk,groupReg] using hready.fresh 105 (by simp)
    | simpa [SR,SC,S₂,S₁,embStk,groupReg] using hready.fresh 106 (by simp)
    | simpa [SR,SC,S₂,S₁,embStk,groupReg] using hready.fresh 108 (by simp)
    | simpa [SR,SC,S₂,S₁,embStk,groupReg] using hready.fresh 109 (by simp)
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := reversePrefixInPlace_exec (body := body)
    (records := 97) (recordSaved := 104) (width := 94) (src := 113) (dst := 115)
    (saved := 105) (buf := 106) (tmp := 108) (count := 109) (by decide)
    w ys.reverse (S.R 113) vR SR
    (by simp [SR,SC,S₂,S₁,hs,hys]) (by simpa [SR,SC,S₂,S₁] using hwS) (by simp [SR,SC,S₂,S₁]) hfresh
  let S₃ : Stacks 144 A := {SR with R := Function.update SR.R 113 (cstream A w ys++S.R 113)}
  have he₃' : Exec (body) (reversePrefixInPlace 97 104 94 113 115 105 106 108 109)
      (mk vR SR) m₃ (mk v₃ S₃) := by simpa [S₃] using he₃
  have h107₃ : S₃.R 107 = List.replicate s tick := by simp [S₃,SR,SC,S₂]
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 107 v₃ S₃
  refine ⟨v₄,(4*s+4)+(m₂+(mC+(mR+(m₃+(2*s+2))))),hu₄.trans (hu₃.trans (huR.trans (huC.trans (hu₂.trans hu₁)))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq heC' (Exec.seq heR (Exec.seq he₃' he₄))))).cast (by rw [h107₃]; simp) ?_⟩
  · have hm₂g : m₂ ≤ pageSpatialGuardedLoopCost boundary q w s t band a b s := by simpa [hlen] using hm₂
    have hm₃' : m₃ ≤ 32*s*w+28*s+22 := by simpa [hys] using hm₃
    dsimp only [runPreparedPageCouplingRowsCost]
    dsimp only [page] at hmC
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h107 : k = 107
    · subst k; simp [S₃,SR,SC,S₂,S₁,hindex]
    by_cases h143' : k = 143
    · subst k; simp [S₃,SR,SC,S₂,S₁,h143]
    by_cases h113 : k = 113
    · subst k; simp [S₃,SR,SC,S₂,S₁,ys]
    by_cases h136 : k = 136
    · subst k; simp [S₃,SR,SC,S₂,S₁]
    by_cases h137 : k = 137
    · subst k; simp [S₃,SR,SC,S₂,S₁]
    by_cases h138 : k = 138
    · subst k; simp [S₃,SR,SC,S₂,S₁]
    by_cases h141 : k = 141
    · subst k; simp [S₃,SR,SC,S₂,S₁,← hsource,source,F]
    by_cases h142 : k = 142
    · subst k; simp [S₃,SR,SC,S₂,S₁]
    simp [S₃,SR,SC,S₂,S₁,h107,h143',h113,h136,h137,h138,h141,h142,ys,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
