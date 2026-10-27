module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingSource

/-! Prepare, read and retire a spatial source while retaining both disjoint coefficient keys. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

noncomputable def placedCachedSpatialCouplingRows (recovery : Bool) (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 256 Q A U :=
  .seq (placedCouplingSourcePrepare boundary)
    (.seq (placedCouplingCacheRead recovery hQ) placedCouplingSourceRetire)

def placedCachedSpatialCouplingRowsCost (boundary : Bool) (q w s t band a b Nwords : ℕ) : ℕ :=
  prepareSpatialCouplingSourceCost s t band a b w+runCachedPageCouplingRowsCost boundary q w s t band a b Nwords+
    retireSpatialCouplingSourceCost s band w

theorem placedCachedSpatialCouplingRows_exec (recovery : Bool) (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail pageTail rhsTail : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) (embStk groupReg (embStk couplingSourceReg S)))
    (hcache : CouplingPageCacheReady recovery P q w s t u band a b pageTail S)
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = []) (h135 : S.R 135 = [])
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ placedCachedSpatialCouplingRowsCost boundary q w s t band a b
      (couplingCoefficientPage P q s t u band a b s).length ∧
      Exec body (placedCachedSpatialCouplingRows recovery hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail)
          113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  let e := couplingSourceReg
  let T := embStk e S
  have hindexT : T.R 107 = [] := hindex
  have h135T : T.R 135 = [] := h135
  have h143T : T.R 143 = [] := h143
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := placedCouplingSourcePrepare_exec (body := body)
    boundary (by omega) hst haS hbS hbandS C tail v S hready hindexT h135T h143T
  let F := fun j : ZMod s => if j ∈
    (if boundary then haloBoundary s t band a b else haloInterior s t band a b) then C j else 0
  let input := cstream A w (cyclicPaddedLine F band)
  let S₁ : Stacks 256 A := {S with R := Function.update S.R 141 (input++S.R 141)}
  have hproj : embStk e S₁ = {T with R := Function.update T.R 141 (input++S.R 141)} :=
    embStk_updateR_inner e couplingSourceReg_injective S 141 _
  have hview : embStk groupReg (embStk e S₁) = embStk groupReg T := by
    rw [hproj]; exact groupProject_updateR T 141 _ (by decide)
  have hcache₁ : CouplingPageCacheReady recovery P q w s t u band a b pageTail S₁ := by
    apply hcache.of_frame
    intro i
    have hi := couplingCachePort_ge recovery i
    have hne : couplingCachePort recovery i ≠ (141 : Fin 256) := by
      intro h; have := congrArg Fin.val h; omega
    simp [S₁,hne]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂,hcache₂⟩ := placedCouplingCacheRead_exec (body := body)
    hQ recovery boundary hA hw5 hqw hst C rhs hlen (S.R 141) pageTail rhsTail
    (cstream A w (chirpLine s C)++tail) v₁ S₁ hcache₁
    (by change CouplingReady _ _ _ _ _ _ _ _ _ _ (embStk groupReg (embStk e S₁)); rw [hview]; exact hready)
    (by change S₁.R 141 = _; simp [S₁,input,F])
    (by change S₁.R 107 = []; simpa [S₁] using hindex)
    (by simpa [S₁] using hrhs)
    (by change S₁.R 143 = []; simpa [S₁] using h143) hxs has
  let ys := guardedCouplingRowWords P q t u band a b boundary C 0 rhs
  let S₂ : Stacks 256 A := {S₁ with R := (Function.update (Function.update S₁.R 93 rhsTail)
    113 (cstream A w ys++S₁.R 113))}
  have hproj₂ : embStk e S₂ = {embStk e S₁ with R :=
      (Function.update (Function.update (embStk e S₁).R 93 rhsTail)
        113 (cstream A w ys++S₁.R 113))} := by
    let D : Stacks 256 A := {S₁ with R := Function.update S₁.R (e 93) rhsTail}
    change embStk e {D with R := Function.update D.R (e 113) (cstream A w ys++S₁.R 113)} = _
    rw [embStk_updateR_inner e couplingSourceReg_injective]
    dsimp only [D]
    rw [embStk_updateR_inner e couplingSourceReg_injective]
  have hs : (T.R 97).length = s := hready.axis
  have hb : (T.R 100).length = band := hready.bandwidth
  have hw : (T.R 94).length = w := hready.width
  have hf (k : Fin 117) (hk : k ∈ [(92 : Fin 117),96,102,104,105,106,108,109,115,116]) :
      T.R (groupReg k) = [] := hready.fresh k hk
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := placedCouplingSourceRetire_exec (body := body)
    s band w input (S.R 141) (by simp [input,cyclicPaddedLine]) v₂ S₂
    (by simpa [e,hproj₂,hproj] using hs)
    (by simpa [e,hproj₂,hproj] using hb)
    (by simpa [e,hproj₂,hproj] using hw)
    (by simp [S₂,S₁])
    (by simpa [e,hproj₂,hproj,groupReg] using hf 116 (by simp))
    (by simpa [e,hproj₂,hproj,groupReg] using hf 108 (by simp))
    (by simpa [e,hproj₂,hproj,groupReg] using hf 104 (by simp))
    (by simpa [e,hproj₂,hproj,groupReg] using hf 105 (by simp))
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),
    by dsimp only [placedCachedSpatialCouplingRowsCost]; omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h93 : k = 93 <;> by_cases h113 : k = 113 <;> by_cases h141 : k = 141 <;>
    simp [S₂,S₁,h93,h113,h141,ys]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
