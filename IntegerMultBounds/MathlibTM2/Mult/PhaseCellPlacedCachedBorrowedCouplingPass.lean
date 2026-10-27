module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedSpatialCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingLines
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageCouplingLines
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCouplingLine

/-! A restoring coupling pass from the original RHS and published solution lines. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

noncomputable def placedCachedBorrowedCouplingPass (recovery : Bool) (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 256 Q A U :=
  .seq placedCouplingLinesStage (.seq (placedCachedSpatialCouplingRows recovery hQ boundary) placedCouplingLineRetire)

def placedCachedBorrowedCouplingPassCost (boundary : Bool) (q w s t band a b Nwords : ℕ) : ℕ :=
  placedCachedSpatialCouplingRowsCost boundary q w s t band a b Nwords+38*s*w+18*s+38

theorem placedCachedBorrowedCouplingPass_exec (recovery : Bool) (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (C B : ZMod s → GaussianInt) (tail sourceTail pageTail : List (Fin (A+4)))
    (v : HS 256 Q A U) (S : Stacks 256 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s B)++tail) (embStk groupReg (embStk couplingSourceReg S)))
    (hcache : CouplingPageCacheReady recovery P q w s t u band a b pageTail S)
    (hsource : S.R 132 = cstream A w (chirpLine s C)++sourceTail)
    (hindex : S.R 107 = []) (h143 : S.R 143 = [])
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ placedCachedBorrowedCouplingPassCost boundary q w s t band a b
      (couplingCoefficientPage P q s t u band a b s).length ∧
      Exec body (placedCachedBorrowedCouplingPass recovery hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 113
          (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 (chirpLine s B))++S.R 113))}) := by
  have hs : (S.R 97).length = s := hready.axis
  have hwS : (S.R 94).length = w := hready.width
  have hrhs : S.R 110 = cstream A w (chirpLine s B)++tail := hready.source
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := placedCouplingLinesStage_exec (body := body)
    s w (cstream A w (chirpLine s B)) (cstream A w (chirpLine s C)) tail sourceTail v S hs hwS hrhs hsource
    (by simp) (by simp) h131 h134 h135
  let source := cstream A w (chirpLine s C)
  let rhs := cstream A w (chirpLine s B)
  let S₁ : Stacks 256 A := {S with R := (Function.update (Function.update S.R 93 (rhs++S.R 93))
    110 (source++S.R 110))}
  let e := couplingSourceReg
  have hready₁ : CouplingReady P q w s t u band a b
      (source++S.R 110) (embStk groupReg (embStk e S₁)) := by
    apply hready.of_source_frame (S' := embStk groupReg (embStk e S₁)) (raw' := source++S.R 110)
      (by change S₁.R 110 = _; simp [S₁]) rfl
    intro k h93 _ _ h110
    have hn93 : e (groupReg k) ≠ (93 : Fin 256) := by
      change e (groupReg k) ≠ e 93
      intro h
      have := couplingSourceReg_injective h
      exact h93 (by simpa [groupReg,Fin.ext_iff] using this)
    have hn110 : e (groupReg k) ≠ (110 : Fin 256) := by
      change e (groupReg k) ≠ e 110
      intro h
      have := couplingSourceReg_injective h
      exact h110 (by simpa [groupReg,Fin.ext_iff] using this)
    change S₁.R (e (groupReg k)) = S.R (e (groupReg k))
    simp [S₁,hn93,hn110]
  have hcache₁ : CouplingPageCacheReady recovery P q w s t u band a b pageTail S₁ := by
    apply hcache.of_frame
    intro i
    have hi := couplingCachePort_ge recovery i
    have hn93 : couplingCachePort recovery i ≠ (93 : Fin 256) := by
      intro h; have := congrArg Fin.val h; omega
    have hn110 : couplingCachePort recovery i ≠ (110 : Fin 256) := by
      intro h; have := congrArg Fin.val h; omega
    simp [S₁,hn93,hn110]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := placedCachedSpatialCouplingRows_exec (body := body)
    recovery hQ boundary hA hw5 hqw hst haS hbS hbandS C (chirpLine s B) (by simp)
    (S.R 110) pageTail (S.R 93) v₁ S₁ hready₁ hcache₁
    (by simpa [S₁] using hindex) (by simp [S₁,rhs]) (by simpa [S₁] using h143)
    (by simpa [S₁] using h135) hxs has
  let ys := guardedCouplingRowWords P q t u band a b boundary C 0 (chirpLine s B)
  let S₂ : Stacks 256 A := {S₁ with R := (Function.update (Function.update S₁.R 93 (S.R 93))
    113 (cstream A w ys++S₁.R 113))}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := placedCouplingLineRetire_exec (body := body)
    s w source (S.R 110) v₂ S₂ (by simpa [S₂,S₁] using hs) (by simpa [S₂,S₁] using hwS)
    (by simp [S₂,S₁]) (by simp [source]) (by simpa [S₂,S₁] using h131)
    (by simpa [S₂,S₁] using h134) (by simpa [S₂,S₁] using h135)
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · dsimp only [placedCachedBorrowedCouplingPassCost]
    nlinarith only [hm₁,hm₂,hm₃]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h93 : k = 93 <;>
      simp [S₂,S₁,h110,h93,ys,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
