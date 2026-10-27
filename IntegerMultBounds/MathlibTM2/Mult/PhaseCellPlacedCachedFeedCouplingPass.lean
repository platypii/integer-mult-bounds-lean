module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedBorrowedCouplingPassSpec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingResultFeed

/-! The computed residual/recovery line feeds the next raw-input solve while
retaining both source lines and restoring the previous output suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

noncomputable def placedCachedFeedCouplingPass (recovery : Bool) (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 256 Q A U :=
  .seq (placedCachedBorrowedCouplingPass recovery hQ boundary) placedCouplingResultFeed

def placedCachedFeedCouplingPassCost (boundary : Bool) (q w s t band a b Nwords : ℕ) : ℕ :=
  placedCachedBorrowedCouplingPassCost boundary q w s t band a b Nwords+12*s*w+9*s+12

theorem placedCachedFeedCouplingPass_spec (recovery : Bool) (hQ : SS.states ≤ Q)
    {p q w s t u band a b rhsExp inputExp countExp : ℕ} [NeZero s] {α d : ℝ}
    (boundary : Bool) (hA : 96 ≤ A) (hp : 0 < p) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ w)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hband : band = PhaseCellBand.width p u)
    (C B : ZMod s → GaussianInt) (x b₀ : ZMod s → ℝ) (K ε rhsError : ℝ) (hε : 0 ≤ ε)
    (hcount : 2*band+1 ≤ 2^countExp)
    (hB : ∀ j, ‖value q (B j)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      |(value q (C j)).re-x j| ≤ ε)
    (hmass : ∀ i < s, (((couplingOffsets band).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u band i (i+δ) : ℝ)|)).sum ≤ K)
    (hBError : ∀ j, |(value q (B j)).re-b₀ j| ≤ rhsError)
    (tail sourceTail pageTail : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hready : CouplingReady (2^15*p) q w s t u band a b
      (cstream A w (chirpLine s B)++tail) (embStk groupReg (embStk couplingSourceReg S)))
    (hcache : CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail S)
    (hindex : S.R 107 = []) (hsource : S.R 132 = cstream A w (chirpLine s C)++sourceTail)
    (h143 : S.R 143 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    let ys := guardedCouplingRowWords (2^15*p) q t u band a b boundary C 0 (chirpLine s B)
    ∃ v' m, v'.user = v.user ∧ m ≤ placedCachedFeedCouplingPassCost boundary q w s t band a b
      (couplingCoefficientPage (2^15*p) q s t u band a b s).length ∧
      Exec body (placedCachedFeedCouplingPass recovery hQ boundary) (mk v S) m
        (mk v' {S with R := Function.update S.R 110 (cstream A w ys++S.R 110)}) ∧
      ys = chirpLine s (guardedCouplingRowField (2^15*p) q t u band a b boundary C B) ∧
      (cstream A w ys).length = s*w ∧
      (∀ j, ‖value q (guardedCouplingRowField (2^15*p) q t u band a b boundary C B j)‖ ≤
        (2 : ℝ)^couplingRowExponent rhsExp inputExp (8*p+1) countExp) ∧
      ∀ j < s, (boundary = true ∨ (j : ZMod s) ∈ haloBoundary s t band a b) → |(value q (decodeWord (((cstream A w ys++S.R 110).drop (j*w)).take w))).re-
        (b₀ (j : ZMod s)-SchurDominance.couple (realMatrix s t p u)
          (if boundary then haloBoundary s t band a b else haloInterior s t band a b) x (j : ZMod s))| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+rhsError+(2*band+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  dsimp only
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hfield,hlen,hnorm,herror⟩ := placedCachedBorrowedCouplingPass_spec (body := body)
    recovery hQ boundary hA hp hst hαu hθ hgap hbudget hw haS hbS hbandS hband C B x b₀ K ε rhsError hε
    hcount hB hC hx hmass hBError tail sourceTail pageTail v S hready hcache hindex hsource h143 h131 h134 h135
  let ys := guardedCouplingRowWords (2^15*p) q t u band a b boundary C 0 (chirpLine s B)
  let result := cstream A w ys
  let S₁ : Stacks 256 A := {S with R := Function.update S.R 113 (result++S.R 113)}
  have hs : (S.R 97).length = s := hready.axis
  have hwS : (S.R 94).length = w := hready.width
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := placedCouplingResultFeed_exec (body := body)
    s w result (S.R 113) v₁ S₁ (by simpa [S₁] using hs) (by simpa [S₁] using hwS)
    (by simp [S₁]) hlen (by simpa [S₁] using h131)
    (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_,hfield,hlen,hnorm,?_⟩
  · dsimp only [placedCachedFeedCouplingPassCost]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h : k = 113 <;> simp [S₁,h,result,ys,Function.update_apply]
  · intro j hj hobserved
    have hj' : j < ys.length := by simpa [ys] using hj
    have hh := herror j hj hobserved
    rw [cstream_word w ys (S.R 110) j hj']
    rw [cstream_word w ys (S.R 113) j hj'] at hh
    exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
