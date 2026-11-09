module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFeedCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBorrowedCouplingPassSpecStock

/-! Feeding the computed residual preserves the borrowed pass's shared row reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem feedCouplingResult_native :
    mnNativePushBound 3 (feedCouplingResult (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [feedCouplingResult,unaryProduct,ucopy,umulSym,takePrefix,transfer,transferAct,
    scanP,scanR,drainR,popDo,keepIn,pushN,popPush,uclear,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

@[irreducible] def feedCouplingPassWorkspace (boundary : Bool) (rowPush P q w s t u band a b : ℕ) : ℕ :=
  borrowedCouplingPassWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary rowPush P q w s t u band a b+
    3*(12*s*w+9*s+12)

theorem feedCouplingPass_spec_within (hQ : SS.states ≤ Q)
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
    (tail sourceTail : List (Fin (A+4))) (rowPush : ℕ)
    (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ rowPush)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady (2^15*p) q w s t u band a b
      (cstream A w (chirpLine s B)++tail) (embStk groupReg S))
    (hindex : S.R 107 = []) (hsource : S.R 132 = cstream A w (chirpLine s C)++sourceTail)
    (h143 : S.R 143 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    let ys := guardedCouplingRowWords (2^15*p) q t u band a b boundary C 0 (chirpLine s B)
    ∃ v' m, v'.user = v.user ∧ m ≤ feedCouplingPassCost boundary (2^15*p) q w s t u band a b ∧
      ExecWithin (embTab groupReg body)
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          feedCouplingPassWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary rowPush (2^15*p) q w s t u band a b)
        0 (feedCouplingPass hQ boundary) (mk v S) m
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
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hfield,hlen,hnorm,herror⟩ := borrowedCouplingPass_spec_within (body := body)
    hQ boundary hA hp hst hαu hθ hgap hbudget hw haS hbS hbandS hband C B x b₀ K ε rhsError hε
    hcount hB hC hx hmass hBError tail sourceTail rowPush hpush v S hready hindex hsource h143 h131 h134 h135
  let ys := guardedCouplingRowWords (2^15*p) q t u band a b boundary C 0 (chirpLine s B)
  let result := cstream A w ys
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 113 (result++S.R 113)}
  have hs : (S.R 97).length = s := hready.axis
  have hwS : (S.R 94).length = w := hready.width
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := feedCouplingResult_exec (body := embTab groupReg body)
    s w result (S.R 113) v₁ S₁ (by simpa [S₁] using hs) (by simpa [S₁] using hwS)
    (by simp [S₁]) hlen (by simpa [S₁] using h131)
    (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  have ht₂ := mn_native_exec_within he₂ 3 feedCouplingResult_native 0
    (mnSize (mk v₁ S₁)+0+3*(12*s*w+9*s+12)) (by omega)
  have ht := (mn_seq_within_add he₁ ht₂).mono (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
      feedCouplingPassWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary rowPush (2^15*p) q w s t u band a b) (by
    intro d z hz
    unfold feedCouplingPassWorkspace
    exact hz)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,ht.cast rfl ?_,hfield,hlen,hnorm,?_⟩
  · dsimp only [feedCouplingPassCost]
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
