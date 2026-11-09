module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareSpatialCouplingSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunSpatialCouplingRowsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireSpatialCouplingSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace

/-! Generate the whole-line row clock, execute every coupling row and publish
in natural coordinate order, releasing the clock and current index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

@[irreducible] def spatialCouplingSourcePush (boundary : Bool) : ℕ :=
  mnProgPush (prepareSpatialCouplingSource (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary)

theorem prepareSpatialCouplingSource_native (boundary : Bool) :
    mnNativePushBound (spatialCouplingSourcePush (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary)
      (prepareSpatialCouplingSource (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary) := by
  have houter : WordCmd.NoCalls (outerCouplingSourceMask (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary) := by
    unfold outerCouplingSourceMask
    exact WordCmd.noCalls_of_native (embProg_native _ _ _ (WordCmd.empty_native _))
  unfold spatialCouplingSourcePush
  apply WordCmd.native_of_noCalls _ le_rfl
  simp [prepareSpatialCouplingSource, prepareMaskedCouplingSource, houter,
    maskCouplingSource, padCouplingSource, padPrefixInPlace, copyCountedLine,
    maskedTransferLine, maskedTransferWord, countedLoop, countedLoopBody, copySlice, unaryProduct, scanP, copyPrefix, discardPrefix,
    transfer, ucopy, umul, umulSym, usub, scanR, drainR, copyR, moveR, whileR, uclear,
    WordCmd.NoCalls]

theorem retireSpatialCouplingSource_native :
    mnNativePushBound 3 (retireSpatialCouplingSource (P := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [retireSpatialCouplingSource, retireCountedLine, unaryProduct, scanP,
    discardPrefix, transfer, transferAct, ucopy, umul, umulSym, scanR, drainR,
    popDo, keepIn, pushN, uclear, moveR, moveStep, whileR, peekR, popPush,
    mnNativePushBound, mnActPush]

def spatialCouplingRowsWorkspace (boundary : Bool) (K P q w s t u band a b : ℕ) : ℕ :=
  spatialCouplingSourcePush (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary*
    prepareSpatialCouplingSourceCost s t band a b w +
    (runSpatialCouplingRowsWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) K P q w s t u band a b +
      3*retireSpatialCouplingSourceCost s band w)

theorem spatialCouplingRows_exec_within (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail rhsTail : List (Fin (A+4))) (K : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) (embStk groupReg S))
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = []) (h135 : S.R 135 = [])
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ spatialCouplingGuardedRowsCost boundary P q w s t u band a b ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        spatialCouplingRowsWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary K P q w s t u band a b) 0
        (spatialCouplingRows hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail)
          113 (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareSpatialCouplingSource_exec (body := body)
    boundary (by omega) hst haS hbS hbandS C tail v S hready hindex h135 h143
  let F := fun j : ZMod s => if j ∈
    (if boundary then haloBoundary s t band a b else haloInterior s t band a b) then C j else 0
  let input := cstream A w (cyclicPaddedLine F band)
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 141 (input++S.R 141)}
  have hview : embStk groupReg S₁ = embStk groupReg S :=
    groupProject_updateR S 141 _ (by decide)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := runSpatialCouplingRows_exec_within (body := body) hQ boundary hA hw5 hqw
    hst haS hbS hP C rhs hlen (S.R 141) rhsTail (cstream A w (chirpLine s C)++tail) K hpush v₁ S₁
    (by rw [hview]; exact hready) (by simp [S₁,input,F])
    (by simpa [S₁] using hindex) (by simpa [S₁] using hrhs)
    (by simpa [S₁] using h143) (by simpa [S₁] using h135) hxs has
  let ys := guardedCouplingRowWords P q t u band a b boundary C 0 rhs
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update (Function.update S₁.R 93 rhsTail)
    113 (cstream A w ys++S₁.R 113))}
  have hs : (S.R 97).length = s := hready.axis
  have hb : (S.R 100).length = band := hready.bandwidth
  have hw : (S.R 94).length = w := hready.width
  have hf (k : Fin 117) (hk : k ∈ [(92 : Fin 117),96,102,104,105,106,108,109,115,116]) :
      S.R (groupReg k) = [] := hready.fresh k hk
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := retireSpatialCouplingSource_exec (body := body)
    s band w input (S.R 141) (by simp [input,cyclicPaddedLine]) v₂ S₂
    (by simpa [S₂,S₁] using hs) (by simpa [S₂,S₁] using hb) (by simpa [S₂,S₁] using hw)
    (by simp [S₂,S₁]) (by simpa [S₂,S₁,groupReg] using hf 116 (by simp))
    (by simpa [S₂,S₁,groupReg] using hf 108 (by simp))
    (by simpa [S₂,S₁,groupReg] using hf 104 (by simp))
    (by simpa [S₂,S₁,groupReg] using hf 105 (by simp))
  have ht₁ := mn_native_exec_within he₁ _ (prepareSpatialCouplingSource_native boundary) 0 _
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm₁) _)
  have ht₃ := mn_native_exec_within he₃ 3 retireSpatialCouplingSource_native 0 _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm₃) _)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add he₂ ht₃)
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),
    by dsimp only [spatialCouplingGuardedRowsCost]; omega,
    (ht.mono (by intro d z hz; dsimp only [spatialCouplingRowsWorkspace]; exact hz)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h93 : k = 93 <;> by_cases h113 : k = 113 <;> by_cases h141 : k = 141 <;>
    simp [S₂,S₁,h93,h113,h141,ys]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
