module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunCachedCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCaptureCouplingSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine

/-! Generate the whole-line row clock, execute every coupling row and publish
in natural coordinate order, releasing the clock and current index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def cachedCouplingCaptureReg (i : Fin 117) : Fin 144 :=
  cachedCouplingOuterReg (cachedCouplingLookupReg i)

theorem cachedCouplingCaptureReg_injective : Function.Injective cachedCouplingCaptureReg :=
  cachedCouplingOuterReg_injective.comp cachedCouplingLookupReg_injective

noncomputable def capturedCouplingRows (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 144 Q A U :=
  .seq (embProg cachedCouplingCaptureReg Empty.elim (captureCouplingSource (P₀ := Empty)))
    (.seq (runCachedCouplingRows hQ boundary) (retireCountedLine 97 94 141 109 104 105))

def capturedCouplingRowsCost (P q w s t u band a b : ℕ) : ℕ :=
  runCachedCouplingRowsCost P q w s t u band a b+s*(28*w+18)+28

theorem capturedCouplingRows_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail rhsTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) (embStk cachedCouplingCoreReg (embStk cachedCouplingOuterReg S)))
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = []) (h135 : S.R 135 = [])
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ capturedCouplingRowsCost P q w s t u band a b ∧
      Exec (body) (capturedCouplingRows hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail)
          113 (cstream A w (couplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  let input := cstream A w (chirpLine s C)
  let T := embStk cachedCouplingCaptureReg S
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀⟩ := captureCouplingSource_prefix_exec
    (body := fun p : Empty => nomatch p) s w input tail (embDn cachedCouplingCaptureReg v) T
    hready.axis hready.width hready.source (by simp [input,chirpLine])
    (hready.fresh 109 (by simp)) (hready.fresh 104 (by simp)) (hready.fresh 105 (by simp))
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    cachedCouplingCaptureReg_injective (fun p => nomatch p) he₀ v rfl S rfl
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 141 (input++S.R 141)}
  have he₁' : Exec body
      (embProg cachedCouplingCaptureReg Empty.elim (captureCouplingSource (P₀ := Empty)))
      (mk v S) n₀ (mk v₁ S₁) := by
    convert he₁ using 1
    apply congrArg (mk v₁)
    rw [embOvr_updR cachedCouplingCaptureReg_injective,embOvr_stk]
    rfl
  have hview : embStk cachedCouplingCoreReg (embStk cachedCouplingOuterReg S₁) =
      embStk cachedCouplingCoreReg (embStk cachedCouplingOuterReg S) := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    have hn : cachedCouplingOuterReg (cachedCouplingCoreReg i) ≠ 141 := by
      simp [cachedCouplingOuterReg,cachedCouplingCoreReg,i.isLt,Fin.ext_iff]
      omega
    exact Function.update_of_ne hn _ _
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := runCachedCouplingRows_exec (body := body) hQ boundary hA hw5 hqw
    hst haS hbS hbandS hP C rhs hlen tail rhsTail v₁ S₁ (by rw [hview]; exact hready)
    (by exact ⟨S.R 141,by simp [S₁,input]⟩) (by simpa [S₁] using hindex) (by simpa [S₁] using hrhs)
    (by simpa [S₁] using h143) (by simpa [S₁] using h135) hxs has
  let ys := couplingRowWords P q t u band a b boundary C 0 rhs
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update (Function.update S₁.R 93 rhsTail)
    113 (cstream A w ys++S₁.R 113))}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := retireCountedLine_exec (body := body)
    97 94 141 109 104 105 (by decide) s w input (S.R 141)
    (by simp [input,chirpLine]) v₂ S₂
    (by have hh : (S.R 97).length = s := hready.axis; simpa [S₂,S₁] using hh)
    (by have hh : (S.R 94).length = w := hready.width; simpa [S₂,S₁] using hh)
    (by simp [S₂,S₁])
    (by simpa [S₂,S₁,embStk,cachedCouplingOuterReg,cachedCouplingCoreReg] using hready.fresh 109 (by simp))
    (by simpa [S₂,S₁,embStk,cachedCouplingOuterReg,cachedCouplingCoreReg] using hready.fresh 104 (by simp))
    (by simpa [S₂,S₁,embStk,cachedCouplingOuterReg,cachedCouplingCoreReg] using hready.fresh 105 (by simp))
  refine ⟨v₃,n₀+(n₂+n₃),hu₃.trans (hu₂.trans (hu₁.trans hu₀)),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · dsimp only [capturedCouplingRowsCost]
    dsimp only [retireCountedLineCost] at hn₃
    nlinarith only [hn₀,hn₂,hn₃]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h93 : i = 93 <;> by_cases h113 : i = 113 <;> by_cases h144' : i = 141 <;>
      simp [S₂,S₁,h93,h113,h144',ys]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
