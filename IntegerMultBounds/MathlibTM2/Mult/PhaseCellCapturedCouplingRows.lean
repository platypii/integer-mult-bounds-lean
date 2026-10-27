module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunCachedCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCaptureCouplingSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunCouplingRows

/-! Generate the whole-line row clock, execute every coupling row and publish
in natural coordinate order, releasing the clock and current index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 145 Q A U}

def cachedCouplingCaptureReg (i : Fin 117) : Fin 145 :=
  cachedCouplingOuterReg (cachedCouplingLookupReg i)

theorem cachedCouplingCaptureReg_injective : Function.Injective cachedCouplingCaptureReg :=
  cachedCouplingOuterReg_injective.comp cachedCouplingLookupReg_injective

noncomputable def capturedCouplingRows (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 145 Q A U :=
  .seq (embProg cachedCouplingCaptureReg Empty.elim (captureCouplingSource (P₀ := Empty)))
    (.seq (runCachedCouplingRows hQ boundary) (uclear 144))

def capturedCouplingRowsCost (P q w s t u band a b : ℕ) : ℕ :=
  runCachedCouplingRowsCost P q w s t u band a b+18*s*w+9*s+18

theorem capturedCouplingRows_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail rhsTail : List (Fin (A+4))) (v : HS 145 Q A U) (S : Stacks 145 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) (embStk cachedCouplingCoreReg (embStk cachedCouplingOuterReg S)))
    (h144 : S.R 144 = [])
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
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀⟩ := captureCouplingSource_exec
    (body := fun p : Empty => nomatch p) s w input tail (embDn cachedCouplingCaptureReg v) T
    hready.axis hready.width hready.source (by simp [input,chirpLine]) h144
    (hready.fresh 109 (by simp)) (hready.fresh 104 (by simp)) (hready.fresh 105 (by simp))
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    cachedCouplingCaptureReg_injective (fun p => nomatch p) he₀ v rfl S rfl
  let S₁ : Stacks 145 A := {S with R := Function.update S.R 144 input}
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
    have hn : cachedCouplingOuterReg (cachedCouplingCoreReg i) ≠ 144 := by
      simp [cachedCouplingOuterReg,cachedCouplingCoreReg,i.isLt,Fin.ext_iff]
      omega
    exact Function.update_of_ne hn _ _
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := runCachedCouplingRows_exec (body := body) hQ boundary hA hw5 hqw
    hst haS hbS hbandS hP C rhs hlen tail rhsTail v₁ S₁ (by rw [hview]; exact hready)
    (by exact ⟨[],by simp [S₁,input]⟩) (by simpa [S₁] using hindex) (by simpa [S₁] using hrhs)
    (by simpa [S₁] using h143) (by simpa [S₁] using h135) hxs has
  let ys := couplingRowWords P q t u band a b boundary C 0 rhs
  let S₂ : Stacks 145 A := {S₁ with R := (Function.update (Function.update S₁.R 93 rhsTail)
    113 (cstream A w ys++S₁.R 113))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 144 v₂ S₂
  have hcacheLen : (S₂.R 144).length = s*w := by simp [S₂,S₁,input,chirpLine]
  have he₃' : Exec body (uclear 144) (mk v₂ S₂) (2*(s*w)+2)
      (mk v₃ {S₂ with R := Function.update S₂.R 144 []}) := by simpa only [hcacheLen] using he₃
  refine ⟨v₃,n₀+(n₂+(2*(s*w)+2)),hu₃.trans (hu₂.trans (hu₁.trans hu₀)),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃')).cast rfl ?_⟩
  · dsimp only [capturedCouplingRowsCost]
    nlinarith only [hn₀,hn₂]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h93 : i = 93 <;> by_cases h113 : i = 113 <;> by_cases h144' : i = 144 <;>
      simp [S₂,S₁,h93,h113,h144',h144,ys]

theorem cachedCouplingRowLoopCost_saving (P q w s t u band a b i N : ℕ) :
    couplingRowLoopCost P q w s t u band a b i N =
      cachedCouplingRowLoopCost P q w s t u band a b i N+N*(18*s*w+9*s+18) := by
  have hrow (j : ℕ) : couplingRowStepCost P q w s t u band a b j =
      cachedCouplingRowStepCost P q w s t u band a b j+(18*s*w+9*s+18) := by
    dsimp only [couplingRowStepCost,cachedCouplingRowStepCost]
    rw [cachedCouplingRowCost_saving]
    ring
  have hsum :
      (Finset.range N).sum (fun j => couplingRowStepCost P q w s t u band a b (i+j)+3) =
      (Finset.range N).sum (fun j => cachedCouplingRowStepCost P q w s t u band a b (i+j)+3)+
        N*(18*s*w+9*s+18) := by
    calc
      _ = (Finset.range N).sum (fun j =>
          (cachedCouplingRowStepCost P q w s t u band a b (i+j)+3)+(18*s*w+9*s+18)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hrow]
        omega
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  dsimp only [couplingRowLoopCost,cachedCouplingRowLoopCost]
  rw [hsum]
  omega

theorem capturedCouplingRowsCost_saving (P q w s t u band a b : ℕ) :
    capturedCouplingRowsCost P q w s t u band a b+s*(18*s*w+9*s+18) =
      runCouplingRowsCost P q w s t u band a b+(18*s*w+9*s+18) := by
  dsimp only [capturedCouplingRowsCost,runCouplingRowsCost,runCachedCouplingRowsCost]
  rw [cachedCouplingRowLoopCost_saving]
  ring

theorem capturedCouplingRowsCost_le (P q w s t u band a b : ℕ) [NeZero s] :
    capturedCouplingRowsCost P q w s t u band a b ≤ runCouplingRowsCost P q w s t u band a b := by
  have h := capturedCouplingRowsCost_saving P q w s t u band a b
  have hN : 1 ≤ s := NeZero.pos s
  have hcopy : 18*s*w+9*s+18 ≤ s*(18*s*w+9*s+18) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (18*s*w+9*s+18) hN
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
