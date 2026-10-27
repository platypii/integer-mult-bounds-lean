module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCouplingRowLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversePrefixInPlace

/-! Generate the whole-line row clock, execute every coupling row and publish
in natural coordinate order, releasing the clock and current index. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def runCachedCouplingRows (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 144 Q A U :=
  .seq (ucopy 97 143 135) (.seq (cachedCouplingRowLoop hQ boundary)
    (.seq (reversePrefixInPlace 97 104 94 113 115 105 106 108 109) (uclear 107)))

def runCachedCouplingRowsCost (P q w s t u band a b : ℕ) : ℕ :=
  cachedCouplingRowLoopCost P q w s t u band a b 0 s+32*s*w+34*s+28

theorem runCachedCouplingRows_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hlen : rhs.length = s)
    (tail rhsTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) (embStk cachedCouplingCoreReg (embStk cachedCouplingOuterReg S)))
    (hcache : ∃ cacheTail, S.R 141 = cstream A w (chirpLine s C)++cacheTail)
    (hindex : S.R 107 = []) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = []) (h135 : S.R 135 = [])
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ runCachedCouplingRowsCost P q w s t u band a b ∧
      Exec (body) (runCachedCouplingRows hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail)
          113 (cstream A w (couplingRowWords P q t u band a b boundary C 0 rhs)++S.R 113))}) := by
  have hs : (S.R 97).length = s := hready.axis
  have hwS : (S.R 94).length = w := hready.width
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body)
    (show (97 : Fin 144) ≠ 143 by decide) (show (97 : Fin 144) ≠ 135 by decide)
    (show (143 : Fin 144) ≠ 135 by decide) v S h135
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 143 (List.replicate s tick)}
  have he₁' : Exec (body) (ucopy 97 143 135) (mk v S) (4*s+4) (mk v₁ S₁) := by
    simpa [S₁,hs,h143] using he₁
  have hready₁ : CouplingReady P q w s t u band a b
      (cstream A w (chirpLine s C)++tail) (embStk cachedCouplingCoreReg (embStk cachedCouplingOuterReg S₁)) := by
    have hproject : embStk cachedCouplingOuterReg S₁ = embStk cachedCouplingOuterReg S := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      exact Function.update_of_ne (cachedCouplingOuterReg_off 143 (by decide) (by decide) i) _ _
    rw [hproject]
    exact hready
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := cachedCouplingRowLoop_exec (body := body) (i := 0) hQ boundary hA hw5 hqw
    hst haS hbS hbandS hP C rhs (by omega) tail rhsTail v₁ S₁ hready₁ (by obtain ⟨cacheTail,hh⟩ := hcache; exact ⟨cacheTail,by simpa [S₁] using hh⟩)
    (by simp [S₁,hindex]) (by simpa [S₁] using hrhs) (by simp [S₁,hlen])
    (by simpa only [Nat.zero_add,hlen] using hxs) (by simpa only [Nat.zero_add,hlen] using has)
  let ys := couplingRowWords P q t u band a b boundary C 0 rhs
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update (Function.update (Function.update (Function.update S₁.R
    93 rhsTail) 107 (List.replicate s tick)) 113 (cstream A w ys.reverse++S₁.R 113)) 143 [])}
  have he₂' : Exec (body) (cachedCouplingRowLoop hQ boundary) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,ys,hlen,S₁,hindex] using he₂
  have hys : ys.length = s := by simp [ys,hlen]
  have hfresh : ∀ k ∈ [(104 : Fin 144),115,105,106,108,109], S₂.R k = [] := by
    intro k hk
    have hlow : k.val < 117 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    let r : Fin 117 := ⟨k.val,hlow⟩
    have hne : k ≠ 93 ∧ k ≠ 107 ∧ k ≠ 113 ∧ k ≠ 143 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hr : r ∈ [(92 : Fin 117),96,102,104,105,106,108,109,115,116] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [r,Fin.ext_iff]
    have hh := hready.fresh r hr
    have hmap : cachedCouplingOuterReg (cachedCouplingCoreReg r) = k := by
      apply Fin.ext
      simp [cachedCouplingOuterReg,cachedCouplingCoreReg,r,hlow]
    change S.R (cachedCouplingOuterReg (cachedCouplingCoreReg r)) = [] at hh
    rw [hmap] at hh
    simpa [S₂,S₁,hne.1,hne.2.1,hne.2.2.1,hne.2.2.2] using hh
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := reversePrefixInPlace_exec (body := body)
    (records := 97) (recordSaved := 104) (width := 94) (src := 113) (dst := 115)
    (saved := 105) (buf := 106) (tmp := 108) (count := 109) (by decide)
    w ys.reverse (S.R 113) v₂ S₂
    (by simp [S₂,S₁,hs,hys]) (by simpa [S₂,S₁] using hwS) (by simp [S₂,S₁]) hfresh
  let S₃ : Stacks 144 A := {S₂ with R := Function.update S₂.R 113 (cstream A w ys++S.R 113)}
  have he₃' : Exec (body) (reversePrefixInPlace 97 104 94 113 115 105 106 108 109)
      (mk v₂ S₂) m₃ (mk v₃ S₃) := by simpa [S₃] using he₃
  have h107₃ : S₃.R 107 = List.replicate s tick := by simp [S₃,S₂]
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 107 v₃ S₃
  refine ⟨v₄,(4*s+4)+(m₂+(m₃+(2*s+2))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast (by rw [h107₃]; simp) ?_⟩
  · have hm₂' : m₂ ≤ cachedCouplingRowLoopCost P q w s t u band a b 0 s := by simpa [hlen] using hm₂
    have hm₃' : m₃ ≤ 32*s*w+28*s+22 := by simpa [hys] using hm₃
    dsimp only [runCachedCouplingRowsCost]
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h107 : k = 107 <;> by_cases h143' : k = 143 <;> by_cases h113 : k = 113 <;>
      simp [S₃,S₂,S₁,h107,h143',h113,hindex,h143,ys,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
