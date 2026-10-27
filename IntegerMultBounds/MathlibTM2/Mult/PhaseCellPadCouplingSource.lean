module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPadPrefixInPlace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPaddingWords
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate and release cyclic-padding controls from ordinary dimension, band and width headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 144 Q A U}

def padCouplingSource : Pr P 144 Q A U :=
  .seq (unaryProduct 100 94 109 104 105)
    (.seq (unaryProduct 97 94 108 104 105)
      (.seq (copyR 108 116 105 id)
        (.seq (usub 109 116 105)
          (.seq (padPrefixInPlace 108 109 116 141 107 115 104 105 106)
            (.seq (uclear 108) (.seq (uclear 109) (uclear 116)))))))

def padCouplingSourceCost (s band w : ℕ) : ℕ := (s+band)*(38*w+9)+68

theorem padCouplingSource_exec {s : ℕ} [NeZero s] (F : ZMod s → GaussianInt)
    (band w : ℕ) (hb : band ≤ s) (tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 97).length = s) (hband : (S.R 100).length = band) (hw : (S.R 94).length = w)
    (hsrc : S.R 141 = cstream A w (chirpLine s F)++tail)
    (h107 : S.R 107 = []) (h108 : S.R 108 = []) (h109 : S.R 109 = [])
    (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) (h106 : S.R 106 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ padCouplingSourceCost s band w ∧
      Exec body padCouplingSource (mk v S) m
        (mk v' {S with R := Function.update S.R 141 (cstream A w (cyclicPaddedLine F band)++tail)}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 100) (b := 94) (dst := 109) (t₁ := 104) (t₂ := 105) (by decide) v S h104 h105
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 109 (List.replicate (band*w) tick)}
  have he₁' : Exec body (unaryProduct 100 94 109 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,hband,hw,h109] using he₁
  have hm₁' : m₁ ≤ band*(4*w+9)+4 := by simpa [hband,hw] using hm₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := 97) (b := 94) (dst := 108) (t₁ := 104) (t₂ := 105) (by decide) v₁ S₁
    (by simpa [S₁] using h104) (by simpa [S₁] using h105)
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 108 (List.replicate (s*w) tick)}
  have he₂' : Exec body (unaryProduct 97 94 108 104 105) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,hs,hw,h108] using he₂
  have hm₂' : m₂ ≤ s*(4*w+9)+4 := by simpa [S₁,hs,hw] using hm₂
  obtain ⟨v₃,hu₃,he₃⟩ := copyR_exec body 108 116 105 (by decide) (by decide) (by decide) id v₂ S₂
    (by simpa [S₂,S₁] using h105)
  let S₃ : Stacks 144 A := {S₂ with R := Function.update S₂.R 116 (List.replicate (s*w) tick)}
  have he₃' : Exec body (copyR 108 116 105 id) (mk v₂ S₂) (4*(s*w)+4) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,h116] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := usub_exec (body := body)
    (a := 109) (b := 116) (t := 105) (by decide) (by decide) (by decide) v₃ S₃
    (by simpa [S₃,S₂,S₁] using h105)
  let S₄ : Stacks 144 A := {S₃ with R := Function.update S₃.R 116 (List.replicate ((s-band)*w) tick)}
  have he₄' : Exec body (usub 109 116 105) (mk v₃ S₃) (4*(band*w)+4) (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁,← Nat.sub_mul] using he₄
  obtain ⟨v₅,m₅,hu₅,hm₅,he₅⟩ := padPrefixInPlace_exec (body := body)
    (full := 108) (band := 109) (skip := 116) (src := 141) (dst := 107)
    (savedSkip := 115) (saved := 104) (tmp := 105) (buf := 106) (by decide)
    w band (chirpLine s F) (by simpa using hb) tail v₄ S₄
    (by simp [S₄,S₃,S₂]) (by simp [S₄,S₃,S₂,S₁]) (by simp [S₄])
    (by simpa [S₄,S₃,S₂,S₁] using hsrc)
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;>
          simp [S₄,S₃,S₂,S₁,h107,h115,h104,h105,h106])
  let S₅ : Stacks 144 A := {S₄ with R := Function.update S₄.R 141 (cstream A w (cyclicPaddedLine F band)++tail)}
  have he₅' : Exec body (padPrefixInPlace 108 109 116 141 107 115 104 105 106)
      (mk v₄ S₄) m₅ (mk v₅ S₅) := by
    simpa [S₅,← cyclicPaddedLine_split F band hb] using he₅
  obtain ⟨v₆,hu₆,he₆⟩ := uclear_exec (body := body) 108 v₅ S₅
  let S₆ : Stacks 144 A := {S₅ with R := Function.update S₅.R 108 []}
  obtain ⟨v₇,hu₇,he₇⟩ := uclear_exec (body := body) 109 v₆ S₆
  let S₇ : Stacks 144 A := {S₆ with R := Function.update S₆.R 109 []}
  obtain ⟨v₈,hu₈,he₈⟩ := uclear_exec (body := body) 116 v₇ S₇
  refine ⟨v₈,m₁+(m₂+((4*(s*w)+4)+((4*(band*w)+4)+
    (m₅+((2*(s*w)+2)+((2*(band*w)+2)+(2*((s-band)*w)+2))))))),
    hu₈.trans (hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅'
      (Exec.seq he₆ (Exec.seq he₇ he₈))))))).cast (by simp [S₇,S₆,S₅,S₄,S₃,S₂,S₁]) ?_⟩
  · have hm₅' : m₅ ≤ (26*s+28*band)*w+46 := by simpa using hm₅
    have hsub : (s-band)*w ≤ s*w := Nat.mul_le_mul_right w (Nat.sub_le _ _)
    dsimp only [padCouplingSourceCost]
    nlinarith only [hm₁',hm₂',hm₅',hsub]
  · apply congrArg (mk v₈)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h108' : k = 108 <;> by_cases h109' : k = 109 <;> by_cases h116' : k = 116 <;>
      simp [S₇,S₆,S₅,S₄,S₃,S₂,S₁,h108',h109',h116',h108,h109,h116,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
