module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeCountedLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Attach the next packed halo to the borrowed source using retained binary
length and precision, then retire the temporary unary controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 264 Q A U}

def attachQueuedHalo : Pr P 264 Q A U :=
  .seq (toUnary 165 258 104 105 106)
    (.seq (generateWordWidth 119 259 104)
      (.seq (takeCountedLine 258 259 256 110 260 104 105) (clearWords [258,259])))

def attachQueuedHaloCost (V q L : ℕ) : ℕ :=
  (6*L+11*V+6)+(8*q+9)+takeCountedLineCost L (2*q+8)+2*(L+(2*q+8))+5

theorem attachQueuedHalo_exec (V q L : ℕ) (hL : L < 2^V)
    (xs tail : List (Fin (A+4))) (hlen : xs.length = L*(2*q+8))
    (v : HS 264 Q A U) (S : Stacks 264 A)
    (h165 : S.R 165 = binSyms V L) (hq : (S.R 119).length = q)
    (hsource : S.R 256 = xs++tail)
    (hfresh : ∀ k ∈ [(104 : Fin 264),105,106,258,259,260], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ attachQueuedHaloCost V q L ∧
      Exec body attachQueuedHalo (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 256 tail) 110 (xs++S.R 110))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear body
    (a := 165) (z := 258) (w := 104) (t := 105) (t₂ := 106) (by decide) hL v S h165
    (hfresh 104 (by simp)) (hfresh 105 (by simp)) (hfresh 106 (by simp))
  let S₁ : Stacks 264 A := {S with R := Function.update S.R 258 (List.replicate L tick)}
  have he₁' : Exec body (toUnary 165 258 104 105 106) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁, hfresh 258 (by simp)] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := generateWordWidth_exec (body := body)
    (precision := 119) (width := 259) (tmp := 104) (by decide) q v₁ S₁
    (by simpa [S₁] using hq) (by simpa [S₁] using hfresh 259 (by simp))
    (by simpa [S₁] using hfresh 104 (by simp))
  let S₂ : Stacks 264 A := {S₁ with R := Function.update S₁.R 259 (List.replicate (2*q+8) tick)}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := takeCountedLine_exec (body := body)
    (rows := 258) (width := 259) (src := 256) (dst := 110) (count := 260) (buf := 104) (tmp := 105)
    (by decide) L (2*q+8) xs tail hlen v₂ S₂ (by simp [S₂,S₁]) (by simp [S₂])
    (by simpa [S₂,S₁] using hsource) (by simpa [S₂,S₁] using hfresh 260 (by simp))
    (by simpa [S₂,S₁] using hfresh 104 (by simp)) (by simpa [S₂,S₁] using hfresh 105 (by simp))
  let S₃ : Stacks 264 A := {S₂ with R := (Function.update (Function.update S₂.R 256 tail) 110 (xs++S₂.R 110))}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [258,259] (by decide) v₃ S₃
  have hclock : 2*(([(258 : Fin 264),259].map fun k => (S₃.R k).length).sum)+
      2*[(258 : Fin 264),259].length+1 = 2*(L+(2*q+8))+5 := by simp [S₃,S₂,S₁]
  refine ⟨v₄,n₁+((8*q+9)+(n₃+(2*(L+(2*q+8))+5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [hclock]) ?_⟩
  · unfold attachQueuedHaloCost
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h258 : k = 258 <;> by_cases h259 : k = 259 <;>
      by_cases h256 : k = 256 <;> by_cases h110 : k = 110 <;>
      simp [S₃,S₂,S₁,h258,h259,h256,h110,hfresh 258 (by simp),hfresh 259 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
