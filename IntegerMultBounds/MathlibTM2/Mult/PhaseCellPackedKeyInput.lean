module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeKeyBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPackedInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth

/-! Local key input beside the actual 263-register packed numerical bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 276 Q A U}

/-- Queue 263, replica count 264, common width 265, input precision 266 and
packet width 267 are outside native solver work. Precision 119 and source 110
are native; every conversion scratch register lies above the solver bank. -/
def packedKeyInput : Pr P 276 Q A U :=
  .seq (takeKeyBatch 264 267 269 263 110 270 271 272)
    (.seq (generateWordWidth 119 268 273)
      (.seq (preparedPackedInput 119 266 265 268 269 110 270 274 275 271 272) (uclear 268)))

def packedKeyInputCost (p q W N L : ℕ) : ℕ :=
  (N*(12*(L*W)+9)+12)+(8*q+9)+
    ((4*q+4*p+9)+packedInputConversionCost W (2*q+8) (q-p-1) (N*L)+(2*(q-p-1)+2))+
    (2*(2*q+8)+2)

/-- Load and normalize exactly one local key batch. The actual packed solver
bank is preserved except for its source, and later-key packets remain intact.
All generated counters and word-width work restore. -/
theorem packedKeyInput_exec (p q W N L : ℕ) (hp : p+1 ≤ q) (hW : 2*q+8 ≤ W)
    (xs : List GaussianInt) (hlen : xs.length = N*L) (tail : List (Fin (A+4)))
    (v : HS 276 Q A U) (S : Stacks 276 A)
    (hq : (S.R 119).length = q) (hpHeader : (S.R 266).length = p)
    (hcommon : (S.R 265).length = W) (hreplicas : (S.R 264).length = N)
    (hpacket : (S.R 267).length = L*W) (hsrc : S.R 263 = cstream A W xs++tail)
    (hblank : ∀ i ∈ ([110,268,269,270,271,272,273,274,275] : List (Fin 276)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedKeyInputCost p q W N L ∧
      Exec body packedKeyInput (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 263 tail) 110
          (cstream A (2*q+8) (xs.map (fun z => (2 : GaussianInt)^(q-p-1)*z))))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := takeCoefficientKeyBatch_exec (body := body)
    (show [(264 : Fin 276),267,269,263,110,270,271,272].Nodup by decide)
    N L W xs hlen tail v S hreplicas hpacket hsrc
    (hblank 110 (by decide)) (hblank 269 (by decide)) (hblank 270 (by decide))
    (hblank 271 (by decide)) (hblank 272 (by decide))
  let S₁ : Stacks 276 A := {S with R := (Function.update (Function.update S.R 263 tail) 110 (cstream A W xs))}
  obtain ⟨v₂,hu₂,he₂⟩ := generateWordWidth_exec (body := body)
    (show [(119 : Fin 276),268,273].Nodup by decide) q v₁ S₁
    (by simpa [S₁] using hq) (by simpa [S₁] using hblank 268 (by decide))
    (by simpa [S₁] using hblank 273 (by decide))
  let S₂ : Stacks 276 A := {S₁ with R := Function.update S₁.R 268 (List.replicate (2*q+8) tick)}
  obtain ⟨v₃,hu₃,he₃⟩ := preparedPackedInput_exec (body := body)
    (show [(119 : Fin 276),266,265,268,269,110,270,274,275,271,272].Nodup by decide)
    p q W hp hW xs v₂ S₂
    (by simpa [S₂,S₁] using hq) (by simpa [S₂,S₁] using hpHeader)
    (by simpa [S₂,S₁] using hcommon) (by simp [S₂]) (by simp [S₂,S₁])
    (by simpa [S₂,S₁] using hblank 269 (by decide))
    (by simpa [S₂,S₁] using hblank 270 (by decide))
    (by simpa [S₂,S₁] using hblank 274 (by decide))
    (by simpa [S₂,S₁] using hblank 275 (by decide))
    (by simpa [S₂,S₁] using hblank 271 (by decide))
    (by simpa [S₂,S₁] using hblank 272 (by decide))
  let S₃ : Stacks 276 A := {S₂ with R := (Function.update S₂.R 110
    (cstream A (2*q+8) (xs.map (fun z => (2 : GaussianInt)^(q-p-1)*z))))}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 268 v₃ S₃
  refine ⟨v₄,n₁+(8*q+9)+((4*q+4*p+9)+packedInputConversionCost W (2*q+8) (q-p-1) xs.length+
    (2*(q-p-1)+2))+(2*(2*q+8)+2),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · simpa only [packedKeyInputCost,hlen] using Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right hn₁ (8*q+9))
        ((4*q+4*p+9)+packedInputConversionCost W (2*q+8) (q-p-1) (N*L)+(2*(q-p-1)+2)))
      (2*(2*q+8)+2)
  · simp [S₃,S₂,S₁,Nat.add_assoc]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = 268
    · subst i; simp [S₃,S₂,S₁,hblank 268 (by decide)]
    by_cases hsource : i = 110
    · subst i; simp [S₃,S₂,S₁]
    by_cases hqueue : i = 263
    · subst i; simp [S₃,S₂,S₁]
    · simp [S₃,S₂,S₁,hi,hsource,hqueue]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
