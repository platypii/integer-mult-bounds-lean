module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine

/-! Retire the local solution, recovery RHS and original RHS after publishing
an owned core. Generate the halo count from the borrowed core/radius headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

def prepareCoreHaloCount : Pr P 256 Q A U :=
  .seq (ucopy 250 255 104) (.seq (ucopy 249 255 104) (ucopy 249 255 104))

theorem prepareCoreHaloCount_exec (rows radius : ℕ) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hrows : (S.R 250).length = rows) (hradius : (S.R 249).length = radius)
    (h255 : S.R 255 = []) (h104 : S.R 104 = []) :
    ∃ v', v'.user = v.user ∧ Exec body prepareCoreHaloCount (mk v S) (4*rows+8*radius+12)
      (mk v' {S with R := Function.update S.R 255 (List.replicate (rows+2*radius) tick)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 250) (b := 255) (t := 104)
    (by decide) (by decide) (by decide) v S h104
  let S₁ : Stacks 256 A := {S with R := Function.update S.R 255 (List.replicate rows tick)}
  have he₁' : Exec body (ucopy 250 255 104) (mk v S) (4*rows+4) (mk v₁ S₁) := by
    simpa [hrows,h255,S₁] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := 249) (b := 255) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using h104)
  let S₂ : Stacks 256 A := {S with R := Function.update S.R 255 (List.replicate (radius+rows) tick)}
  have he₂' : Exec body (ucopy 249 255 104) (mk v₁ S₁) (4*radius+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hradius,List.replicate_append_replicate] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec body (a := 249) (b := 255) (t := 104)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂] using h104)
  have he₃' : Exec body (ucopy 249 255 104) (mk v₂ S₂) (4*radius+4)
      (mk v₃ {S with R := Function.update S.R 255 (List.replicate (rows+2*radius) tick)}) := by
    simpa [S₂,hradius,List.replicate_append_replicate,
      show radius+(radius+rows) = rows+2*radius by omega] using he₃
  exact ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁' (Exec.seq he₂' he₃')).cast (by omega) rfl⟩

def haloBufferRelease : Pr P 256 Q A U :=
  .seq prepareCoreHaloCount (.seq (retireCountedLine 255 130 132 109 104 105)
    (.seq (retireCountedLine 255 130 110 109 104 105)
      (.seq (retireCountedLine 255 130 110 109 104 105) (uclear 255))))

def haloBufferReleaseCost (rows radius w : ℕ) : ℕ :=
  (4*rows+8*radius+12)+3*retireCountedLineCost (rows+2*radius) w+2*(rows+2*radius)+2

theorem haloBufferRelease_exec (rows radius w : ℕ)
    (output residual rhs outputTail rhsTail : List (Fin (A+4)))
    (houtputLen : output.length = (rows+2*radius)*w)
    (hresidualLen : residual.length = (rows+2*radius)*w)
    (hrhsLen : rhs.length = (rows+2*radius)*w)
    (v : HS 256 Q A U) (S : Stacks 256 A)
    (hrows : (S.R 250).length = rows) (hradius : (S.R 249).length = radius)
    (hwidth : (S.R 130).length = w) (houtput : S.R 132 = output++outputTail)
    (hsource : S.R 110 = residual++(rhs++rhsTail))
    (hfresh : ∀ i ∈ ([104,105,109,255] : List (Fin 256)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ haloBufferReleaseCost rows radius w ∧
      Exec body haloBufferRelease (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 132 outputTail) 110 rhsTail)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := prepareCoreHaloCount_exec (body := body) rows radius v S hrows hradius
    (hfresh 255 (by decide)) (hfresh 104 (by decide))
  let S₁ : Stacks 256 A := {S with R := Function.update S.R 255 (List.replicate (rows+2*radius) tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := retireCountedLine_exec (body := body)
    255 130 132 109 104 105 (by decide) (rows+2*radius) w output outputTail houtputLen v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hwidth) (by simpa [S₁] using houtput)
    (by simpa [S₁] using hfresh 109 (by decide)) (by simpa [S₁] using hfresh 104 (by decide))
    (by simpa [S₁] using hfresh 105 (by decide))
  let S₂ : Stacks 256 A := {S₁ with R := Function.update S₁.R 132 outputTail}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := retireCountedLine_exec (body := body)
    255 130 110 109 104 105 (by decide) (rows+2*radius) w residual (rhs++rhsTail) hresidualLen v₂ S₂
    (by simp [S₂,S₁]) (by simpa [S₂,S₁] using hwidth) (by simpa [S₂,S₁] using hsource)
    (by simpa [S₂,S₁] using hfresh 109 (by decide)) (by simpa [S₂,S₁] using hfresh 104 (by decide))
    (by simpa [S₂,S₁] using hfresh 105 (by decide))
  let S₃ : Stacks 256 A := {S₂ with R := Function.update S₂.R 110 (rhs++rhsTail)}
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := retireCountedLine_exec (body := body)
    255 130 110 109 104 105 (by decide) (rows+2*radius) w rhs rhsTail hrhsLen v₃ S₃
    (by simp [S₃,S₂,S₁]) (by simpa [S₃,S₂,S₁] using hwidth) (by simp [S₃])
    (by simpa [S₃,S₂,S₁] using hfresh 109 (by decide)) (by simpa [S₃,S₂,S₁] using hfresh 104 (by decide))
    (by simpa [S₃,S₂,S₁] using hfresh 105 (by decide))
  let S₄ : Stacks 256 A := {S₃ with R := Function.update S₃.R 110 rhsTail}
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec body 255 v₄ S₄
  have h255 : (S₄.R 255).length = rows+2*radius := by simp [S₄,S₃,S₂,S₁]
  refine ⟨v₅,(4*rows+8*radius+12)+(n₂+(n₃+(n₄+(2*(rows+2*radius)+2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast (by rw [h255]) ?_⟩
  · dsimp only [haloBufferReleaseCost]
    omega
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h255i : i = 255 <;> by_cases h132i : i = 132 <;> by_cases h110i : i = 110 <;>
      simp [S₄,S₃,S₂,S₁,h255i,h132i,h110i,hfresh 255 (by decide)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
