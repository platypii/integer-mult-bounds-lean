module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPackedInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth

/-! Local key input beside the actual 263-register packed numerical bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 276 Q A U}

/-- Supply the native publication replica dimension from the retained real
runtime count, rather than requiring an initialized native counter. -/
def packedKeyInputCounted : Pr P 276 Q A U :=
  .seq packedKeyInput (ucopy 264 251 273)

theorem packedKeyInputCounted_exec (p q W N L : ℕ) (hp : p+1 ≤ q) (hW : 2*q+8 ≤ W)
    (xs : List GaussianInt) (hlen : xs.length = N*L) (tail : List (Fin (A+4)))
    (v : HS 276 Q A U) (S : Stacks 276 A)
    (hq : (S.R 119).length = q) (hpHeader : (S.R 266).length = p)
    (hcommon : (S.R 265).length = W) (hreplicas : (S.R 264).length = N)
    (hpacket : (S.R 267).length = L*W) (hsrc : S.R 263 = cstream A W xs++tail)
    (hblank : ∀ i ∈ ([110,268,269,270,271,272,273,274,275] : List (Fin 276)), S.R i = []) :
    S.R 251 = [] →
    ∃ v' n, v'.user = v.user ∧ n ≤ packedKeyInputCost p q W N L+(4*N+4) ∧
      Exec body packedKeyInputCounted (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 263 tail) 110
          (cstream A (2*q+8) (xs.map (fun z => (2 : GaussianInt)^(q-p-1)*z)))) 251 (List.replicate N tick))}) := by
  intro hcountBlank
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := packedKeyInput_exec (body := body) p q W N L hp hW
    xs hlen tail v S hq hpHeader hcommon hreplicas hpacket hsrc hblank
  let F : Stacks 276 A := {S with R := (Function.update (Function.update S.R 263 tail) 110
    (cstream A (2*q+8) (xs.map (fun z => (2 : GaussianInt)^(q-p-1)*z))))}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body)
    (by decide : (264 : Fin 276) ≠ 251) (by decide : (264 : Fin 276) ≠ 273)
    (by decide : (251 : Fin 276) ≠ 273) v₁ F (by simpa [F] using hblank 273 (by decide))
  refine ⟨v₂,n₁+(4*N+4),hu₂.trans hu₁,Nat.add_le_add_right hn₁ _,
    (Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp [F,hreplicas]
  · apply congrArg (mk v₂)
    simp [F,hreplicas,hcountBlank]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
