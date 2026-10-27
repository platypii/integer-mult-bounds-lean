module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizationHeader
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizationBudget

/-! Generate and retire the normalization exponent from retained working precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

theorem boundaryFactorReg_ne_header (r : RsbR) : boundaryFactorReg r ≠ 223 := by
  cases r <;> first | decide | (rename_i c; cases c <;> decide)

theorem boundaryFactorState_update_header {A : ℕ} (S : Stacks 224 A) (xs : List (Fin (A+4))) :
    boundaryFactorState {S with R := Function.update S.R 223 xs} = boundaryFactorState S := by
  funext r
  exact Function.update_of_ne (boundaryFactorReg_ne_header r) _ _

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def generatedBoundaryNormalize (hQ : SS.states ≤ Q) : Pr P 224 Q A U :=
  .seq boundaryNormalizationHeader (.seq (boundaryNormalizePhysical hQ) (uclear 223))

def generatedBoundaryNormalizeCost (q N : ℕ) : ℕ :=
  (4*q+5)+(boundaryNormalizePhysicalCost q (q/2-1) N+(2*(q/2-1)+2))

theorem generatedBoundaryNormalize_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q : ℕ) (hq : 2 ≤ q) (heven : q%2 = 0) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2))
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hready : RsbReady (boundaryFactorState S) (2*q+8) q) (hmaster : (S.R 119).length = q)
    (h184 : S.R 184 = []) (h220 : S.R 220 = []) (h221 : S.R 221 = []) (h223 : S.R 223 = [])
    (hya : S.R 208 = []) (hac2 : S.R 215 = []) (hsrc : S.R 206 = cstream A (2*q+8) xs) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedBoundaryNormalizeCost q xs.length ∧
      Exec body (generatedBoundaryNormalize hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 206
          (cstream A (2*q+8) (xs.map (normalizeBoundaryWord q (q/2-1)))))}) := by
  let e := q/2-1
  have hsplit : q = q/2+e+1 := by dsimp [e]; omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := boundaryNormalizationHeader_exec (body := body) q v S hmaster h184 h223
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 223 (List.replicate e tick)}
  have hstate : boundaryFactorState S₁ = boundaryFactorState S := boundaryFactorState_update_header S _
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryNormalizePhysical_exec (body := body) hQ hA q (q/2) e hsplit xs hbound
    v₁ S₁ hleft (by
      intro i
      have hi223 : boundaryFactorMulReg i ≠ 223 := by
        intro hi
        have hv := congrArg (fun k : Fin 224 => k.val) hi
        have hi' := i.isLt
        change i.val = 223 at hv
        omega
      simpa only [S₁,Function.update_of_ne hi223] using hmul i)
    (by rw [hstate]; exact hready) (by simp [S₁])
    (by simpa [S₁] using hsrc) (by simpa [S₁] using h184) (by simpa [S₁] using h220)
    (by simpa [S₁] using h221) (by simpa [S₁] using hya) (by simpa [S₁] using hac2)
  let output := cstream A (2*q+8) (xs.map (normalizeBoundaryWord q e))
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 206 output}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 223 v₂ S₂
  have hlen : (S₂.R 223).length = e := by simp [S₂,S₁]
  have he₃' : Exec body (uclear 223) (mk v₂ S₂) (2*e+2)
      (mk v₃ {S₂ with R := Function.update S₂.R 223 []}) := he₃.cast (by rw [hlen]) rfl
  refine ⟨v₃,n₁+(n₂+(2*e+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃')).cast rfl ?_⟩
  · exact Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _)
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi223 : i = 223 <;> by_cases hi206 : i = 206 <;>
      simp [S₂,S₁,output,e,hi223,hi206,h223]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
