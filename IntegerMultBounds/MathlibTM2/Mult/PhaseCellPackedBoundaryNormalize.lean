module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactorWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryNormalize
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Normalize the owned folded boundary RHS in place, preserving packed geometry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

noncomputable def packedBoundaryNormalize (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  embProg packedBoundaryNormalizeReg Empty.elim (generatedBoundaryNormalize hQ)

theorem packedBoundaryNormalize_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q : ℕ) (hq : 2 ≤ q) (heven : q%2 = 0) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2))
    (v : HS 242 Q A U) (S : Stacks 242 A)
    (hleft : ∀ i, (embStk packedBoundaryNormalizeReg S).L i = [])
    (hmul : ∀ i : Fin 64,
      (embStk packedBoundaryNormalizeReg S).R (boundaryFactorMulReg i) = [])
    (hready : RsbReady (boundaryFactorState (embStk packedBoundaryNormalizeReg S)) (2*q+8) q)
    (hmaster : (S.R 119).length = q)
    (h184 : (embStk packedBoundaryNormalizeReg S).R 184 = [])
    (h220 : (embStk packedBoundaryNormalizeReg S).R 220 = [])
    (h221 : (embStk packedBoundaryNormalizeReg S).R 221 = [])
    (h223 : (embStk packedBoundaryNormalizeReg S).R 223 = [])
    (hya : (embStk packedBoundaryNormalizeReg S).R 208 = [])
    (hac2 : (embStk packedBoundaryNormalizeReg S).R 215 = [])
    (hsrc : S.R 143 = cstream A (2*q+8) xs) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedBoundaryNormalizeCost q xs.length ∧
      Exec body (packedBoundaryNormalize hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 143
          (cstream A (2*q+8) (xs.map (normalizeBoundaryWord q (q/2-1)))))}) := by
  obtain ⟨v₁,n,hu₁,hn,he⟩ := generatedBoundaryNormalize_exec
    (body := fun p : Empty => nomatch p) hQ hA q hq heven xs hbound
    (embDn packedBoundaryNormalizeReg v) (embStk packedBoundaryNormalizeReg S)
    hleft hmul hready hmaster h184 h220 h221 h223 hya hac2 hsrc
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedBoundaryNormalizeReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR packedBoundaryNormalizeReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
