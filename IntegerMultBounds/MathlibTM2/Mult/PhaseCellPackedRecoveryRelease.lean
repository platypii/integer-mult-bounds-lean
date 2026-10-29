module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCouplingCoefficientPage
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Reuse the coefficient-page disposer with recovery's retained word-width header. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedRecoveryReleaseReg (i : Fin 144) : Fin 248 :=
  Fin.castLE (by decide) (Equiv.swap 94 130 i)

theorem packedRecoveryReleaseReg_injective : Function.Injective packedRecoveryReleaseReg := by
  intro i j hij
  apply (Equiv.swap (94 : Fin 144) 130).injective
  apply Fin.ext
  exact congrArg (fun k : Fin 248 => k.val) hij

def packedRecoveryRelease : Pr P 248 Q A U :=
  embProg packedRecoveryReleaseReg Empty.elim releaseCouplingCoefficientPage

def packedRecoveryReleaseCost (N rows w : ℕ) : ℕ :=
  releaseCouplingCoefficientPageCost N rows w

theorem packedRecoveryRelease_exec (w rows : ℕ) (xs : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 248 Q A U) (S : Stacks 248 A)
    (hcount : (S.R 139).length = xs.length) (hrows : (S.R 140).length = rows)
    (hwidth : (S.R 130).length = w) (hpage : S.R 138 = cstream A w xs++tail)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedRecoveryReleaseCost xs.length rows w ∧
      Exec body packedRecoveryRelease (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 138 tail) 139 []) 140 [])}) := by
  obtain ⟨v₁,n,hu₁,hn,he⟩ := releaseCouplingCoefficientPage_exec
    (body := fun p : Empty => nomatch p) w rows xs tail
    (embDn packedRecoveryReleaseReg v) (embStk packedRecoveryReleaseReg S)
    hcount hrows hwidth hpage h109 h104 h105
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedRecoveryReleaseReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let B := embStk packedRecoveryReleaseReg S
  let B₁ : Stacks 144 A := {B with R := Function.update B.R 138 tail}
  let B₂ : Stacks 144 A := {B₁ with R := Function.update B₁.R 139 []}
  change embOvr packedRecoveryReleaseReg {B₂ with R := Function.update B₂.R 140 []}.get S = _
  rw [embOvr_updR packedRecoveryReleaseReg_injective]
  dsimp only [B₂]
  rw [embOvr_updR packedRecoveryReleaseReg_injective]
  dsimp only [B₁,B]
  rw [embOvr_updR packedRecoveryReleaseReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
