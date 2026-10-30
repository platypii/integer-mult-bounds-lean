module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInputAdvance
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResetPackedInputWidth

/-! Exact return state and cost of advancing a completed prepared input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedInputFinish : Pr P 248 Q A U :=
  .seq packedInputAdvance resetPackedInputWidth

def packedInputFinished {A : ℕ} (S : Stacks 248 A) (tail : List (Fin (A+4))) : Stacks 248 A :=
  {S with R := Function.update (Function.update S.R 110 tail) 130 []}

theorem packedInputFinish_exec (V N w : ℕ) (hNV : N < 2^V)
    (residual input tail : List (Fin (A+4)))
    (hresidual : residual.length = N*w) (hinput : input.length = N*w)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hN : S.R 165 = binSyms V N) (hw : (S.R 174).length = w)
    (hwidth : (S.R 130).length = w)
    (hsrc : S.R 110 = residual++(input++tail))
    (hclean : ∀ i ∈ ([0,1,2,246,247,242,243] : List (Fin 248)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedInputAdvanceCost V N w+(2*w+3) ∧
      Exec body packedInputFinish (mk v S) n (mk v' (packedInputFinished S tail)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := packedInputAdvance_exec V N w hNV residual input tail
    hresidual hinput v S hN hw hsrc hclean
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := resetPackedInputWidth_exec (body := body) w v₁
    {S with R := Function.update S.R 110 tail} (by simpa using hwidth)
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂⟩

theorem packedInputFinished_frame {A : ℕ} (S : Stacks 248 A)
    (tail : List (Fin (A+4))) (i : Fin 248) (h110 : i ≠ 110) (h130 : i ≠ 130) :
    (packedInputFinished S tail).R i = S.R i := by
  simp [packedInputFinished,h110,h130]

/-- Advancing the source and clearing its width leaves the prepared numerical
bank usable for the next input. -/
theorem packedInputFinished_preparedBank {A q w W N : ℕ} (S : Stacks 248 A)
    (tail : List (Fin (A+4)))
    (h : PackedPreparedBank q w W N (embStk packedBoundaryRecoveryBase S)) :
    PackedPreparedBank q w W N
      (embStk packedBoundaryRecoveryBase (packedInputFinished S tail)) := by
  apply h.of_recovery_frame
  · rfl
  · intro i
    have hi := i.isLt
    have hm := h.workspace.mul i
    simpa [embStk,packedBoundaryRecoveryBase,packedInputFinished,preparedBoundaryCoreReg,
      packedBoundaryFactorReg,boundaryFactorMulReg,Fin.ext_iff,
      show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
      show i.val ≠ 206 by omega,show i.val < 154 by omega,
      show i.val ≠ 110 by omega,show i.val ≠ 130 by omega] using hm
  · rfl
  · intro k hk hne
    exact packedInputFinished_frame S tail (packedBoundaryRecoveryBase k)
      (by intro he; have hv := congrArg Fin.val he; change k.val = 110 at hv; omega)
      (by intro he; have hv := congrArg Fin.val he; change k.val = 130 at hv; omega)

theorem packedInputFinish_prepared_exec (V N w q W boundaryCount : ℕ) (hNV : N < 2^V)
    (residual input tail : List (Fin (A+4)))
    (hresidual : residual.length = N*w) (hinput : input.length = N*w)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hN : S.R 165 = binSyms V N) (hw : (S.R 174).length = w)
    (hwidth : (S.R 130).length = w)
    (hsrc : S.R 110 = residual++(input++tail))
    (hclean : ∀ i ∈ ([0,1,2,246,247,242,243] : List (Fin 248)), S.R i = [])
    (hbank : PackedPreparedBank q w W boundaryCount (embStk packedBoundaryRecoveryBase S)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedInputAdvanceCost V N w+(2*w+3) ∧
      Exec body packedInputFinish (mk v S) n (mk v' (packedInputFinished S tail)) ∧
      PackedPreparedBank q w W boundaryCount (embStk packedBoundaryRecoveryBase (packedInputFinished S tail)) := by
  obtain ⟨v',n,hu,hn,he⟩ := packedInputFinish_exec V N w hNV residual input tail
    hresidual hinput v S hN hw hwidth hsrc hclean
  exact ⟨v',n,hu,hn,he,packedInputFinished_preparedBank S tail hbank⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
