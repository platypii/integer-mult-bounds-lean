module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInputFinish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellInputBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundaryWorkspace

/-! The executed post-recovery continuation of a prepared packed input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedPreparedInputRelease : Pr P 248 Q A U :=
  .seq packedRecoveryRelease packedInputFinish

def packedPreparedInputReleased {A : ℕ} (S : Stacks 248 A)
    (tail : List (Fin (A+4))) : Stacks 248 A :=
  packedInputFinished
    {S with R := Function.update (Function.update (Function.update S.R 138 []) 139 []) 140 []} tail

theorem packedPreparedInputRelease_exec (V N w q W boundaryCount rows : ℕ)
    (hNV : N < 2^V) (xs : List GaussianInt)
    (residual input tail : List (Fin (A+4)))
    (hresidual : residual.length = N*w) (hinput : input.length = N*w)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hN : S.R 165 = binSyms V N) (hw : (S.R 174).length = w)
    (hwidth : (S.R 130).length = w)
    (hsrc : S.R 110 = residual++(input++tail))
    (hcount : (S.R 139).length = xs.length) (hrows : (S.R 140).length = rows)
    (hpage : S.R 138 = cstream A w xs)
    (hclean : ∀ i ∈ ([0,1,2,104,105,109,246,247,242,243] : List (Fin 248)), S.R i = [])
    (hbank : PackedPreparedBank q w W boundaryCount (embStk packedBoundaryRecoveryBase S)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ packedRecoveryReleaseCost xs.length rows w+packedInputAdvanceCost V N w+(2*w+3) ∧
      Exec body packedPreparedInputRelease (mk v S) n
        (mk v' (packedPreparedInputReleased S tail)) ∧
      PackedPreparedBank q w W boundaryCount
        (embStk packedBoundaryRecoveryBase (packedPreparedInputReleased S tail)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := packedRecoveryRelease_exec w rows xs [] v S
    hcount hrows hwidth (by simpa using hpage)
    (hclean 109 (by decide)) (hclean 104 (by decide)) (hclean 105 (by decide))
  let S₁ : Stacks 248 A :=
    {S with R := Function.update (Function.update (Function.update S.R 138 []) 139 []) 140 []}
  have hbank₁ : PackedPreparedBank q w W boundaryCount (embStk packedBoundaryRecoveryBase S₁) :=
    packedRecoveryRelease_preparedBank S [] hbank
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hbank₂⟩ := packedInputFinish_prepared_exec V N w q W boundaryCount
    hNV residual input tail hresidual hinput v₁ S₁
    (by simpa [S₁] using hN) (by simpa [S₁] using hw)
    (by simpa [S₁] using hwidth) (by simpa [S₁] using hsrc)
    (by
      intro i hi
      have hmem : i ∈ ([0,1,2,104,105,109,246,247,242,243] : List (Fin 248)) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto
      have h138 : i ≠ 138 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have h139 : i ≠ 139 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have h140 : i ≠ 140 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [S₁,h138,h139,h140] using hclean i hmem) hbank₁
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,hbank₂⟩

/-- The completed input exposes the next borrowed source in precisely the
native-bank format required by the packed halo producer. -/
theorem packedPreparedInputReleased_native {A : ℕ} (S : Stacks 248 A)
    (tail : List (Fin (A+4)))
    (hleft : ∀ i : Fin 117, S.L ⟨i.val,by omega⟩ = [])
    (hnative : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → S.R ⟨i.val,by omega⟩ = []) :
    embStk ScalarPlacement.packedCellCoreReg
      (embStk packedHaloRuntimeReg
        (embStk packedBoundaryRecoveryBase (packedPreparedInputReleased S tail))) =
      ScalarPlacement.releasedCellBank [] tail (S.R 93) S.inp S.out := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    exact hleft i
  · funext i
    have hi := i.isLt
    by_cases h93 : i = 93
    · subst i
      simp [embStk,ScalarPlacement.packedCellCoreReg,packedHaloRuntimeReg,
        packedBoundaryRecoveryBase,packedPreparedInputReleased,packedInputFinished,ScalarPlacement.releasedCellBank]
    by_cases h110 : i = 110
    · subst i
      simp [embStk,ScalarPlacement.packedCellCoreReg,packedHaloRuntimeReg,
        packedBoundaryRecoveryBase,packedPreparedInputReleased,packedInputFinished,ScalarPlacement.releasedCellBank]
    have h93v : i.val ≠ 93 := fun he => h93 (Fin.ext he)
    have h110v : i.val ≠ 110 := fun he => h110 (Fin.ext he)
    simpa [embStk,ScalarPlacement.packedCellCoreReg,packedHaloRuntimeReg,
      packedBoundaryRecoveryBase,packedPreparedInputReleased,packedInputFinished,ScalarPlacement.releasedCellBank,
      Fin.ext_iff,h93v,h110v,show i.val ≠ 130 by omega,
      show i.val ≠ 138 by omega,show i.val ≠ 139 by omega,show i.val ≠ 140 by omega]
      using hnative i h93 h110

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
