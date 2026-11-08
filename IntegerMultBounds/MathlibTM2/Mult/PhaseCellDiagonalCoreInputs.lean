module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalPageInputs

/-! Construct owned interval endpoints from retained recovery rulers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def copyUnarySum (a b dst tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy a dst tmp) (uadd b dst tmp)

theorem copyUnarySum_native (a b dst tmp : Fin T) :
    mnNativePushBound 2 (copyUnarySum (P := P) (Q := Q) (A := A) (U := U) a b dst tmp) := by
  simp [copyUnarySum,ucopy,uadd,umulSym,scanR,drainR,popDo,keepIn,
    pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem copyUnarySum_exec (a b dst tmp : Fin T) (hreg : [a,b,dst,tmp].Nodup)
    (x y : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (ha : (S.R a).length = x) (hb : (S.R b).length = y)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyUnarySum a b dst tmp) (mk v S) ((4*x+4)+(4*y+4))
        (mk v' {S with R := Function.update S.R dst (List.replicate (x+y) tick)}) := by
  regs_ne hreg
  obtain ⟨v₁,hv₁,he₁⟩ := ucopy_exec (body := body) (a := a) (b := dst) (t := tmp)
    (by assumption) (by assumption) (by assumption) v S htmp
  let M : Stacks T A := {S with R := Function.update S.R dst (List.replicate x tick)}
  have he₁' : Exec body (ucopy a dst tmp) (mk v S) (4*x+4) (mk v₁ M) := by
    simpa [M,ha,hdst] using he₁
  have hbd : b ≠ dst := by assumption
  have htd : tmp ≠ dst := Ne.symm (by assumption)
  obtain ⟨v₂,hv₂,he₂⟩ := uadd_exec (body := body) (a := b) (b := dst) (t := tmp)
    hbd (by assumption) (by assumption) v₁ M (by simpa [M,Function.update_of_ne htd] using htmp)
  have he₂' : Exec body (uadd b dst tmp) (mk v₁ M) (4*y+4)
      (mk v₂ {S with R := Function.update S.R dst (List.replicate (x+y) tick)}) := by
    simpa [M,Function.update_of_ne hbd,hb,List.replicate_append_replicate,Nat.add_comm] using he₂
  exact ⟨v₂,hv₂.trans hv₁,Exec.seq he₁' he₂'⟩

namespace ScalarPlacement.LocalRecoveryLayout
noncomputable section
variable {body : P → Pr P tapes Q A U}

def diagonalHaloStart : Fin tapes := recovery (.parameter 6)
def diagonalCropOffset : Fin tapes := recovery (.control .cropOffset)
def diagonalCropRows : Fin tapes := recovery (.control .cropRows)

def prepareDiagonalCoreInputs : Pr P tapes Q A U :=
  .seq (copyUnarySum diagonalHaloStart diagonalCropOffset diagonalCoreStart diagonalConvertTmp)
    (copyUnarySum diagonalCoreStart diagonalCropRows diagonalCoreEnd diagonalConvertTmp)

def prepareDiagonalCoreInputsCost (a radius rows : ℕ) : ℕ :=
  ((4*a+4)+(4*radius+4))+((4*(a+radius)+4)+(4*rows+4))

theorem prepareDiagonalCoreInputs_native :
    mnNativePushBound 2 (prepareDiagonalCoreInputs (P := P) (Q := Q) (A := A) (U := U)) :=
  ⟨copyUnarySum_native ..,copyUnarySum_native ..⟩

theorem prepareDiagonalCoreInputs_exec (a radius rows : ℕ)
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (ha : (S.R diagonalHaloStart).length = a)
    (hradius : (S.R diagonalCropOffset).length = radius)
    (hrows : (S.R diagonalCropRows).length = rows)
    (hfresh : ∀ i ∈ [(309 : Fin 392),310,307], S.R (recovery (.work i)) = []) :
    ∃ v', v'.user = v.user ∧ ∀ depth,
      ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        2*prepareDiagonalCoreInputsCost a radius rows) depth prepareDiagonalCoreInputs (mk v S)
        (prepareDiagonalCoreInputsCost a radius rows)
        (mk v' {S with R := (Function.update (Function.update S.R diagonalCoreStart
          (List.replicate (a+radius) tick)) diagonalCoreEnd (List.replicate (a+radius+rows) tick))}) := by
  have hreg₁ : [diagonalHaloStart,diagonalCropOffset,diagonalCoreStart,diagonalConvertTmp].Nodup := by
    simp [diagonalHaloStart,diagonalCropOffset,diagonalCoreStart,diagonalConvertTmp,recovery_injective.eq_iff]
  obtain ⟨v₁,hv₁,he₁⟩ := copyUnarySum_exec (body := body) _ _ _ _ hreg₁ a radius v S ha hradius
    (hfresh 309 (by simp)) (hfresh 307 (by simp))
  let M : Stacks tapes A := {S with R := Function.update S.R diagonalCoreStart (List.replicate (a+radius) tick)}
  have hreg₂ : [diagonalCoreStart,diagonalCropRows,diagonalCoreEnd,diagonalConvertTmp].Nodup := by
    simp [diagonalCoreStart,diagonalCropRows,diagonalCoreEnd,diagonalConvertTmp,recovery_injective.eq_iff]
  have hrd : diagonalCropRows ≠ diagonalCoreStart := by
    simp [diagonalCropRows,diagonalCoreStart,recovery_injective.eq_iff]
  have hed : diagonalCoreEnd ≠ diagonalCoreStart := by
    simp [diagonalCoreEnd,diagonalCoreStart,recovery_injective.eq_iff]
  have htd : diagonalConvertTmp ≠ diagonalCoreStart := by
    simp [diagonalConvertTmp,diagonalCoreStart,recovery_injective.eq_iff]
  obtain ⟨v₂,hv₂,he₂⟩ := copyUnarySum_exec (body := body) _ _ _ _ hreg₂ (a+radius) rows v₁ M
    (by simp [M]) (by exact congrArg List.length (Function.update_of_ne hrd _ _) |>.trans hrows)
    (by exact (Function.update_of_ne hed _ _).trans (hfresh 310 (by simp)))
    (by exact (Function.update_of_ne htd _ _).trans (hfresh 307 (by simp)))
  have hex : Exec body prepareDiagonalCoreInputs (mk v S) (prepareDiagonalCoreInputsCost a radius rows)
      (mk v₂ {S with R := (Function.update (Function.update S.R diagonalCoreStart
        (List.replicate (a+radius) tick)) diagonalCoreEnd (List.replicate (a+radius+rows) tick))}) :=
    Exec.seq he₁ he₂
  exact ⟨v₂,hv₂.trans hv₁,fun depth => mn_native_exec_within hex 2 prepareDiagonalCoreInputs_native depth
    (mnSize (mk v S)+depth+2*prepareDiagonalCoreInputsCost a radius rows) (by omega)⟩

end
end ScalarPlacement.LocalRecoveryLayout
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
