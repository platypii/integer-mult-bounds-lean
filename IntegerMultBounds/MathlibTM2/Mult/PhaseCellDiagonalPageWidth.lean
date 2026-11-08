module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientWidth
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Reuse coefficient-evaluator sizing for the owned diagonal page. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main

/-- Two extra bits cover replacing the coefficient evaluator's `t+1` by `s+t`.
The existing coefficient-width generator supplies the remaining width. -/
def diagonalPageWidth (p w u t : ℕ) : ℕ :=
  coefficientWorkspaceWidth p w 1 u 0 t + 2

theorem diagonalPageWidth_bound (p w s t u : ℕ) (hst : s ≤ t) :
    w ≤ diagonalPageWidth p w u t ∧
      u*(s+t)^2*2^(13*p+8) < 2^diagonalPageWidth p w u t := by
  have h := coefficientWorkspaceWidth_bound p w 0 1 u 0 t (by omega)
  dsimp only at h
  refine ⟨by dsimp [diagonalPageWidth]; omega, ?_⟩
  have hs : (s+t)^2 ≤ 4*(t+1)^2 := by
    have hh := Nat.pow_le_pow_left (show s+t ≤ 2*(t+1) by omega) 2
    nlinarith only [hh]
  have hb : u*(t+1)^2*2^(13*p+8) <
      2^coefficientWorkspaceWidth p w 1 u 0 t := by
    simpa only [Nat.mul_one] using h.2.2.2.2.2.2.2
  calc
    _ ≤ 4*(u*(t+1)^2*2^(13*p+8)) := by
      have hm := Nat.mul_le_mul_left u hs
      have hn := Nat.mul_le_mul_right (2^(13*p+8)) hm
      nlinarith only [hn]
    _ < 4*2^coefficientWorkspaceWidth p w 1 u 0 t :=
      Nat.mul_lt_mul_of_pos_left hb (by decide)
    _ = _ := by simp [diagonalPageWidth,pow_add]; ring

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def generateDiagonalPageWidth : Pr P 117 Q A U :=
  .seq generateCoefficientWidth (.act (pushN 115 (fun _ => tick) 2 .done))

theorem generateDiagonalPageWidth_native :
    mnNativePushBound 16 (generateDiagonalPageWidth (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [generateDiagonalPageWidth,generateCoefficientWidth,unarySize,ldrLoop,ldrStep,
    ldrHalfFx,ldrBitAct,ucopy,umul,umulSym,uclear,scanR,drainR,popDo,keepIn,
    pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem generateDiagonalPageWidth_exec (p w u t : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hp : (S.R 114).length = p) (hw : (S.R 94).length = w)
    (hone : (S.R 98).length = 1) (hu : (S.R 99).length = u)
    (hzero : (S.R 100).length = 0) (ht : (S.R 102).length = t)
    (hfresh : ∀ k ∈ [(0 : Fin 117),1,2,3,4,104,115], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ coefficientWidthCost p w 1 u 0 t + 1 ∧
      Exec body generateDiagonalPageWidth (mk v S) m
        (mk v' {S with R := (Function.update S.R 115
          (List.replicate (diagonalPageWidth p w u t) tick))}) := by
  obtain ⟨v',m,hv,hm,he⟩ := generateCoefficientWidth_exec p w 1 u 0 t v S
    hp hw hone hu hzero ht hfresh
  have hpush := Exec.act (body := body) (pushN 115 (fun _ => tick) 2 .done)
    (mk v' {S with R := (Function.update S.R 115
      (List.replicate (coefficientWorkspaceWidth p w 1 u 0 t) tick))})
  rw [pushN_run] at hpush
  refine ⟨v',m+1,hv,by omega,Exec.seq he ?_⟩
  simpa only [Action.run,Function.update_self,Function.update_idem,
    List.replicate_append_replicate,diagonalPageWidth,Nat.add_comm] using hpush

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
