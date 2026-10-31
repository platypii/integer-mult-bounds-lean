module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Join two isolated archive banks in forward order. Three moves reuse one
empty scratch tape; every moved symbol is charged twice and scratch is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def joinOwnedArchives (src next saved : Fin T) : Pr P T Q A U :=
  .seq (moveR src saved id) (.seq (moveR next saved id) (moveR saved src id))

theorem joinOwnedArchives_exec (src next saved : Fin T)
    (hreg : [src,next,saved].Nodup) (X Y : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = X) (hnext : S.R next = Y) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (joinOwnedArchives src next saved) (mk v S) (4*(X.length+Y.length)+6)
        (mk v' {S with R := (Function.update (Function.update S.R src (X++Y)) next [])}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body src saved ‹src ≠ saved› id v S
  let S₁ : Stacks T A := {S with R := movedR S.R src saved id (S.R src)}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body next saved ‹next ≠ saved› id v₁ S₁
  let S₂ : Stacks T A := {S₁ with R := movedR S₁.R next saved id (S₁.R next)}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body saved src ‹src ≠ saved›.symm id v₂ S₂
  have hlen₁ : (S.R src).length = X.length := by rw [hsrc]
  have hlen₂ : (S₁.R next).length = Y.length := by simp [S₁,movedR,‹src ≠ next›.symm,‹next ≠ saved›,hnext]
  have hlen₃ : (S₂.R saved).length = Y.length+X.length := by
    simp [S₂,S₁,movedR,hsrc,hnext,hsaved,‹next ≠ saved›,‹src ≠ next›.symm]
  have hf : movedR S₂.R saved src id (S₂.R saved) =
      Function.update (Function.update S.R src (X++Y)) next [] := by
    funext i
    by_cases his : i = src
    · subst i
      simp [S₂,S₁,movedR,hsrc,hnext,hsaved,‹src ≠ saved›,‹src ≠ next›,‹src ≠ next›.symm,‹next ≠ saved›]
    · by_cases hin : i = next
      · subst i
        simp [S₂,S₁,movedR,‹src ≠ next›.symm,‹next ≠ saved›]
      · by_cases hia : i = saved
        · subst i
          simp [movedR,‹src ≠ saved›.symm,‹next ≠ saved›.symm,hsaved]
        · simp [S₂,S₁,movedR,his,hin,hia]
  refine ⟨v₃,hu₃.trans hu₂ |>.trans hu₁,?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  simpa only [joinOwnedArchives,hlen₁,hlen₂,hlen₃,hf,
    show (2*X.length+2)+(2*Y.length+2+(2*(Y.length+X.length)+2)) = 4*(X.length+Y.length)+6 by omega] using he

theorem joinOwnedArchives_pushBound (src next saved : Fin T) :
    mnNativePushBound 1 (joinOwnedArchives (P := P) (Q := Q) (A := A) (U := U) src next saved) := by
  simp [joinOwnedArchives,moveR,whileR,moveStep,drainR,popDo,peekR,popPush,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
