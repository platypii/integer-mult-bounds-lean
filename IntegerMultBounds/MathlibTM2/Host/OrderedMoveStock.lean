module

public import IntegerMultBounds.MathlibTM2.Host.OrderedMove
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock

/-! An ordered move transfers ownership without allocating tape stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {s t : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ}

theorem moveRightOrdered_within (src tmp dst : Fin T)
    (he : Exec body (moveRightOrdered src tmp dst) s n t)
    (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (moveRightOrdered src tmp dst) s n t := by
  cases he with
  | seq h₁ h₂ =>
    have hw := moveR_within src tmp id h₁ depth B hb
    exact .seq hw (moveR_within tmp dst id h₂ depth B hw.final)

def moveRightPairOrdered (leftSrc rightSrc tmp leftDst rightDst : Fin T) : Pr P T Q A U :=
  .seq (moveRightOrdered leftSrc tmp leftDst) (moveRightOrdered rightSrc tmp rightDst)

/-- Transfer two cached archives into a consumer bank through one shared blank
buffer. Their order and borrowed destination suffixes survive, with zero stock growth. -/
theorem moveRightPairOrdered_exec_within (leftSrc rightSrc tmp leftDst rightDst : Fin T)
    (hreg : [leftSrc,rightSrc,tmp,leftDst,rightDst].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = [])
    (depth B : ℕ) (hb : mnSize (mk v S)+depth ≤ B) :
    let J : Stacks T A := {S with R := (Function.update (Function.update S.R leftSrc []) leftDst
      (S.R leftSrc++S.R leftDst))}
    let F : Stacks T A := {J with R := (Function.update (Function.update J.R rightSrc []) rightDst
      (S.R rightSrc++S.R rightDst))}
    ∃ vf, vf.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ B) depth
        (moveRightPairOrdered leftSrc rightSrc tmp leftDst rightDst) (mk v S)
        (4*((S.R leftSrc).length+(S.R rightSrc).length)+8) (mk vf F) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := moveRightOrdered_exec (body := body) leftSrc tmp leftDst
    ‹leftSrc ≠ tmp› ‹leftSrc ≠ leftDst› ‹tmp ≠ leftDst› v S htmp
  let J : Stacks T A := {S with R := (Function.update (Function.update S.R leftSrc []) leftDst
    (S.R leftSrc++S.R leftDst))}
  have htmpJ : J.R tmp = [] := by
    simpa [J,‹tmp ≠ leftDst›,Ne.symm ‹leftSrc ≠ tmp›] using htmp
  have hrightSrc : J.R rightSrc = S.R rightSrc := by
    simp [J,‹rightSrc ≠ leftDst›,Ne.symm ‹leftSrc ≠ rightSrc›]
  have hrightDst : J.R rightDst = S.R rightDst := by
    simp [J,Ne.symm ‹leftDst ≠ rightDst›,Ne.symm ‹leftSrc ≠ rightDst›]
  obtain ⟨vf,hu₂,he₂⟩ := moveRightOrdered_exec (body := body) rightSrc tmp rightDst
    ‹rightSrc ≠ tmp› ‹rightSrc ≠ rightDst› ‹tmp ≠ rightDst› v₁ J htmpJ
  have hw₁ := moveRightOrdered_within leftSrc tmp leftDst he₁ depth B hb
  have hw₂ := moveRightOrdered_within rightSrc tmp rightDst he₂ depth B hw₁.final
  refine ⟨vf,hu₂.trans hu₁,?_⟩
  have hw := ExecWithin.seq hw₁ hw₂
  rw [hrightSrc,hrightDst] at hw
  simpa only [moveRightPairOrdered,J,show (4*(S.R leftSrc).length+4)+(4*(S.R rightSrc).length+4) =
    4*((S.R leftSrc).length+(S.R rightSrc).length)+8 by omega] using hw

end IntegerMultBounds.MathlibTM2.Host
