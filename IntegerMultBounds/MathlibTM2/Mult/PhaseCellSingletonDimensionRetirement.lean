module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonPublicationSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Release singleton control copies after the restoring publication call. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U} {src dst : Fin T}

theorem retireSingletonDimensions_exec (plan : PreparedPublicationPlan T src dst)
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R plan.count = []) (hwindow : S.R plan.window = [])
    (hwidth : S.R plan.wordWidth = []) (coreBits wordWidth : List (Fin (A+4))) :
    let F : Stacks T A := {S with R := (Function.update (Function.update
      (Function.update S.R plan.count [tick]) plan.window coreBits) plan.wordWidth wordWidth)}
    ∃ v', v'.user = v.user ∧
      Exec body (clearWords [plan.count,plan.window,plan.wordWidth]) (mk v F)
        (2*(1+coreBits.length+wordWidth.length)+7) (mk v' S) := by
  dsimp only
  have hr := plan.hreg
  regs_ne hr
  let F : Stacks T A := {S with R := (Function.update (Function.update
    (Function.update S.R plan.count [tick]) plan.window coreBits) plan.wordWidth wordWidth)}
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [plan.count,plan.window,plan.wordWidth]
    (by regs_nodup) v F
  have hcost : (([plan.count,plan.window,plan.wordWidth].map (fun i => (F.R i).length)).sum) =
      1+coreBits.length+wordWidth.length := by
    simp [F,Function.update_of_ne, *,Ne.symm,Nat.add_assoc]
  rw [hcost] at he
  refine ⟨v',hu,?_⟩
  convert he using 1
  congr 1
  dsimp only [F]
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hc : i = plan.count
  · subst i; simp [hcount]
  by_cases hw : i = plan.window
  · subst i; simp [hwindow]
  by_cases hwidth' : i = plan.wordWidth
  · subst i; simp [hwidth]
  · simp [F,hc,hw,hwidth',Function.update_of_ne]

/-- Restore setup's owned dimension copies after publication changed its data
ports and advance retirement restored the borrowed suffix. -/
theorem retireSingletonDimensions_after_setup (plan : PreparedPublicationPlan T src dst)
    (coreBits wordWidth : Fin T) (a w : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R plan.count = []) (hwindow : S.R plan.window = [])
    (hwidth : S.R plan.wordWidth = []) (sourceTail output : List (Fin (A+4))) :
    let B := singletonPublicationSetupState plan coreBits wordWidth a w S
    let F : Stacks T A := {B with R := (Function.update (Function.update
      (Function.update B.R src sourceTail) dst output) plan.advances (S.R plan.advances))}
    ∃ v', v'.user = v.user ∧
      Exec body (clearWords [plan.count,plan.window,plan.wordWidth]) (mk v F)
        (2*(1+(S.R coreBits).length+(S.R wordWidth).length)+7)
        (mk v' {S with R := (Function.update (Function.update S.R src sourceTail) dst output)}) := by
  dsimp only
  have hr := plan.hreg
  regs_ne hr
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R src sourceTail) dst output)}
  obtain ⟨v',hu,he⟩ := retireSingletonDimensions_exec (body := body) plan v M
    (by simpa [M,Function.update_of_ne, *,Ne.symm] using hcount)
    (by simpa [M,Function.update_of_ne, *,Ne.symm] using hwindow)
    (by simpa [M,Function.update_of_ne, *,Ne.symm] using hwidth) (S.R coreBits) (S.R wordWidth)
  refine ⟨v',hu,?_⟩
  convert he using 1
  congr 1
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hc : i = plan.count
  · subst i; simp [singletonPublicationSetupState,M,Function.update_of_ne, *,Ne.symm]
  by_cases hw : i = plan.window
  · subst i; simp [singletonPublicationSetupState,M,Function.update_of_ne, *,Ne.symm]
  by_cases hww : i = plan.wordWidth
  · subst i; simp [singletonPublicationSetupState,M,Function.update_of_ne, *,Ne.symm]
  by_cases ha : i = plan.advances
  · subst i; simp [singletonPublicationSetupState,M,Function.update_of_ne, *,Ne.symm]
  · simp [singletonPublicationSetupState,M,Function.update_apply,hc,hw,hww,ha]

/-- Clearing the retained control copies never increases stock. -/
theorem retireSingletonDimensions_within (plan : PreparedPublicationPlan T src dst)
    (v v' : HS T Q A U) (S F : Stacks T A) (n depth : ℕ)
    (he : Exec body (clearWords [plan.count,plan.window,plan.wordWidth]) (mk v S) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth) depth
      (clearWords [plan.count,plan.window,plan.wordWidth]) (mk v S) n (mk v' F) :=
  mn_native_exec_within he 0 (clearWords_native _) depth _ (by simp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
