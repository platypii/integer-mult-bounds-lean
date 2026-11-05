module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundaryMasterPreparation

/-! Release generated seam masters after the restoring publication stage.
The retained caller words and both published data ports survive cleanup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem standardBoundaryMasterRetirement_exec (v : HS 117 Q A U) (S : Stacks 117 A)
    (hblank : S.R 26 = [] ∧ S.R 24 = [] ∧ S.R 54 = [] ∧ S.R 19 = [])
    (skip coreBits narrowBits count sourceTail output : List (Fin (A+4))) :
    let F : Stacks 117 A := {S with R := (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update S.R 26 skip) 24 coreBits) 54 narrowBits)
        19 count) 95 sourceTail) 96 output)}
    ∃ v', v'.user = v.user ∧
      Exec body (clearWords [26,24,54,19]) (mk v F)
        (2*(skip.length+coreBits.length+narrowBits.length+count.length)+9)
        (mk v' {S with R := (Function.update (Function.update S.R 95 sourceTail) 96 output)}) := by
  dsimp only
  let F : Stacks 117 A := {S with R := (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update S.R 26 skip) 24 coreBits) 54 narrowBits)
      19 count) 95 sourceTail) 96 output)}
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [(26:Fin 117),24,54,19] (by decide +kernel) v F
  have hcost : (([(26:Fin 117),24,54,19].map (fun i => (F.R i).length)).sum) =
      skip.length+coreBits.length+narrowBits.length+count.length := by
    simp [F,Nat.add_assoc]
  rw [hcost] at he
  refine ⟨v',hu,?_⟩
  convert he using 1
  congr 1
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i ∈ [(26:Fin 117),24,54,19]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [hblank.1,hblank.2.1,hblank.2.2.1,hblank.2.2.2]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    simp [F,Function.update_apply,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2]

theorem standardBoundaryMasterRetirement_within (v v' : HS 117 Q A U) (S F : Stacks 117 A)
    (n depth : ℕ) (he : Exec body (clearWords [26,24,54,19]) (mk v S) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth) depth
      (clearWords [26,24,54,19]) (mk v S) n (mk v' F) :=
  mn_native_exec_within he 0 (clearWords_native _) depth _ (by simp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
