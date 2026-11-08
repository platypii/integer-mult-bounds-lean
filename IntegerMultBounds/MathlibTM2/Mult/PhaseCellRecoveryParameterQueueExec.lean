module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryParameterQueue

/-! Execute normalization parameter preparation from retained ordinary rulers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
namespace RecoveryParameterQueue
variable {T Q A : ℕ} {P U : Type} {normalize : RecoveryNormalizePlan T}
  {body : P → Pr P T Q A U}

theorem exec (queue : RecoveryParameterQueue normalize)
    (B p u l target s t a b : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R (normalize.scalar .wr)).length = B)
    (hparameters : ∀ i : Fin 8, (S.R (queue.parameters i)).length = ![p,u,l,target,s,t,a,b] i)
    (hblank : ∀ i ∈ [queue.word,queue.saved,queue.tmp], S.R i = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (p+u+l+target+s+t+a+b)*(4*B+10)+8*(8*B+12)+1 ∧
      ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+8*(2*(4*B+4))) depth
        queue.program (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R normalize.header
          ((inverseParameterWords p u l target s t a b).flatMap (fun i => binSyms (A := A) B i.2)++S.R normalize.header))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := binaryHeaderQueue_exec (body := body)
    (normalize.scalar .wr) queue.word queue.saved queue.tmp normalize.header queue.carry
    (List.ofFn queue.parameters)
    (by intro src hs; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs; exact queue.regs i)
    v S hblank depth
  have hcost : binaryHeaderQueueCost S.R B (List.ofFn queue.parameters) =
      (p+u+l+target+s+t+a+b)*(4*B+10)+8*(8*B+12)+1 := by
    rw [binaryHeaderQueueCost_eq]
    have hm : (List.ofFn queue.parameters).map (fun i => (S.R i).length) =
        List.ofFn (fun i : Fin 8 => ![p,u,l,target,s,t,a,b] i) := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact hparameters i
    rw [hm]
    norm_num [List.ofFn_succ]
    ring
  have hwords : (List.ofFn queue.parameters).flatMap (fun i => binSyms (A := A) B (S.R i).length) =
      (inverseParameterWords p u l target s t a b).flatMap (fun i => binSyms (A := A) B i.2) := by
    simp [List.ofFn_succ,inverseParameterWords,hparameters]
  rw [hwidth] at hn he
  rw [hcost] at hn
  exact ⟨v',n,hu,hn,by simpa only [program,List.length_ofFn,hwords] using he⟩

end RecoveryParameterQueue
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
