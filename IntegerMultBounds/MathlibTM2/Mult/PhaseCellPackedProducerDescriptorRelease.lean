module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerDescriptor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseDescriptorBank

/-! Release the generated descriptor and clock after the producer restores them.
Only the owned prefix is retired; the caller's following queue is retained. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedProducerPlan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def releaseDescriptor (plan : PackedProducerPlan T Q) : Pr P T Q A U :=
  .seq (retireDescriptorBank plan.src plan.count plan.tmp 325) (uclear plan.clock)

theorem releaseDescriptor_exec (plan : PackedProducerPlan T Q) (r : PackedNormalizedJob A s)
    (rest : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R plan.src = descriptorScheduleTape plan.work PackedNormalizedJob.words [r]++rest)
    (hcount : S.R plan.count = []) (htmp : S.R plan.tmp = []) (hclock : (S.R plan.clock).length = 1)
    (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 9*(descriptorScheduleTape plan.work PackedNormalizedJob.words [r]).length+5 ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        9*(descriptorScheduleTape plan.work PackedNormalizedJob.words [r]).length+5) depth
        plan.releaseDescriptor (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R plan.src rest) plan.clock [])}) := by
  have hr := plan.hreg
  regs_ne hr
  have htape : descriptorScheduleTape plan.work PackedNormalizedJob.words [r] =
      descriptorBankTape (placedDescriptorFields plan.work r.words) := by
    simp only [descriptorScheduleTape,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  obtain ⟨v',n,hu,hn,he⟩ := releaseDescriptorBank_exec (body := body) plan.work r.words
    plan.src plan.count plan.tmp plan.clock (by regs_nodup) rest v S
    (by simpa only [htape] using hsrc) hcount htmp hclock depth
  rw [← htape] at hn he
  exact ⟨v',n,hu,hn,he.mono (by intro d z hz; omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedProducerPlan
