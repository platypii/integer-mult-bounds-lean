module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTilePlan

/-! Loading the archive source preserves every ordinary transpose header. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {t₀ T Q c d W K : ℕ}

theorem BankReady.with_source {plan : ArchiveTilePlan t₀ T Q c d W}
    {S : Stacks T (prime+K)} (h : plan.BankReady S) (word : List (Fin (prime+K+4))) :
    plan.BankReady {S with R := Function.update S.R plan.src word} := by
  have control (r : Fin T)
      (hr : r ∈ [plan.base,plan.one,plan.width,plan.exponent,plan.powTmp,plan.powSaved,
        plan.a,plan.half,plan.par,plan.bits,plan.cnt,plan.work]) : r ≠ plan.src :=
    plan.hsourceControls r hr
  have scratch (r : Fin T)
      (hr : r ∈ [plan.ι (reg plan.re),plan.ι (reg plan.im),plan.tmp,plan.saved,plan.count,plan.reRev,plan.imRev]) :
      r ≠ plan.src := by
    intro he
    exact (List.nodup_cons.mp plan.hreg).1 (he ▸ hr)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,h.hL,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Function.update_of_ne (control plan.base (by simp))] using h.hbase
  · simpa only [Function.update_of_ne (control plan.one (by simp))] using h.hone
  · simpa only [Function.update_of_ne (control plan.width (by simp))] using h.hwidth
  · simpa only [Function.update_of_ne (control plan.exponent (by simp))] using h.hexponent
  · intro r hr
    have hne : r ≠ plan.src := by intro he; exact plan.hsourceBank (he ▸ hr)
    simpa only [Function.update_of_ne hne] using h.hblank r hr
  · simpa only [Function.update_of_ne (control plan.powTmp (by simp))] using h.htmp
  · simpa only [Function.update_of_ne (control plan.powSaved (by simp))] using h.hsaved
  · intro j hj
    simpa only [Function.update_of_ne (plan.hsourceOff j)] using h.hpriv j hj
  · intro k
    simpa only [Function.update_of_ne (plan.hsourceOff (reg (plan.hd k)))] using h.hhdr k
  · intro r hr
    have hne := control r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      tauto)
    simpa only [Function.update_of_ne hne] using h.hgenBlank r hr
  · simpa only [Function.update_of_ne (scratch plan.count (by simp))] using h.hcount
  · intro r hr
    have hne := scratch r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      tauto)
    simpa only [Function.update_of_ne hne] using h.hcodecBlank r hr
  · intro i hre him hhd
    simpa only [Function.update_of_ne (plan.hsourceOff (reg i))] using h.hother i hre him hhd

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
