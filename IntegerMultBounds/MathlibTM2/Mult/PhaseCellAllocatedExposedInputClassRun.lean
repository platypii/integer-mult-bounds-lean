module
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedInputClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringAllocatedRealGather
/-! Actual ambient exposure, metadata loading and restoring routing feed the
numerical class. Only certified output remains after the complete call. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
namespace ComputedClassBanks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {t₀ T Q c d W₀ K s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P (T+PackedTranspose.tapeCount) Q (prime+K) U}
  (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
open ComputedRecoveryPlan (routedPayload)
theorem allocatedExposedInputClassRun_exec (b : RawRecoveryProgramBounds Q (prime+K) U)
    (jobs : List (PackedNormalizedJob (prime+K) s))
    (V D Cprog reserve depth : ℕ)
    (rg : TblR 12 → Fin (T+PackedTranspose.tapeCount)) (hrg : Function.Injective rg) (hoff : ∀ r k, rg r ≠ (extendedBank bank) k)
    (st : TblSt 12 (prime+K)) (hfitValues : ∀ i, st.val i < 2^D)
    (hwl : ∀ r ∈ jobs, V = r.Bcore)
    (hfit : ∀ r ∈ jobs, r.a < 2^V)
    (hstock : ∀ r ∈ jobs, (plan (extendedBank bank) (extendedBank_injective bank hinj)).coreStock b V r Cprog ≤ reserve)
    (hpush : mnProgPush (descriptorSolverSchedule (plan (extendedBank bank) (extendedBank_injective bank hinj)).src (plan (extendedBank bank) (extendedBank_injective bank hinj)).saved (plan (extendedBank bank) (extendedBank_injective bank hinj)).tmp (plan (extendedBank bank) (extendedBank_injective bank hinj)).clock (plan (extendedBank bank) (extendedBank_injective bank hinj)).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := (prime+K))
        (plan (extendedBank bank) (extendedBank_injective bank hinj)).work (plan (extendedBank bank) (extendedBank_injective bank hinj)).src (plan (extendedBank bank) (extendedBank_injective bank hinj)).saved (plan (extendedBank bank) (extendedBank_injective bank hinj)).count (plan (extendedBank bank) (extendedBank_injective bank hinj)).tmp (plan (extendedBank bank) (extendedBank_injective bank hinj)).spare (plan (extendedBank bank) (extendedBank_injective bank hinj)).result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (coreWidth radius H N W : ℕ) (hcoreWidth : 0 < coreWidth) (hwide : s+coreWidth+2*radius < 2^V)
    (hHfit : H < 2^V) (hA : 4 ≤ (prime+K)) (hV : 0 < V)
    (hlen : jobs.length = (coreGatherIndices s coreWidth radius H).length)
    (horiginJobs : jobs.flatMap (fun r => binSyms (A := (prime+K)) V r.a) =
      (coreGatherIndices s coreWidth radius H).flatMap (fun k => binSyms V (coreStart coreWidth k-radius)))
    (hvolume : ∀ r ∈ jobs, (routedPayload r).length = N*(H*W))
    (v : HS (T+PackedTranspose.tapeCount) Q (prime+K) U) (S : Stacks (T+PackedTranspose.tapeCount) (prime+K)) 
     (hjobHalo : ∀ r ∈ jobs, H = r.b-r.a)
    (hvalues : st.val 6 = V ∧ st.val 7 = W ∧ st.val 8 = N ∧ st.val 9 = radius ∧ st.val 11 = H)
    (hprecision : ∀ r ∈ jobs, st.val 0 = r.p)
    (hparameters : ∀ r ∈ jobs, ∀ i : Fin 6,
      st.val (Fin.castLE (by decide : 6 ≤ 12) i) = r.masterInput.values (Fin.castLE (by decide : 6 ≤ 8) i))
    (hjobRadius : ∀ r ∈ jobs, radius = r.radius)
    (hjobRows : ∀ r ∈ jobs, st.val 10 = coreLength s r.coreWidth r.k)
    (hjobWord : ∀ r ∈ jobs, W = r.W) (hjobFields : ∀ r ∈ jobs, N = r.Fs.length)
    (Vg a Dg : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (borrowed : List (Fin (prime+K+4)))
    (g : AllocatedRealGatherData (Q := Q) bank Vg s coreWidth radius H W a Dg Fs borrowed S)
    (hstream : jobs.flatMap routedPayload = coreSupplierStream (prime+K) coreWidth radius H W Fs.reverse)
    (hready : InputReady (extendedBank bank) (extendedBank_injective bank hinj) rg V D s coreWidth radius H st S)
      :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ g.timeCost+(unaryCopiesCost D st.val (inputCopies (extendedBank bank))+((preparedCoreOriginsCost V s coreWidth radius H+recoveryPayloadCountCost N H W)+
        ((jobs.map ((plan (extendedBank bank) (extendedBank_injective bank hinj)).coreTimeCost b V)).sum+5*jobs.length+4)+(2*(jobs.length+N*(H*W))+5))+(2*inputVolume st.val+2*(inputRegisters (extendedBank bank)).length+1)) ∧
      List.Forall₂ PackedNormalizedJob.output jobs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (g.stockAllowance+(3*unaryCopiesCost D st.val (inputCopies (extendedBank bank))+(((3*preparedCoreOriginsCost V s coreWidth radius H+2*recoveryPayloadCountCost N H W)+reserve)+3*(2*inputVolume st.val+2*(inputRegisters (extendedBank bank)).length+1))))) depth
        (.seq g.program (inputClassProgram (extendedBank bank) (extendedBank_injective bank hinj) b rg)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (plan (extendedBank bank) (extendedBank_injective bank hinj)).result
          (outputs.reverse.flatten++S.R (plan (extendedBank bank) (extendedBank_injective bank hinj)).result))}) := by
  apply preparedInputClassRun_exec (body := body) (extendedBank bank) (extendedBank_injective bank hinj)
    b jobs V D Cprog reserve depth rg hrg hoff st hfitValues hwl hfit hstock hpush hbody
    coreWidth radius H N W hcoreWidth hwide hHfit hA hV hlen horiginJobs hvolume v S
    hjobHalo hvalues hprecision hparameters hjobRadius hjobRows hjobWord hjobFields
    g.program g.timeCost g.stockAllowance g.houtput ?_ hready
  obtain ⟨v',n,hu,hn,he⟩ := g.exec body v depth
  rw [←hstream] at he
  exact ⟨v',n,hu,hn,he⟩

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
