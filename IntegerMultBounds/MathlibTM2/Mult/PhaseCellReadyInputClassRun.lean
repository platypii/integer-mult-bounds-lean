module
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassInputReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputComputedClassRun
/-! Execute the generated-input class from its ordinary readiness record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
namespace ComputedClassBanks
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}
  (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
open ComputedRecoveryPlan (routedPayload)
theorem inputClassRun_exec_of_ready (b : RawRecoveryProgramBounds Q A U)
    (jobs : List (PackedNormalizedJob A s))
    (V D Cprog reserve depth : ℕ)
    (rg : TblR 12 → Fin T) (hrg : Function.Injective rg) (hoff : ∀ r k, rg r ≠ bank k)
    (st : TblSt 12 A) (hfitValues : ∀ i, st.val i < 2^D)
    (hwl : ∀ r ∈ jobs, V = r.Bcore)
    (hfit : ∀ r ∈ jobs, r.a < 2^V)
    (hstock : ∀ r ∈ jobs, (plan bank hinj).coreStock b V r Cprog ≤ reserve)
    (hpush : mnProgPush (descriptorSolverSchedule (plan bank hinj).src (plan bank hinj).saved (plan bank hinj).tmp (plan bank hinj).clock (plan bank hinj).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
        (plan bank hinj).work (plan bank hinj).src (plan bank hinj).saved (plan bank hinj).count (plan bank hinj).tmp (plan bank hinj).spare (plan bank hinj).result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (coreWidth radius H N W : ℕ) (hcoreWidth : 0 < coreWidth) (hwide : s+coreWidth+2*radius < 2^V)
    (hHfit : H < 2^V) (hA : 4 ≤ A) (hV : 0 < V)
    (hlen : jobs.length = (coreGatherIndices s coreWidth radius H).length)
    (horiginJobs : jobs.flatMap (fun r => binSyms (A := A) V r.a) =
      (coreGatherIndices s coreWidth radius H).flatMap (fun k => binSyms V (coreStart coreWidth k-radius)))
    (hvolume : ∀ r ∈ jobs, (routedPayload r).length = N*(H*W))
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
     (hjobHalo : ∀ r ∈ jobs, H = r.b-r.a)
    (hvalues : st.val 6 = V ∧ st.val 7 = W ∧ st.val 8 = N ∧ st.val 9 = radius ∧ st.val 11 = H)
    (hprecision : ∀ r ∈ jobs, st.val 0 = r.p)
    (hparameters : ∀ r ∈ jobs, ∀ i : Fin 6,
      st.val (Fin.castLE (by decide : 6 ≤ 12) i) = r.masterInput.values (Fin.castLE (by decide : 6 ≤ 8) i))
    (hjobRadius : ∀ r ∈ jobs, radius = r.radius)
    (hjobRows : ∀ r ∈ jobs, st.val 10 = coreLength s r.coreWidth r.k)
    (hjobWord : ∀ r ∈ jobs, W = r.W) (hjobFields : ∀ r ∈ jobs, N = r.Fs.length)
    (hready : InputReady bank hinj rg V D s coreWidth radius H st S)
    (hsource : S.R (control bank .source) = jobs.flatMap routedPayload++tail)  :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ unaryCopiesCost D st.val (inputCopies bank)+((preparedCoreOriginsCost V s coreWidth radius H+recoveryPayloadCountCost N H W)+
        ((jobs.map ((plan bank hinj).coreTimeCost b V)).sum+5*jobs.length+4)+(2*(jobs.length+N*(H*W))+5))+(2*inputVolume st.val+2*(inputRegisters bank).length+1) ∧
      List.Forall₂ PackedNormalizedJob.output jobs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (3*unaryCopiesCost D st.val (inputCopies bank)+(((3*preparedCoreOriginsCost V s coreWidth radius H+2*recoveryPayloadCountCost N H W)+reserve)+3*(2*inputVolume st.val+2*(inputRegisters bank).length+1)))) depth
        (inputClassProgram bank hinj b rg) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (control bank .source) tail) (plan bank hinj).result
          (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  exact inputClassRun_exec (body := body) bank hinj b jobs V D Cprog reserve depth rg hrg hoff st hfitValues
    hwl hfit hstock hpush hbody coreWidth radius H N W hcoreWidth hwide hHfit hA hV hlen horiginJobs hvolume
    v S tail hready.hs hready.hw hready.hr hready.hH hready.hz hready.htable hready.h104 hready.h106
    hready.h116 hready.hprepBlank hjobHalo hready.hreaderBlank hready.hinput hready.hinputBlank hvalues
    hprecision hparameters hjobRadius hjobRows hready.hscalar hready.hmasters hready.hcontrols hready.hleft
    hjobWord hjobFields hready.hblank hready.hsaved hready.htmp hsource hready.hloopSaved

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
