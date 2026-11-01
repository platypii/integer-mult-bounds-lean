module
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassBanks
/-! The complete class lifecycle runs from ordinary shared bank inputs.
All static register and per-call staged readiness obligations are derived. -/
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
theorem classRun_exec (b : RawRecoveryProgramBounds Q A U)
    (jobs : List (PackedNormalizedJob A s)) (wl : List (Fin (A+4)))
    (hwl : ∀ r ∈ jobs, wl.length = r.Bcore)
    (V Cprog reserve depth : ℕ)
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
    (h37 : (S.R (geometry bank 37)).length = V)
    (hs : S.R (geometry bank 32) = binSyms V s) (hw : S.R (geometry bank 33) = binSyms V coreWidth)
    (hr : S.R (geometry bank 34) = binSyms V radius) (hH : S.R (geometry bank 35) = binSyms V H) (hz : S.R (geometry bank 36) = [])
    (htable : ∀ k : Fin 117, k.val < 31 → S.R (geometry bank k) = [])
    (h104 : S.R (geometry bank 104) = []) (h106 : S.R (geometry bank 106) = []) (h116 : S.R (geometry bank 116) = [])
    (hN : (S.R (plan bank hinj).replicas).length = N) (hhalo : (S.R (control bank .halo)).length = H) (hW : (S.R (plan bank hinj).packet).length = W)
    (hprepBlank : ∀ k ∈ [(control bank .symbols),(control bank .count),(control bank .prepSaved),(control bank .prepTmp)], S.R k = [])
    (hwidth : (S.R (control bank .width)).length = V) (hjobHalo : ∀ r ∈ jobs, H = r.b-r.a)
    (hreaderBlank : ∀ k ∈ [(control bank .binary),(plan bank hinj).master.parameters 6,(plan bank hinj).master.parameters 7,
      (control bank .endpointWork),(control bank .endpointSaved),(control bank .endpointTmp)], S.R k = [])
    (hp : ∀ r ∈ jobs, (S.R (recovery bank (.control .precision))).length = r.p)
    (hparameters : ∀ r ∈ jobs, ∀ i : Fin 8, i ≠ 6 → i ≠ 7 →
      (S.R (recovery bank (.parameter i))).length = r.masterInput.values i)
    (hscalarWidth : S.R (recovery bank (.scalar .wr)) = wl)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (recovery bank (.scalar i)) = [])
    (hmasters : ∀ i, S.R (recovery bank (.master i)) = [])
    (hcontrols : ∀ i, i ∉ RecoveryBanks.liveControls → S.R (recovery bank (.control i)) = [])
    (hleft : ∀ i, S.L (recovery bank (.work i)) = [])
    (hoffset : ∀ r ∈ jobs, (S.R (recovery bank (.control .cropOffset))).length = r.radius)
    (hrows : ∀ r ∈ jobs, (S.R (recovery bank (.control .cropRows))).length = coreLength s r.coreWidth r.k)
    (hjobWord : ∀ r ∈ jobs, W = r.W) (hjobFields : ∀ r ∈ jobs, N = r.Fs.length)
    (hblank : ∀ i, S.R ((plan bank hinj).work i) = []) (hsaved : S.R (control bank .saved) = []) (htmp : S.R (control bank .tmp) = [])
    (hsource : S.R (control bank .source) = jobs.flatMap routedPayload++tail) (hloopSaved : S.R (control bank .loopSaved) = []) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (preparedCoreOriginsCost V s coreWidth radius H+recoveryPayloadCountCost N H W)+
        ((jobs.map ((plan bank hinj).coreTimeCost b V)).sum+5*jobs.length+4)+(2*(jobs.length+N*(H*W))+5) ∧
      List.Forall₂ PackedNormalizedJob.output jobs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((3*preparedCoreOriginsCost V s coreWidth radius H+2*recoveryPayloadCountCost N H W)+reserve)) depth
        ((plan bank hinj).classRun b (normalize bank hinj) (queue bank hinj) (crop bank hinj) (link bank hinj) (geometry bank) (control bank .symbols) (control bank .prepSaved) (control bank .prepTmp) (control bank .width) (control bank .halo) (control bank .binary) (control bank .endpointWork)
          (control bank .endpointSaved) (control bank .endpointTmp) (control bank .count) (control bank .source) (control bank .saved) (control bank .tmp) (control bank .loopSaved)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (control bank .source) tail) (plan bank hinj).result
          (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  have hoff : ∀ k, (plan bank hinj).scanSupport (normalize bank hinj) (queue bank hinj) (crop bank hinj)
      (control bank .width) (control bank .halo) (control bank .binary) (control bank .endpointWork)
      (control bank .endpointSaved) (control bank .endpointTmp) (control bank .count)
      (control bank .saved) (control bank .tmp) k →
      k ≠ geometry bank 116 ∧ k ≠ control bank .loopSaved ∧ k ≠ geometry bank 109 ∧
        k ≠ control bank .source ∧ k ≠ (plan bank hinj).result := by
    intro k hk
    rcases hk with hk | hk
    · have hresult : k ≠ (plan bank hinj).result := by
        intro h; subst k
        exact ComputedRecoveryPlan.localSupport_result (plan bank hinj) (normalize bank hinj)
          (queue bank hinj) (crop bank hinj) (link bank hinj) rfl hk
      obtain ⟨i,rfl⟩ := localSupport_range bank hinj k hk
      exact ⟨by simp [recovery,geometry,hinj.eq_iff], by simp [recovery,control,hinj.eq_iff],
        by simp [recovery,geometry,hinj.eq_iff], by simp [recovery,control,hinj.eq_iff],hresult⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,geometry,control,hinj.eq_iff]
  have hready (r : PackedNormalizedJob A s) (hr : r ∈ jobs) :=
    RecoveryBanks.stagedReady (recovery bank) (recovery_injective bank hinj) r wl S
      (control bank .source) (geometry bank 109) [] []
      (by intro i; simp [control,recovery,hinj.eq_iff])
      (by intro i; simp [geometry,recovery,hinj.eq_iff])
      (hp r hr) (hW.trans (hjobWord r hr)) (hN.trans (hjobFields r hr))
      (hparameters r hr) hscalarWidth hscalar hmasters hcontrols hblank hleft (hoffset r hr) (hrows r hr)
  exact ComputedRecoveryPlan.classRun_sum_exec (body := body) (plan bank hinj) b
    (normalize bank hinj) (queue bank hinj) (crop bank hinj) (link bank hinj) rfl
    (RecoveryBanks.normalize_support_masters _ _) (RecoveryBanks.normalize_support_payload _ _)
    (by simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,hinj.eq_iff]) (by simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,hinj.eq_iff])
    jobs wl hwl
    (control bank .width) (control bank .halo) (geometry bank 109) (control bank .binary)
    (control bank .endpointWork) (control bank .endpointSaved) (control bank .endpointTmp)
    (control bank .count) (control bank .source) (control bank .saved) (control bank .tmp)
    (geometry bank 116) (control bank .loopSaved)
    (by simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,geometry,control,hinj.eq_iff]) (by simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,control,hinj.eq_iff]) (by simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,geometry,control,hinj.eq_iff]) (by simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,geometry,control,hinj.eq_iff])
    hoff (by intro i; simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,control,hinj.eq_iff]) (by intro i; simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,geometry,hinj.eq_iff])
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,geometry,control,hinj.eq_iff])
    (by simp [plan,crop,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,hinj.eq_iff,RecoveryBanks.crop_ports]) (by simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,hinj.eq_iff])
    (by simp [plan,crop,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,hinj.eq_iff,RecoveryBanks.crop_ports])
    V Cprog reserve depth hfit hstock hpush hbody (geometry bank) (geometry_injective bank hinj) rfl rfl
    (control bank .symbols) (control bank .prepSaved) (control bank .prepTmp)
    (by simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,control,hinj.eq_iff])
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,geometry,control,hinj.eq_iff])
    (by simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,geometry,control,hinj.eq_iff]) (localSupport_external bank hinj .count)
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery,geometry,control,hinj.eq_iff])
    coreWidth radius H N W hcoreWidth hwide hHfit hA hV hlen horiginJobs hvolume
    v S tail h37 hs hw hr hH hz htable h104 h106 h116 hN hhalo hW hprepBlank
    hwidth hjobHalo hreaderBlank hready hblank hsaved htmp hsource hloopSaved
end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
