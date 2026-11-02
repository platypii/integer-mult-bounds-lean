module
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassBankRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassInput
/-! Generate shared class inputs from a retained binary dimension table, execute
the actual restoring class, and erase only the generated input counters. -/
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
noncomputable def inputClassProgram (b : RawRecoveryProgramBounds Q A U) (rg : TblR 12 → Fin T) : Pr P T Q A U :=
  .seq (inputProgram bank rg)
    (.seq ((plan bank hinj).classRun b (normalize bank hinj) (queue bank hinj) (crop bank hinj) (link bank hinj)
      (geometry bank) (control bank .symbols) (control bank .prepSaved) (control bank .prepTmp)
      (control bank .width) (control bank .halo) (control bank .binary) (control bank .endpointWork)
      (control bank .endpointSaved) (control bank .endpointTmp) (control bank .count) (control bank .source)
      (control bank .saved) (control bank .tmp) (control bank .loopSaved)) (clearWords (inputRegisters bank)))

theorem inputClassRun_exec (b : RawRecoveryProgramBounds Q A U)
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
    (hs : S.R (geometry bank 32) = binSyms V s) (hw : S.R (geometry bank 33) = binSyms V coreWidth)
    (hr : S.R (geometry bank 34) = binSyms V radius) (hH : S.R (geometry bank 35) = binSyms V H) (hz : S.R (geometry bank 36) = [])
    (htable : ∀ k : Fin 117, k.val < 31 → S.R (geometry bank k) = [])
    (h104 : S.R (geometry bank 104) = []) (h106 : S.R (geometry bank 106) = []) (h116 : S.R (geometry bank 116) = [])
    (hprepBlank : ∀ k ∈ [(control bank .symbols),(control bank .count),(control bank .prepSaved),(control bank .prepTmp)], S.R k = [])
     (hjobHalo : ∀ r ∈ jobs, H = r.b-r.a)
    (hreaderBlank : ∀ k ∈ [(control bank .binary),(plan bank hinj).master.parameters 6,(plan bank hinj).master.parameters 7,
      (control bank .endpointWork),(control bank .endpointSaved),(control bank .endpointTmp)], S.R k = [])
    (hinput : tblHolds rg S (tblRho D (List.replicate D tick) [] st))
    (hinputBlank : ∀ k ∈ inputRegisters bank, S.R k = [])
    (hvalues : st.val 6 = V ∧ st.val 7 = W ∧ st.val 8 = N ∧ st.val 9 = radius ∧ st.val 11 = H)
    (hprecision : ∀ r ∈ jobs, st.val 0 = r.p)
    (hparameters : ∀ r ∈ jobs, ∀ i : Fin 6,
      st.val (Fin.castLE (by decide : 6 ≤ 12) i) = r.masterInput.values (Fin.castLE (by decide : 6 ≤ 8) i))
    (hjobRadius : ∀ r ∈ jobs, radius = r.radius)
    (hjobRows : ∀ r ∈ jobs, st.val 10 = coreLength s r.coreWidth r.k)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (recovery bank (.scalar i)) = [])
    (hmasters : ∀ i, S.R (recovery bank (.master i)) = [])
    (hcontrols : ∀ i, i ∉ RecoveryBanks.liveControls → S.R (recovery bank (.control i)) = [])
    (hleft : ∀ i, S.L (recovery bank (.work i)) = [])
    (hjobWord : ∀ r ∈ jobs, W = r.W) (hjobFields : ∀ r ∈ jobs, N = r.Fs.length)
    (hblank : ∀ i, S.R ((plan bank hinj).work i) = []) (hsaved : S.R (control bank .saved) = []) (htmp : S.R (control bank .tmp) = [])
    (hsource : S.R (control bank .source) = jobs.flatMap routedPayload++tail) (hloopSaved : S.R (control bank .loopSaved) = []) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ unaryCopiesCost D st.val (inputCopies bank)+((preparedCoreOriginsCost V s coreWidth radius H+recoveryPayloadCountCost N H W)+
        ((jobs.map ((plan bank hinj).coreTimeCost b V)).sum+5*jobs.length+4)+(2*(jobs.length+N*(H*W))+5))+(2*inputVolume st.val+2*(inputRegisters bank).length+1) ∧
      List.Forall₂ PackedNormalizedJob.output jobs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (3*unaryCopiesCost D st.val (inputCopies bank)+(((3*preparedCoreOriginsCost V s coreWidth radius H+2*recoveryPayloadCountCost N H W)+reserve)+3*(2*inputVolume st.val+2*(inputRegisters bank).length+1)))) depth
        (inputClassProgram bank hinj b rg) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (control bank .source) tail) (plan bank hinj).result
          (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  let F := inputState bank st.val S
  have hat (p : Fin 12 × ComputedClassBank) (hp : p ∈ inputAssignments) :
      F.R (bank p.2) = List.replicate (st.val p.1) tick := inputState_at bank hinj st.val S hinputBlank p hp
  have hpar (i : Fin 6) : F.R (bank (.recovery (.parameter (Fin.castLE (by decide : 6 ≤ 8) i)))) =
      List.replicate (st.val (Fin.castLE (by decide : 6 ≤ 12) i)) tick :=
    inputState_parameter bank hinj st.val S hinputBlank i
  have hstable (k : ComputedClassBank) (hk : k ∉ inputAssignments.map Prod.snd) : F.R (bank k) = S.R (bank k) :=
    inputState_off bank st.val S _ (inputRegisters_off bank hinj k hk)
  obtain ⟨hB,hWord,hReplicas,hRadius,hHalo⟩ := hvalues
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := input_exec (body := body) bank rg hrg hoff D (List.replicate D tick) [] st hfitValues v S hinput depth
  obtain ⟨v₂,n₂,outputs,hu₂,hn₂,houtputs,he₂⟩ := classRun_exec (body := body) bank hinj b jobs
    (List.replicate V tick) (by intro r hr; simpa only [List.length_replicate] using hwl r hr)
    V Cprog reserve depth hfit hstock hpush hbody coreWidth radius H N W hcoreWidth hwide hHfit hA hV
    hlen horiginJobs hvolume v₁ F tail
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hat (6,.geometry 37) (by simp [inputAssignments]),List.length_replicate]; exact hB)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.geometry 32) (by simp [inputAssignments])]; exact hs)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.geometry 33) (by simp [inputAssignments])]; exact hw)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.geometry 34) (by simp [inputAssignments])]; exact hr)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.geometry 35) (by simp [inputAssignments])]; exact hH)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.geometry 36) (by simp [inputAssignments])]; exact hz)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        intro k hk
        have hne : k ≠ 37 := by intro he; rw [he] at hk; norm_num at hk
        rw [hstable (.geometry k) (by simpa [inputAssignments] using hne)]
        exact htable k hk)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.geometry 104) (by simp [inputAssignments])]; exact h104)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.geometry 106) (by simp [inputAssignments])]; exact h106)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.geometry 116) (by simp [inputAssignments])]; exact h116)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hat (8,.recovery (.control .replicas)) (by simp [inputAssignments]),List.length_replicate]; exact hReplicas)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hat (11,.control .halo) (by simp [inputAssignments]),List.length_replicate]; exact hHalo)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hat (7,.recovery (.control .packet)) (by simp [inputAssignments]),List.length_replicate]; exact hWord)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        · rw [hstable (.control .symbols) (by simp [inputAssignments])]; exact hprepBlank _ (by simp [control])
        · rw [hstable (.control .count) (by simp [inputAssignments])]; exact hprepBlank _ (by simp [control])
        · rw [hstable (.control .prepSaved) (by simp [inputAssignments])]; exact hprepBlank _ (by simp [control])
        · rw [hstable (.control .prepTmp) (by simp [inputAssignments])]; exact hprepBlank _ (by simp [control]))
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hat (6,.control .width) (by simp [inputAssignments]),List.length_replicate]; exact hB)
    hjobHalo
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hstable (.control .binary) (by simp [inputAssignments])]; exact hreaderBlank _ (by simp [control,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery])
        · rw [hstable (.recovery (.parameter 6)) (by simp [inputAssignments])]; exact hreaderBlank _ (by simp [control,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery])
        · rw [hstable (.recovery (.parameter 7)) (by simp [inputAssignments])]; exact hreaderBlank _ (by simp [control,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery])
        · rw [hstable (.control .endpointWork) (by simp [inputAssignments])]; exact hreaderBlank _ (by simp [control,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery])
        · rw [hstable (.control .endpointSaved) (by simp [inputAssignments])]; exact hreaderBlank _ (by simp [control,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery])
        · rw [hstable (.control .endpointTmp) (by simp [inputAssignments])]; exact hreaderBlank _ (by simp [control,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan,recovery]))
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        intro r hr
        rw [hat (0,.recovery (.control .precision)) (by simp [inputAssignments]),List.length_replicate]
        exact hprecision r hr)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        intro r hr i ha hb
        obtain ⟨j,rfl⟩ := parameter_prefix i ha hb
        rw [hpar j,List.length_replicate]
        exact hparameters r hr j)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hat (6,.recovery (.scalar .wr)) (by simp [inputAssignments]),hB])
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        intro i hi
        rw [hstable (.recovery (.scalar i)) (by simp [inputAssignments,hi])]; exact hscalar i hi)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        intro i; rw [hstable (.recovery (.master i)) (by simp [inputAssignments])]; exact hmasters i)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        intro i hi
        rw [hstable (.recovery (.control i)) (by
          simp [RecoveryBanks.liveControls] at hi
          simp [inputAssignments,hi])]; exact hcontrols i hi)
    hleft
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        intro r hr
        rw [hat (9,.recovery (.control .cropOffset)) (by simp [inputAssignments]),List.length_replicate,hRadius]
        exact hjobRadius r hr)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        intro r hr
        rw [hat (10,.recovery (.control .cropRows)) (by simp [inputAssignments]),List.length_replicate]
        exact hjobRows r hr)
    hjobWord hjobFields
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        intro i; rw [hstable (.recovery (.work i)) (by simp [inputAssignments])]; exact hblank i)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.control .saved) (by simp [inputAssignments])]; exact hsaved)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.control .tmp) (by simp [inputAssignments])]; exact htmp)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.control .source) (by simp [inputAssignments])]; exact hsource)
    (by dsimp only [geometry,control,recovery,plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]
        rw [hstable (.control .loopSaved) (by simp [inputAssignments])]; exact hloopSaved)
  have hsourceOff : control bank .source ∉ inputRegisters bank :=
    inputRegisters_off bank hinj _ (by simp [inputAssignments])
  have hresultOff : (plan bank hinj).result ∉ inputRegisters bank :=
    inputRegisters_off bank hinj _ (by simp [inputAssignments])
  obtain ⟨v₃,hu₃,he₃⟩ := input_release_output_exec (body := body) bank hinj st.val S hinputBlank
    (control bank .source) (plan bank hinj).result tail outputs.reverse.flatten hsourceOff hresultOff v₂ depth
  refine ⟨v₃,n₁+(n₂+(2*inputVolume st.val+2*(inputRegisters bank).length+1)),outputs,
    hu₃.trans (hu₂.trans hu₁),?_,houtputs,?_⟩
  · omega
  · simpa only [inputClassProgram] using mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃)

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
