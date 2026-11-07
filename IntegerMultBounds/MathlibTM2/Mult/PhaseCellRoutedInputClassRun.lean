module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedClassInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadyInputClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedClassStock

/-! Execute the numerical class from an owned R4 output prefix. The actual
handoff consumes that external prefix, preserves its borrowed suffix, and
shares peak workspace with the computed numerical class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
namespace ComputedClassBanks
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}
  (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
open ComputedRecoveryPlan (routedPayload)

noncomputable def inputClassTimeCost (b : RawRecoveryProgramBounds Q A U)
    (jobs : List (PackedNormalizedJob A s)) (V D : ℕ) (st : TblSt 12 A)
    (width radius H N W : ℕ) : ℕ :=
  unaryCopiesCost D st.val (inputCopies bank)+
    ((preparedCoreOriginsCost V s width radius H+recoveryPayloadCountCost N H W)+
      ((jobs.map ((plan bank hinj).coreTimeCost b V)).sum+5*jobs.length+4)+
      (2*(jobs.length+N*(H*W))+5))+(2*inputVolume st.val+2*(inputRegisters bank).length+1)

def inputClassWorkspace (s V D : ℕ) (st : TblSt 12 A) (width radius H N W reserve : ℕ) : ℕ :=
  3*unaryCopiesCost D st.val (inputCopies bank)+
    (((3*preparedCoreOriginsCost V s width radius H+2*recoveryPayloadCountCost N H W)+reserve)+
      3*(2*inputVolume st.val+2*(inputRegisters bank).length+1))

theorem routedInputClassRun_exec (b : RawRecoveryProgramBounds Q A U)
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
    (v : HS T Q A U) (S : Stacks T A)
     (hjobHalo : ∀ r ∈ jobs, H = r.b-r.a)
    (hvalues : st.val 6 = V ∧ st.val 7 = W ∧ st.val 8 = N ∧ st.val 9 = radius ∧ st.val 11 = H)
    (hprecision : ∀ r ∈ jobs, st.val 0 = r.p)
    (hparameters : ∀ r ∈ jobs, ∀ i : Fin 6,
      st.val (Fin.castLE (by decide : 6 ≤ 12) i) = r.masterInput.values (Fin.castLE (by decide : 6 ≤ 8) i))
    (hjobRadius : ∀ r ∈ jobs, radius = r.radius)
    (hjobRows : ∀ r ∈ jobs, st.val 10 = coreLength s r.coreWidth r.k)
    (hjobWord : ∀ r ∈ jobs, W = r.W) (hjobFields : ∀ r ∈ jobs, N = r.Fs.length)
    (count src saved tmp : Fin T)
    (hreg : [count,src,saved,tmp,control bank .source].Nodup)
    (borrowed : List (Fin (A+4)))
    (hsource : S.R src = jobs.flatMap routedPayload++borrowed)
    (hcount : (S.R count).length = (jobs.flatMap routedPayload).length)
    (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hsrcBank : ∀ k, src ≠ bank k) (hsrcTable : ∀ r, src ≠ rg r)
    (htransferPush : mnProgPush (installRoutedClassInput (P := P) (Q := Q) (A := A) (U := U) bank count src saved tmp) ≤ Cprog)
    (hready : InputReady bank hinj rg V D s coreWidth radius H st S) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ 6*(jobs.flatMap routedPayload).length+6+
        inputClassTimeCost bank hinj b jobs V D st coreWidth radius H N W ∧
      List.Forall₂ PackedNormalizedJob.output jobs outputs ∧
      mnSize (mk v' {S with R := (Function.update (Function.update S.R src borrowed)
        (plan bank hinj).result (outputs.reverse.flatten++S.R (plan bank hinj).result))}) ≤ mnSize (mk v S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        max ((Cprog+1)*(6*(jobs.flatMap routedPayload).length+6))
          (inputClassWorkspace bank s V D st coreWidth radius H N W reserve)) depth
        (.seq (installRoutedClassInput bank count src saved tmp) (inputClassProgram bank hinj b rg))
        (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src borrowed)
          (plan bank hinj).result (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  let payload := jobs.flatMap routedPayload
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R src borrowed)
    (control bank .source) (payload++S.R (control bank .source)))}
  obtain ⟨v₁,hu₁,hreadyM,hsize,he₁,hcert⟩ := installRoutedClassInput_exec_of_ready
    bank hinj rg V D s coreWidth radius H st count src saved tmp hreg payload borrowed v S
    hready hsource hcount hsaved htmp hsrcBank hsrcTable (fun r => hoff r (.control .source))
  obtain ⟨v₂,n₂,outputs,hu₂,hn₂,houtputs,he₂⟩ := inputClassRun_exec_of_ready (body := body)
    bank hinj b jobs V D Cprog reserve depth rg hrg hoff st hfitValues hwl hfit hstock hpush hbody
    coreWidth radius H N W hcoreWidth hwide hHfit hA hV hlen horiginJobs hvolume v₁ M (S.R (control bank .source))
    hjobHalo hvalues hprecision hparameters hjobRadius hjobRows hjobWord hjobFields hreadyM
    (by simp [M,payload])
  have hn : n₂ ≤ inputClassTimeCost bank hinj b jobs V D st coreWidth radius H N W := hn₂
  let reserve₁ := (Cprog+1)*(6*payload.length+6)
  let reserve₂ := inputClassWorkspace bank s V D st coreWidth radius H N W reserve
  have ht₁ := (hcert Cprog htransferPush hbody depth).mono (by
    intro d z hz
    exact hz.trans (Nat.add_le_add_left (Nat.le_max_left reserve₁ reserve₂) _))
  have ht₂ := he₂.mono (by
    intro d z hz
    change mnSize z+d ≤ mnSize (mk v₁ M)+depth+reserve₂ at hz
    rw [hsize] at hz
    exact hz.trans (Nat.add_le_add_left (Nat.le_max_right reserve₁ reserve₂) _))
  have hne : control bank .source ≠ (plan bank hinj).result := by
    simp [control,plan,RecoveryBanks.plan,recovery,hinj.eq_iff]
  have hsrcSource : control bank .source ≠ src := (hsrcBank (.control .source)).symm
  have hsrcResult : (plan bank hinj).result ≠ src := by
    simpa only [plan,RecoveryBanks.plan,recovery] using (hsrcBank (.recovery (.control .result))).symm
  have hend : {M with R := (Function.update (Function.update M.R (control bank .source) (S.R (control bank .source)))
      (plan bank hinj).result (outputs.reverse.flatten++M.R (plan bank hinj).result))} =
      {S with R := (Function.update (Function.update S.R src borrowed)
        (plan bank hinj).result (outputs.reverse.flatten++S.R (plan bank hinj).result))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hr : k = (plan bank hinj).result
    · subst k; simp [M,hne.symm,hsrcResult]
    by_cases hs : k = control bank .source
    · subst k; simp [M,hr,hsrcSource]
    · simp [M,hr,hs]
  refine ⟨v₂,(6*payload.length+6)+n₂,outputs,hu₂.trans hu₁,Nat.add_le_add_left hn _,houtputs,
    routedClass_boundary_size_le bank hinj jobs outputs houtputs src borrowed v v₂ S hsource hsrcBank,?_⟩
  rw [hend] at ht₂
  exact ExecWithin.seq ht₁ ht₂

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
