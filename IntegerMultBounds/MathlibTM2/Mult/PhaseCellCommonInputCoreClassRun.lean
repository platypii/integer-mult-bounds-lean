module
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputComputedClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonClassInputValues
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreJobQueues
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonCoreJob
/-! Proper-core geometry and the common job constructor derive every shared
input profile and queue fact for the actual class execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
namespace ComputedClassBanks
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}
  (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
open ComputedRecoveryPlan (routedPayload)
theorem commonInputCoreClassRun_exec (b : RawRecoveryProgramBounds Q A U)
    (p u l target t width L : ℕ) (α gap : ℝ) (C : ZMod s → GaussianInt)
    (V : Fin (coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) L).length → ℕ)
    (bounds : ∀ j, let k := (coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) L)[j.val]
      PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target+1) (rhsExp := 2)
        (a := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target)).1)
        (b := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target)).2) (V := V j) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    let B := inverseCallerWordWidth p u l target s t
    let W := packedHaloCommonWidth p l s u (target+1) 2
    let radius := localityDepth p target*PhaseCellBand.width p u
    let indices := coreGatherIndices s width radius L
    let jobs := fun j : Fin indices.length => PackedNormalizedJob.ofCoreCommon (A := A)
      p u l target t width indices[j.val] (V j) α gap C Fs (bounds j) hF
    let st : TblSt 12 A := ⟨commonInputValues p u l target s t B W Fs.length radius L,[]⟩
    ∀     (D Cprog reserve depth : ℕ)
    (rg : TblR 12 → Fin T) (hrg : Function.Injective rg) (hoff : ∀ r k, rg r ≠ bank k)
     (hfitValues : ∀ i, st.val i < 2^D)
    
    
    (hstock : ∀ r ∈ (List.ofFn jobs), (plan bank hinj).coreStock b B r Cprog ≤ reserve)
    (hpush : mnProgPush (descriptorSolverSchedule (plan bank hinj).src (plan bank hinj).saved (plan bank hinj).tmp (plan bank hinj).clock (plan bank hinj).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
        (plan bank hinj).work (plan bank hinj).src (plan bank hinj).saved (plan bank hinj).count (plan bank hinj).tmp (plan bank hinj).spare (plan bank hinj).result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (hcoreWidth : 0 < width) (hwide : s+width+2*radius < 2^B)
    (hHfit : L < 2^B) (hA : 4 ≤ A) (hV : 0 < B)
    
    
    
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (hs : S.R (geometry bank 32) = binSyms B s) (hw : S.R (geometry bank 33) = binSyms B width)
    (hr : S.R (geometry bank 34) = binSyms B radius) (hH : S.R (geometry bank 35) = binSyms B L) (hz : S.R (geometry bank 36) = [])
    (htable : ∀ k : Fin 117, k.val < 31 → S.R (geometry bank k) = [])
    (h104 : S.R (geometry bank 104) = []) (h106 : S.R (geometry bank 106) = []) (h116 : S.R (geometry bank 116) = [])
    (hprepBlank : ∀ k ∈ [(control bank .symbols),(control bank .count),(control bank .prepSaved),(control bank .prepTmp)], S.R k = [])
     
    (hreaderBlank : ∀ k ∈ [(control bank .binary),(plan bank hinj).master.parameters 6,(plan bank hinj).master.parameters 7,
      (control bank .endpointWork),(control bank .endpointSaved),(control bank .endpointTmp)], S.R k = [])
    (hinput : tblHolds rg S (tblRho D (List.replicate D tick) [] st))
    (hinputBlank : ∀ k ∈ inputRegisters bank, S.R k = [])
    
    
    
    
    
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (recovery bank (.scalar i)) = [])
    (hmasters : ∀ i, S.R (recovery bank (.master i)) = [])
    (hcontrols : ∀ i, i ∉ RecoveryBanks.liveControls → S.R (recovery bank (.control i)) = [])
    (hleft : ∀ i, S.L (recovery bank (.work i)) = [])
     
    (hblank : ∀ i, S.R ((plan bank hinj).work i) = []) (hsaved : S.R (control bank .saved) = []) (htmp : S.R (control bank .tmp) = [])
    (hsource : S.R (control bank .source) = coreSupplierStream A width radius L W Fs++tail) (hloopSaved : S.R (control bank .loopSaved) = []),
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ unaryCopiesCost D st.val (inputCopies bank)+((preparedCoreOriginsCost B s width radius L+recoveryPayloadCountCost Fs.length L W)+
        (((List.ofFn jobs).map ((plan bank hinj).coreTimeCost b B)).sum+5*(List.ofFn jobs).length+4)+(2*((List.ofFn jobs).length+Fs.length*(L*W))+5))+(2*inputVolume st.val+2*(inputRegisters bank).length+1) ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (3*unaryCopiesCost D st.val (inputCopies bank)+(((3*preparedCoreOriginsCost B s width radius L+2*recoveryPayloadCountCost Fs.length L W)+reserve)+3*(2*inputVolume st.val+2*(inputRegisters bank).length+1)))) depth
        (inputClassProgram bank hinj b rg) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (control bank .source) tail) (plan bank hinj).result
          (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  intro B W radius indices jobs st D Cprog reserve depth rg hrg hoff hfitValues hstock hpush hbody
    hcoreWidth hwide hHfit hA hB v S tail hs hw hr hH hz htable h104 h106 h116 hprepBlank
    hreaderBlank hinput hinputBlank hscalar hmasters hcontrols hleft hblank hsaved htmp hsource hloopSaved
  have hwidthJob : ∀ i : Fin indices.length, (jobs i).coreWidth = width := fun _ => rfl
  have hk : ∀ i : Fin indices.length, (jobs i).k = indices[i.val]'i.isLt := fun _ => rfl
  have hradius : ∀ i : Fin indices.length, (jobs i).radius = radius := fun _ => rfl
  have hword : ∀ i : Fin indices.length, (jobs i).W = W := fun _ => rfl
  have hFs : ∀ i : Fin indices.length, (jobs i).Fs = Fs := fun _ => rfl
  have hlength (i : Fin indices.length) : (jobs i).b-(jobs i).a = L := by
    have hg := (coreGatherIndices_spec s width radius L (jobs i).k
      (by rw [hk i]; exact List.getElem_mem i.isLt)).2.2
    have hh := (jobs i).haloLength
    rw [hwidthJob i,hradius i] at hh
    exact hh.trans hg
  have horigin := coreJobs_origins width radius L B jobs hwidthJob hradius hk
  have hpayload := coreJobs_payloads width radius L W Fs jobs hwidthJob hradius hk hword hFs
  have hvolume := coreJobs_payload_length width radius L W Fs jobs hwidthJob hradius hk hword hFs
  have hcoreLength := coreJobs_core_length width radius L jobs hwidthJob hk
  apply inputClassRun_exec bank hinj b (List.ofFn jobs) B D Cprog reserve depth rg hrg hoff st hfitValues
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; rfl)
    (by intro r hr; have := r.bounds.hab; have := r.bounds.hbs; omega)
    hstock hpush hbody width radius L Fs.length W hcoreWidth hwide hHfit hA hB
    (List.length_ofFn) horigin
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
        simpa only [ComputedRecoveryPlan.routedPayload,PackedNormalizedJob.inputPayload,Nat.mul_assoc] using hvolume i)
    v S tail hs hw hr hH hz htable h104 h106 h116 hprepBlank
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact (hlength i).symm)
    hreaderBlank hinput hinputBlank
    (by simp [st,commonInputValues,Matrix.vecAppend_eq_ite])
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
        change commonInputValues p u l target s t B W Fs.length radius L 0 = p
        simp [commonInputValues])
    (by intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
        intro i
        change commonInputValues p u l target s t B W Fs.length radius L _ = _
        rw [commonInputValues_prefix,masterInput_prefix]; rfl)
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; rfl)
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
        change commonInputValues p u l target s t B W Fs.length radius L 10 = _
        simpa [commonInputValues,Matrix.vecAppend_eq_ite] using (hcoreLength i).symm)
    hscalar hmasters hcontrols hleft
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact (hword i).symm)
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; rw [hFs i])
    hblank hsaved htmp
    (by change S.R (control bank .source) = (List.ofFn jobs).flatMap PackedNormalizedJob.inputPayload++tail
        exact hsource.trans (congrArg (fun xs => xs++tail) hpayload.symm)) hloopSaved

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
