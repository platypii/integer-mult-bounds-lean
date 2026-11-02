module
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedInputClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonInputCoreClassRun
/-! Actual common-format proper-core jobs consume the physical ambient gather
stream with its explicit reversed replica order. -/
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
theorem preparedCommonCoreClassRun_exec (b : RawRecoveryProgramBounds Q A U)
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
      p u l target t width indices[j.val] (V j) α gap C Fs.reverse (bounds j)
        (by intro F hmem i; exact hF F (List.mem_reverse.mp hmem) i)
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
    (v : HS T Q A U) (S : Stacks T A) 
    (prep : Pr P T Q A U) (prepTime prepStock : ℕ)
    (hsourceBlank : S.R (control bank .source) = [])
    (hprep : ∃ v' n, v'.user = v.user ∧ n ≤ prepTime ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+prepStock)
        depth prep (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (control bank .source)
          (coreSupplierStream A width radius L W Fs.reverse))}))
    (hready : InputReady bank hinj rg B D s width radius L st S) ,
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ prepTime+(unaryCopiesCost D st.val (inputCopies bank)+((preparedCoreOriginsCost B s width radius L+recoveryPayloadCountCost Fs.length L W)+
        (((List.ofFn jobs).map ((plan bank hinj).coreTimeCost b B)).sum+5*(List.ofFn jobs).length+4)+(2*((List.ofFn jobs).length+Fs.length*(L*W))+5))+(2*inputVolume st.val+2*(inputRegisters bank).length+1)) ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (prepStock+(3*unaryCopiesCost D st.val (inputCopies bank)+(((3*preparedCoreOriginsCost B s width radius L+2*recoveryPayloadCountCost Fs.length L W)+reserve)+3*(2*inputVolume st.val+2*(inputRegisters bank).length+1))))) depth
        (.seq prep (inputClassProgram bank hinj b rg)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (plan bank hinj).result
          (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  intro B W radius indices jobs st D Cprog reserve depth rg hrg hoff hfitValues hstock hpush hbody
    hcoreWidth hwide hHfit hA hB v S prep prepTime prepStock hsourceBlank hprep hready
  have hwidthJob : ∀ i : Fin indices.length, (jobs i).coreWidth = width := fun _ => rfl
  have hk : ∀ i : Fin indices.length, (jobs i).k = indices[i.val]'i.isLt := fun _ => rfl
  have hradius : ∀ i : Fin indices.length, (jobs i).radius = radius := fun _ => rfl
  have hword : ∀ i : Fin indices.length, (jobs i).W = W := fun _ => rfl
  have hFs : ∀ i : Fin indices.length, (jobs i).Fs = Fs.reverse := fun _ => rfl
  have hlength (i : Fin indices.length) : (jobs i).b-(jobs i).a = L := by
    have hg := (coreGatherIndices_spec s width radius L (jobs i).k
      (by rw [hk i]; exact List.getElem_mem i.isLt)).2.2
    have hh := (jobs i).haloLength
    rw [hwidthJob i,hradius i] at hh
    exact hh.trans hg
  have horigin := coreJobs_origins width radius L B jobs hwidthJob hradius hk
  have hpayload := coreJobs_payloads width radius L W Fs.reverse jobs hwidthJob hradius hk hword hFs
  have hvolume := coreJobs_payload_length width radius L W Fs.reverse jobs hwidthJob hradius hk hword hFs
  have hcoreLength := coreJobs_core_length width radius L jobs hwidthJob hk
  apply preparedInputClassRun_exec bank hinj b (List.ofFn jobs) B D Cprog reserve depth rg hrg hoff st hfitValues
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; rfl)
    (by intro r hr; have := r.bounds.hab; have := r.bounds.hbs; omega)
    hstock hpush hbody width radius L Fs.length W hcoreWidth hwide hHfit hA hB
    (List.length_ofFn) horigin
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
        simpa only [ComputedRecoveryPlan.routedPayload,PackedNormalizedJob.inputPayload,Nat.mul_assoc,List.length_reverse] using hvolume i)
    v S
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact (hlength i).symm)
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
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact (hword i).symm)
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; rw [hFs i,List.length_reverse])
    prep prepTime prepStock hsourceBlank ?_ hready
  obtain ⟨v',n,hu,hn,he⟩ := hprep
  have hstream : (List.ofFn jobs).flatMap routedPayload =
      coreSupplierStream A width radius L W Fs.reverse := hpayload
  rw [←hstream] at he
  exact ⟨v',n,hu,hn,he⟩

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
