module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedInputClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonClassInputValues
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreJobQueues
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonCoreJob

/-! Consume the ordered R4 core stream using the actual common-core numerical
jobs. Queue, geometry, common headers and replica order follow from the same
job constructors as the verified single-axis caller. No supplier trace is assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
namespace ComputedClassBanks
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}
  (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
open ComputedRecoveryPlan (routedPayload)

theorem routedCommonCoreClassRun_exec (b : RawRecoveryProgramBounds Q A U)
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
    (count src saved tmp : Fin T)
    (hreg : [count,src,saved,tmp,control bank .source].Nodup)
    (borrowed : List (Fin (A+4)))
    (hsource : S.R src = coreSupplierStream A width radius L W Fs.reverse++borrowed)
    (hcount : (S.R count).length = (coreSupplierStream A width radius L W Fs.reverse).length)
    (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hsrcBank : ∀ k, src ≠ bank k) (hsrcTable : ∀ r, src ≠ rg r)
    (htransferPush : mnProgPush (installRoutedClassInput (P := P) (Q := Q) (A := A) (U := U) bank count src saved tmp) ≤ Cprog)
    (hready : InputReady bank hinj rg B D s width radius L st S),
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ 6*(coreSupplierStream A width radius L W Fs.reverse).length+6+
        inputClassTimeCost bank hinj b (List.ofFn jobs) B D st width radius L Fs.length W ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        max ((Cprog+1)*(6*(coreSupplierStream A width radius L W Fs.reverse).length+6))
          (inputClassWorkspace bank s B D st width radius L Fs.length W reserve)) depth
        (.seq (installRoutedClassInput bank count src saved tmp) (inputClassProgram bank hinj b rg))
        (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src borrowed)
          (plan bank hinj).result (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  intro B W radius indices jobs st D Cprog reserve depth rg hrg hoff hfitValues hstock hpush hbody
    hcoreWidth hwide hHfit hA hB v S count src saved tmp hreg borrowed hsource hcount
    hsaved htmp hsrcBank hsrcTable htransferPush hready
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
  have hstream : (List.ofFn jobs).flatMap routedPayload =
      coreSupplierStream A width radius L W Fs.reverse := hpayload
  rw [←hstream]
  apply routedInputClassRun_exec bank hinj b (List.ofFn jobs) B D Cprog reserve depth rg hrg hoff st hfitValues
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
    count src saved tmp hreg borrowed
    (by rw [hstream]; exact hsource)
    (by rw [hstream]; exact hcount)
    hsaved htmp hsrcBank hsrcTable htransferPush hready

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
