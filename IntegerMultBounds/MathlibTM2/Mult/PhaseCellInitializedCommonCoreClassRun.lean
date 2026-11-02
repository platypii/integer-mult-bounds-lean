module
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCommonCoreClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedClassRun
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
theorem initializedPreparedCommonCoreClassRun_exec (b : RawRecoveryProgramBounds Q A U)
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
    (src : Fin 4 → Fin T) (hsrc : ∀ i k, src i ≠ bank k)
    (hs : S.R (src 0) = binSyms B s) (hw : S.R (src 1) = binSyms B width)
    (hr : S.R (src 2) = binSyms B radius) (hL : S.R (src 3) = binSyms B L)
    (prep : Pr P T Q A U) (prepTime prepStock : ℕ)
    (hsourceBlank : S.R (control bank .source) = [])
    (hprep : ∀ w : HS T Q A U, ∃ v' n, v'.user = w.user ∧ n ≤ prepTime ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk w (loadedClassGeometry bank src S))+depth+prepStock)
        depth prep (Host.mk w (loadedClassGeometry bank src S)) n
        (Host.mk v' {loadedClassGeometry bank src S with R := (Function.update (loadedClassGeometry bank src S).R (control bank .source)
          (coreSupplierStream A width radius L W Fs.reverse))}))
    (hinput : tblHolds rg S (tblRho D (List.replicate D tick) [] st))
    (hblank : ∀ i, i ≠ .control .source → S.R (bank i) = [])
    (hleft : ∀ i, S.L (recovery bank (.work i)) = []) ,
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (24*B+25)+((prepTime+(unaryCopiesCost D st.val (inputCopies bank)+((preparedCoreOriginsCost B s width radius L+recoveryPayloadCountCost Fs.length L W)+
        (((List.ofFn jobs).map ((plan bank hinj).coreTimeCost b B)).sum+5*(List.ofFn jobs).length+4)+(2*((List.ofFn jobs).length+Fs.length*(L*W))+5))+(2*inputVolume st.val+2*(inputRegisters bank).length+1)))+(8*B+9)) ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(2*(24*B+25)+
        (prepStock+(3*unaryCopiesCost D st.val (inputCopies bank)+(((3*preparedCoreOriginsCost B s width radius L+2*recoveryPayloadCountCost Fs.length L W)+reserve)+3*(2*inputVolume st.val+2*(inputRegisters bank).length+1)))))) depth
        (initializedClassProgram bank src (.seq prep (inputClassProgram bank hinj b rg))) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (plan bank hinj).result
          (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  intro B W radius indices jobs st D Cprog reserve depth rg hrg hoff hfitValues hstock hpush hbody
    hcoreWidth hwide hHfit hA hB v S src hsrc hs hw hr hL prep prepTime prepStock hsourceBlank hprep hinput hblank hleft
  have hwords : ∀ i, (S.R (src i)).length = B := by
    intro i
    fin_cases i
    · rw [show (⟨0,by decide⟩ : Fin 4) = 0 by decide, hs,length_binSyms]
    · rw [show (⟨1,by decide⟩ : Fin 4) = 1 by decide, hw,length_binSyms]
    · rw [show (⟨2,by decide⟩ : Fin 4) = 2 by decide, hr,length_binSyms]
    · rw [show (⟨3,by decide⟩ : Fin 4) = 3 by decide, hL,length_binSyms]
  have hready := loadedClassGeometry_ready bank hinj src rg hoff B D s width radius L st S
    hs hw hr hL hinput hblank hleft
  have hsource : (loadedClassGeometry bank src S).R (control bank .source) = [] := by
    change copyWordHeadersR S.R (classGeometryCopies bank src) S.R (control bank .source) = []
    rw [copyWordHeadersR_off S.R (classGeometryCopies bank src) S.R _ ?_]
    · exact hsourceBlank
    · intro r hr
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      simp [geometry,control,hinj.eq_iff]
  apply initializedClassRun_exec_within body bank hinj src hsrc B v S hblank hwords
    (.seq prep (inputClassProgram bank hinj b rg)) _ _ depth _
  intro w
  exact preparedCommonCoreClassRun_exec (body := body) bank hinj b p u l target t width L α gap C V bounds Fs hF
    D Cprog reserve depth rg hrg hoff hfitValues hstock hpush hbody hcoreWidth hwide hHfit hA hB
    w (loadedClassGeometry bank src S) prep prepTime prepStock hsource (hprep w) hready

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
