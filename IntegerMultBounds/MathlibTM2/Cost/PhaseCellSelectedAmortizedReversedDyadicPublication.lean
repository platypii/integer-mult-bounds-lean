module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedPlacedDyadicPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicPublicationReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreArchiveCopy
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPublicationHandoffBudget
public import IntegerMultBounds.MathlibTM2.Host.EmbedRightUpdatesStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPolynomialPublicationBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatherSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherPublicationClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreArchiveVolume
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellExactDyadicPublicationBudget

/-! Source-linear bounds for the same actual dyadic archive publication trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement PackedTranspose FixedStreamedBank
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
variable {T Q K : ℕ} {P U : Type}

theorem selectedAmortizedReversedDyadicPublication_exec (body : P → Pr P T Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (ct cV : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
    ∀ (e : Fin PackedTranspose.tapeCount → Fin T) (he : Function.Injective e),
    let p := Sizes.p m
    let s := Sizes.s m i
    ∀ (u target : ℕ) (htarget : target ≤ ct*p) (W : ℕ) (hW : 1 ≤ W) (b V : ℕ),
    V ≤ cV*p → 2^b ≤ Sizes.T m →
    let width := amortizedCoreWidth ct p
    let radius := localityDepth p target*PhaseCellBand.width p u
    let g := gatherPublicationClass s width radius (width+2*radius)
    let hw : 0 < width := (amortizedCoreWidth_bounds ct p u target (by have := h.thirteen_le_p; omega) htarget).1
    let a := Nat.clog 2 g.indices.length
    ∀
    (hbits : a+b < V) (hfit : (g.length*W)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (exponent packet pad tmp saved : Fin PackedTranspose.tapeCount)
    (hExponent : exponent = headerReg 51) (hPacket : packet = headerReg 82)
    (hpadReg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (Fs : List (ZMod s → GaussianInt)) (hFs : Fs.length = 2^b)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (batches : List (List (List GaussianInt)))
    (hrows : List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p W width k Fs J rows) (coreBulkIndices s width (PhaseCellBand.width p u) (localityDepth p target)) batches)
    (depth : ℕ)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (copyCount copySavedCount copyWidth source archive copySaved copyTmp : Fin T)
    (hcopyReg : [copyCount,copySavedCount,copyWidth,source,archive,e (extra 1),copySaved,copyTmp].Nodup)
    (hcopyCount : (S.R copyCount).length = g.indices.length)
    (hcopyWidth : (S.R copyWidth).length = Fs.length*(g.length*W))
    (sourceTail : List (Fin (prime+K+4)))
    (hcopyFresh : ∀ r ∈ [copySavedCount,archive,copySaved,copyTmp], S.R r = [])
    (hsourceBlank : S.R (e (extra 1)) = [])
    (ready : PublicationKernelReady e pad tmp saved V S)
    (hpadOff : ∀ r ∈ [pad,tmp,saved], r ∉ generatedPublicationHeaderRegisters)
    (hsourceA : (S.R (e replicaCount)).length = 2^b)
    (hsourceB : (S.R (e realRows)).length = g.indices.length)
    (hsourceC : (S.R (e (headerReg 86))).length = g.length)
    (hword : (S.R (e (headerReg 87))).length = W)
    (hheaderBlank : ∀ i ∈ [(84 : Fin 117),85,81,51,82,53,54,55,56,57,97,98,102,40,41,42,43,44,45], S.R (e (headerReg i)) = [])
    (hsrc : S.R source = (batches.map (fun rows => cstream (prime+K) W rows.flatten)).reverse.flatten++sourceTail)
    (dst : Fin PackedTranspose.tapeCount) (pub : PreparedPublicationPlan PackedTranspose.tapeCount (extra 1) dst)
    (clock lineRows : Fin PackedTranspose.tapeCount)
    (hports : (pub.support++[extra 1,dst,clock,lineRows]).Nodup)
    (hpubOff : ∀ r ∈ pub.sweepSupport++[extra 1,dst,lineRows], r ∉ generatedPublicationHeaderRegisters)
    (hwindow : pub.window = headerReg 82) (hpadding : pub.padRows = headerReg 53)
    (hwordPort : pub.wordWidth = headerReg 87)
    (ambient : Fin Fs.length → List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = s*W)
    (hcountPort : pub.count = headerReg 88) (hadvancePort : pub.advances = headerReg 91)
    (hsetupReg : [realRows,headerReg 86,headerReg 87,headerReg 90,pub.count,pub.advances,
      pub.savedAdvances,pub.savedControl,pub.tmp].Nodup)
    (hstrideOff : ∀ r ∈ pub.sweepSupport++[extra 1,dst,lineRows], r ≠ headerReg 90)
    (hpadSetupOff : ∀ r ∈ [pad,tmp,saved], r ∉ [headerReg 88,headerReg 91,headerReg 90])
    (hsetupBlank : ∀ r ∈ pub.uniformSetupHeaders (headerReg 90), S.R (e r) = [])
    (hfresh : ∀ r ∈ [pub.savedControl,pub.savedAdvances,pub.counter,pub.zero,pub.acc,pub.control,
      pub.trash,pub.tmp,pub.retireCount,pub.gap], S.R (e r) = [])
    (outputTail : List (Fin (prime+K+4)))
    (hdst : (embStk e S).R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : clock = headerReg 54) (hline : ((embStk e S).R lineRows).length = s),
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' : HS T Q (prime+K) U, ∃ n : ℕ,
      v'.user = v.user ∧ (n : ℝ) ≤ 2*(Sizes.T m : ℝ)+(2855+100*cV : ℕ)*(2^b*(s*W) : ℕ)+6+
        108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (2^b*(s*W) : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1) ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (2*Sizes.T m+(4390+100*cV+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(2^b*(s*W))+12)) depth
        (.seq (reverseCopyRows copyCount copySavedCount copyWidth source archive (e (extra 1)) copySaved copyTmp)
          (embProg e Empty.elim (uniformDyadicPublicationProgram hstates exponent packet pad tmp saved pub clock lineRows)))
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update S.R (e dst) (lines.flatten++outputTail))}) := by
  dsimp only
  have hplaced := selectedAmortizedPlacedDyadicPublication_exec (T := T) body hstates ct cV
  filter_upwards [hplaced,selectedAmortizedGatherSchedule ct] with m hplaced hschedule
  intro h i _ e he u target htarget W hW b V hV hreplicas hbits hfit hA exponent packet pad tmp saved hExponent hPacket hpadReg
    Fs hFs J batches hrows depth v S copyCount copySavedCount copyWidth source archive copySaved copyTmp
    hcopyReg hcopyCount hcopyWidth sourceTail hcopyFresh hsourceBlank ready hpadOff hsourceA hsourceB hsourceC hword hheaderBlank hsrc dst pub clock lineRows hports hpubOff hwindow hpadding hwordPort
    ambient hambient hcountPort hadvancePort hsetupReg hstrideOff hpadSetupOff hsetupBlank hfresh outputTail hdst hclock hline
  let p := Sizes.p m
  let s := Sizes.s m i
  let width := amortizedCoreWidth ct p
  let radius := localityDepth p target*PhaseCellBand.width p u
  let g := gatherPublicationClass s width radius (width+2*radius)
  have hbulkKeys := (hschedule h i u target htarget).2.2.2.1
  have hclassRows : List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p W width k Fs J rows) g.indices batches := by
    simpa only [g,gatherPublicationClass,hbulkKeys] using hrows
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := exactCoreArchive_copy_exec (body := body)
    g.indices Fs J batches hclassRows
    (fun k hk => ((mem_corePublicationIndices _ _ _ _).mp (g.sublist.subset hk)).2)
    copyCount copySavedCount copyWidth source archive (e (extra 1)) copySaved copyTmp hcopyReg
    sourceTail v S hcopyCount hcopyWidth hsrc hcopyFresh depth
  let word := (batches.map (fun rows => cstream (prime+K) W rows.flatten)).flatten
  let M : Stacks T (prime+K) := {S with R := Function.update S.R (e (extra 1)) word}
  have heCopy : ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
      2*reverseCopyRowsCost g.indices.length (Fs.length*(g.length*W))) depth
      (reverseCopyRows copyCount copySavedCount copyWidth source archive (e (extra 1)) copySaved copyTmp)
      (Host.mk v S) n₁ (Host.mk v₁ M) := by simpa only [hsourceBlank,List.append_nil] using he₁
  have hread (j : Fin PackedTranspose.tapeCount) (hj : j ≠ extra 1) : M.R (e j) = S.R (e j) :=
    Function.update_of_ne (he.ne hj) _ _
  have readyM := ready.of_frame hpadReg hread (by intro j; rfl)
  have setupBlankM : ∀ r ∈ pub.uniformSetupHeaders (headerReg 90), M.R (e r) = [] := by
    intro r hr
    have hne : r ≠ extra 1 := by
      simp only [PreparedPublicationPlan.uniformSetupHeaders,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (pub.support_off (by simp [PreparedPublicationPlan.support])).1
      · exact (pub.support_off (by simp [PreparedPublicationPlan.support])).1
      · exact base_extra _ _
    rw [hread r hne]
    exact hsetupBlank r hr
  have freshM : ∀ r ∈ [pub.savedControl,pub.savedAdvances,pub.counter,pub.zero,pub.acc,pub.control,
      pub.trash,pub.tmp,pub.retireCount,pub.gap], M.R (e r) = [] := by
    intro r hr
    have hmem : r ∈ pub.support := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [PreparedPublicationPlan.support]
    rw [hread r (pub.support_off hmem).1]
    exact hfresh r hr
  have htail : [extra 1,dst,clock,lineRows].Nodup := (List.nodup_append.mp hports).2.1
  have hlineOff : lineRows ≠ extra 1 := by
    intro heq
    exact (List.nodup_cons.mp htail).1 (heq ▸ (by simp : lineRows ∈ [dst,clock,lineRows]))
  obtain ⟨lines,v',n₂,hu₂,hn₂,hgood,he₂⟩ := hplaced
    h i e he u target htarget W hW b V hV hreplicas hbits hfit hA exponent packet pad tmp saved hExponent hPacket hpadReg
    Fs hFs J batches hrows depth v₁ M ⟨readyM.pad,readyM.tmp,readyM.saved,readyM.zero,readyM.width,
      readyM.blank,readyM.stages,readyM.left,readyM.fresh,readyM.count,readyM.codec⟩ hpadOff
    (by change (M.R (e replicaCount)).length = _; rw [hread replicaCount (base_extra _ _)]; exact hsourceA)
    (by change (M.R (e realRows)).length = _; rw [hread realRows (base_extra _ _)]; exact hsourceB)
    (by change (M.R (e (headerReg 86))).length = _; rw [hread (headerReg 86) (base_extra _ _)]; exact hsourceC)
    (by change (M.R (e (headerReg 87))).length = _; rw [hread (headerReg 87) (base_extra _ _)]; exact hword)
    (by intro i hi; change M.R (e (headerReg i)) = []; rw [hread (headerReg i) (base_extra _ _)]; exact hheaderBlank i hi)
    (by simp only [embStk,M,Function.comp_apply,Function.update_self,word])
    dst pub clock lineRows hports hpubOff hwindow hpadding hwordPort ambient hambient hcountPort hadvancePort hsetupReg hstrideOff hpadSetupOff setupBlankM freshM outputTail
    (by change M.R (e dst) = _; rw [hread dst pub.src_ne_dst.symm]; exact hdst)
    hclock
    (by change (M.R (e lineRows)).length = _; rw [hread lineRows hlineOff]; exact hline)
  have htotal := execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ heCopy he₂
  have hfinal : ({M with R := (Function.update (Function.update M.R (e (extra 1)) [])
      (e dst) (lines.flatten++outputTail))} : Stacks T (prime+K)) =
      {S with R := Function.update S.R (e dst) (lines.flatten++outputTail)} := by
    simp only [M,Function.update_idem,←hsourceBlank,Function.update_eq_self]
  have htotalFinal := htotal.cast rfl (congrArg (Host.mk v') hfinal)
  let windows := coreSubsetPublicationWindows s width g.length
    (amortizedCoreWidth_bounds ct p u target (by have := h.thirteen_le_p; omega) htarget).1 g.indices g.sublist
  have hrowsVolume : g.indices.length*g.length ≤ s := by
    have hv := windows.gaps_volume 1
    simp only [windows,scatterVolume,PublicationWindows.gaps_length,coreSubsetPublicationWindows,
      PublicationWindows.restrict,List.length_map,Nat.mul_one] at hv
    omega
  have hlength : 1 ≤ g.length := by
    have hw := (amortizedCoreWidth_bounds ct p u target (by have := h.thirteen_le_p; omega) htarget).1
    change 0 < width+2*radius-2*radius
    change 0 < width at hw
    omega
  have hreplicaPos : 1 ≤ Fs.length := by rw [hFs]; exact Nat.two_pow_pos b
  have hcopyBound := reverseCopyRowsCost_le_traffic g.indices.length Fs.length s g.length W
    hrowsVolume hlength hreplicaPos hW
  rw [hFs] at hcopyBound
  have hallowance : 2*reverseCopyRowsCost g.indices.length (Fs.length*(g.length*W))+
      (2*Sizes.T m+(4320+100*cV+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(2^b*(s*W))) ≤
      2*Sizes.T m+(4390+100*cV+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(2^b*(s*W))+12 := by
    rw [hFs]
    nlinarith only [hcopyBound]
  refine ⟨lines,v',n₁+n₂,hu₂.trans hu₁,?_,hgood,
    htotalFinal.mono (by intro z state hz; exact hz.trans (Nat.add_le_add_left hallowance _))⟩
  have htCopy := Nat.cast_le (α := ℝ).mpr (hn₁.trans (by simpa only [hFs] using hcopyBound))
  rw [Nat.cast_add]
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at htCopy hn₂ ⊢
  linarith only [htCopy,hn₂]

end IntegerMultBounds.MathlibTM2.Cost
