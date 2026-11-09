module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedUniformDyadicPublication
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

theorem selectedAmortizedPlacedDyadicPublication_exec (body : P → Pr P T Q (prime+K) U)
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
    (hworkspace : PublicationKernelReady (fun i => i) pad tmp saved V (embStk e S))
    (hpadOff : ∀ r ∈ [pad,tmp,saved], r ∉ generatedPublicationHeaderRegisters)
    (hsourceA : ((embStk e S).R replicaCount).length = 2^b)
    (hsourceB : ((embStk e S).R realRows).length = g.indices.length)
    (hsourceC : ((embStk e S).R (headerReg 86)).length = g.length)
    (hword : ((embStk e S).R (headerReg 87)).length = W)
    (hheaderBlank : ∀ i ∈ [(84 : Fin 117),85,81,51,82,53,54,55,56,57,97,98,102,40,41,42,43,44,45], (embStk e S).R (headerReg i) = [])
    (hsrc : (embStk e S).R (extra 1) = (batches.map (fun rows => cstream (prime+K) W rows.flatten)).flatten)
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
    (hsetupBlank : ∀ r ∈ pub.uniformSetupHeaders (headerReg 90), (embStk e S).R r = [])
    (hfresh : ∀ r ∈ [pub.savedControl,pub.savedAdvances,pub.counter,pub.zero,pub.acc,pub.control,
      pub.trash,pub.tmp,pub.retireCount,pub.gap], (embStk e S).R r = [])
    (outputTail : List (Fin (prime+K+4)))
    (hdst : (embStk e S).R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : clock = headerReg 54) (hline : ((embStk e S).R lineRows).length = s),
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' : HS T Q (prime+K) U, ∃ n : ℕ,
      v'.user = v.user ∧ (n : ℝ) ≤ 2*(Sizes.T m : ℝ)+(2820+100*cV : ℕ)*(2^b*(s*W) : ℕ)+
        108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (2^b*(s*W) : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1) ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (2*Sizes.T m+(4320+100*cV+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(2^b*(s*W)))) depth
        (embProg e Empty.elim (uniformDyadicPublicationProgram hstates exponent packet pad tmp saved pub clock lineRows))
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update
          (Function.update S.R (e (extra 1)) []) (e dst) (lines.flatten++outputTail))}) := by
  dsimp only
  have hlocal := selectedAmortizedUniformDyadicPublication_exec (fun f : Empty => nomatch f)
    hstates ct cV (U := U) (K := K)
  filter_upwards [hlocal] with m hlocal
  intro h i _ e he u target htarget W hW b V hV hreplicas hbits hfit hA exponent packet pad tmp saved hExponent hPacket hpadReg
    Fs hFs J batches hrows depth v S hworkspace hpadOff hsourceA hsourceB hsourceC hword hheaderBlank hsrc
    dst pub clock lineRows hports hpubOff hwindow hpadding hwordPort ambient hambient
    hcountPort hadvancePort hsetupReg hstrideOff hpadSetupOff hsetupBlank hfresh outputTail hdst hclock hline
  obtain ⟨lines,vm,F,n,hu,ht,hwithin,hs,hd,hgood,hi,ho,hl,hframe⟩ := hlocal
    h i u target htarget W hW b V hV hreplicas hbits hfit hA exponent packet pad tmp saved hExponent hPacket hpadReg
    Fs hFs J batches hrows depth (embDn e v) (embStk e S) hworkspace hpadOff hsourceA hsourceB hsourceC hword hheaderBlank hsrc
    dst pub clock lineRows hports hpubOff hwindow hpadding hwordPort
    ambient hambient hcountPort hadvancePort hsetupReg hstrideOff hpadSetupOff hsetupBlank hfresh outputTail hdst hclock hline
  have hfinal : F = {(embStk e S) with R := (Function.update
      (Function.update (embStk e S).R (extra 1) []) dst (lines.flatten++outputTail))} := by
    refine Stacks.ext hi ho hl ?_
    funext r
    by_cases hrs : r = extra 1
    · subst r
      simpa only [Function.update_of_ne pub.src_ne_dst,Function.update_self] using hs
    · by_cases hrd : r = dst
      · subst r
        simpa only [Function.update_self] using hd
      · simpa only [Function.update_of_ne hrs,Function.update_of_ne hrd] using hframe r hrs hrd
  have hlocalTrace := hwithin.cast rfl (congrArg (Host.mk vm) hfinal)
  obtain ⟨v',hprojection,huser,hplaced⟩ := exec_emb_ovr_within_stock (e := e) (ι := Empty.elim)
    (body' := body) he (by intro f; cases f) hlocalTrace v rfl S rfl
  have hend : embOvr e ({(embStk e S) with R := (Function.update
      (Function.update (embStk e S).R (extra 1) []) dst (lines.flatten++outputTail))}).get S =
      {S with R := (Function.update (Function.update S.R (e (extra 1)) []) (e dst) (lines.flatten++outputTail))} := by
    change embOvr e (rightUpdates [(extra 1,[]),(dst,lines.flatten++outputTail)] (embStk e S)).get S = _
    rw [embOvr_rightUpdates he,embOvr_stk]
    rfl
  rw [hend] at hplaced
  exact ⟨lines,v',n,huser.trans hu,ht,hgood,hplaced⟩

end IntegerMultBounds.MathlibTM2.Cost
