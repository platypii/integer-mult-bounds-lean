module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedInitializedDyadicPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUniformDyadicPublicationProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConsecutivePublicationAdvances
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellUniformSweepBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPublicationSweepReady
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedPublicationHeaderBudget

/-! Generate binary dimensions from unary masters, execute selected dyadic
publication, and retire the owned headers. Only source and output change. -/
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
variable {Q K : ℕ} {P U : Type}

private theorem initialization_header_off_sweep (j : Fin 117)
    (hj : j ∈ [(84 : Fin 117),85,81,51,82,53,54,55,56,57,97,98,102,40,41,42,43,44,45]) :
    j ≠ 88 ∧ j ≠ 91 ∧ j ≠ 90 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem selectedAmortizedUniformDyadicPublication_exec (body : P → Pr P PackedTranspose.tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (ct cV : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
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
    (v : HS PackedTranspose.tapeCount Q (prime+K) U) (S : Stacks PackedTranspose.tapeCount (prime+K))
    (hworkspace : PublicationKernelReady (fun i => i) pad tmp saved V S)
    (hpadOff : ∀ r ∈ [pad,tmp,saved], r ∉ generatedPublicationHeaderRegisters)
    (hsourceA : (S.R replicaCount).length = 2^b)
    (hsourceB : (S.R realRows).length = g.indices.length)
    (hsourceC : (S.R (headerReg 86)).length = g.length)
    (hword : (S.R (headerReg 87)).length = W)
    (hheaderBlank : ∀ i ∈ [(84 : Fin 117),85,81,51,82,53,54,55,56,57,97,98,102,40,41,42,43,44,45], S.R (headerReg i) = [])
    (hsrc : S.R (extra 1) = (batches.map (fun rows => cstream (prime+K) W rows.flatten)).flatten)
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
    (hsetupBlank : ∀ r ∈ pub.uniformSetupHeaders (headerReg 90), S.R r = [])
    (hfresh : ∀ r ∈ [pub.savedControl,pub.savedAdvances,pub.counter,pub.zero,pub.acc,pub.control,
      pub.trash,pub.tmp,pub.retireCount,pub.gap], S.R r = [])
    (outputTail : List (Fin (prime+K+4)))
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : clock = headerReg 54) (hline : (S.R lineRows).length = s),
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ (n : ℝ) ≤ (2*(Sizes.T m : ℝ)+(2820+100*cV : ℕ)*(2^b*(s*W) : ℕ)+
        108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (2^b*(s*W) : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (2*Sizes.T m+(4320+100*cV+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(2^b*(s*W)))) depth
        (uniformDyadicPublicationProgram hstates exponent packet pad tmp saved pub clock lineRows) (Host.mk v S) n (Host.mk v' F) ∧
      F.R (extra 1) = [] ∧ F.R dst = lines.flatten++outputTail ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ extra 1 → r ≠ dst → F.R r = S.R r := by
  dsimp only
  filter_upwards [selectedAmortizedInitializedDyadicPublication_exec body hstates ct cV,
    selectedAmortizedCoreGeometry ct] with m hpub hgeometry
  intro h i _ u target htarget W hW b V hV hreplicas hbits hfit hA exponent packet pad tmp saved hExponent hPacket hpadReg
    Fs hFs J batches hrows depth v S hworkspace hpadOff hsourceA hsourceB hsourceC hword hheaderBlank hsrc
    dst pub clock lineRows hports hpubOff hwindow hpadding hwordPort ambient hambient
    hcountPort hadvancePort hsetupReg hstrideOff hpadSetupOff hsetupBlank hfresh outputTail hdst hclock hline
  let p := Sizes.p m
  let s := Sizes.s m i
  let width := amortizedCoreWidth ct p
  let radius := localityDepth p target*PhaseCellBand.width p u
  let g := gatherPublicationClass s width radius (width+2*radius)
  obtain ⟨hw,hpow,hguard,hroom,_⟩ := hgeometry h i u target htarget
  change 0 < width at hw
  change radius ≤ width at hguard
  change 3*width+PhaseCellBand.width p u ≤ s at hroom
  have hp : 1 ≤ p := by have := h.thirteen_le_p; omega
  have hradius : 0 < radius := localityCoreWidth_pos hp u target
  let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
  have hwindowCount : windows.origins.length = g.indices.length := by
    simp only [windows,coreSubsetPublicationWindows,PublicationWindows.restrict,List.length_map]
  have hstride := fullGatherPublication_advances s width radius W hw hradius hguard (by omega)
  obtain ⟨v₀,n₀,hu₀,hn₀,sweepReady,he₀⟩ := PreparedPublicationPlan.uniformSetup_exec_within body pub
    realRows (headerReg 86) (headerReg 87) (headerReg 90) hsetupReg
    (by intro r hr; exact hstrideOff r (List.mem_append_left _ hr)) windows W depth (by simpa only [hwindowCount] using hstride) v S
    (by rw [hwindowCount]; exact hsourceB) hsourceC hword hsetupBlank hfresh
  let M := pub.uniformSetupState (headerReg 90) g.indices.length (g.length*W) S
  simp only [hwindowCount] at hn₀ sweepReady he₀
  have hread (r : Fin PackedTranspose.tapeCount) (hr : r ∉ pub.uniformSetupHeaders (headerReg 90)) : M.R r = S.R r :=
    PreparedPublicationPlan.uniformSetupState_off pub _ _ _ S r hr
  have hreadGen (r : Fin PackedTranspose.tapeCount) (hr : r ∉ [headerReg 88,headerReg 91,headerReg 90]) : M.R r = S.R r :=
    hread r (by simpa only [PreparedPublicationPlan.uniformSetupHeaders,hcountPort,hadvancePort] using hr)
  have hreadHeader (j : Fin 117) (h88 : j ≠ 88) (h91 : j ≠ 91) (h90 : j ≠ 90) :
      M.R (headerReg j) = S.R (headerReg j) :=
    hreadGen _ (by simp [headerReg_injective.eq_iff,h88,h91,h90])
  have kernelM := hworkspace.of_generator_frame (F := M) [88,91,90]
    (by intro j hj; simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; rcases hj with rfl | rfl | rfl <;> decide)
    (by intro r hr j hj heq; apply hpadSetupOff r hr; rw [heq];
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; rcases hj with rfl | rfl | rfl <;> simp)
    (by intro r hr; apply hreadGen; simp [hr 88 (by simp),hr 91 (by simp),hr 90 (by simp)])
    (by intro j; rfl)
  have dataOff (r : Fin PackedTranspose.tapeCount) (hr : r ∈ [extra 1,dst,lineRows]) :
      r ∉ pub.uniformSetupHeaders (headerReg 90) := by
    have hd := (List.nodup_append.mp hports).2.2
    have hr' : r ∈ [extra 1,dst,clock,lineRows] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl <;> simp
    simp only [PreparedPublicationPlan.uniformSetupHeaders,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨(hd pub.count (by simp [PreparedPublicationPlan.support]) r hr').symm,
      (hd pub.advances (by simp [PreparedPublicationPlan.support]) r hr').symm,
      hstrideOff r (List.mem_append_right _ hr)⟩
  obtain ⟨lines,v₂,F,n₂,hu₂,hn₂,he₂,hs,hd,hgood,hi,ho,hl,hframe⟩ := hpub
    h i u target htarget W hW b V hV hreplicas hbits hfit hA exponent packet pad tmp saved hExponent hPacket hpadReg
    Fs hFs J batches hrows depth v₀ M kernelM hpadOff
    (by change (M.R (headerReg 83)).length = _; rw [hreadHeader 83 (by decide) (by decide) (by decide)]; exact hsourceA)
    (by change (M.R (headerReg 80)).length = _; rw [hreadHeader 80 (by decide) (by decide) (by decide)]; exact hsourceB)
    (by rw [hreadHeader 86 (by decide) (by decide) (by decide)]; exact hsourceC)
    (by rw [hreadHeader 87 (by decide) (by decide) (by decide)]; exact hword)
    (by
      intro j hj
      obtain ⟨h88,h91,h90⟩ := initialization_header_off_sweep j hj
      rw [hreadHeader j h88 h91 h90]
      exact hheaderBlank j hj)
    (by rw [hread _ (dataOff _ (by simp))]; exact hsrc)
    dst pub clock lineRows hports hpubOff hwindow hpadding hwordPort ambient hambient outputTail [] sweepReady
    (by rw [hread _ (dataOff _ (by simp))]; exact hdst) hclock
    (by rw [hread _ (dataOff _ (by simp))]; exact hline)
  have hF : F = {M with R := Function.update (Function.update M.R (extra 1) []) dst (lines.flatten++outputTail)} := by
    refine Stacks.ext hi ho hl ?_
    funext r
    by_cases hr : r = dst
    · subst r; simpa only [Function.update_self] using hd
    · by_cases hs' : r = extra 1
      · subst r; simpa only [Function.update_of_ne hr,Function.update_self] using hs
      · simpa only [Function.update_of_ne hr,Function.update_of_ne hs'] using hframe r hs' hr
  obtain ⟨v',hu₃,he₃⟩ := PreparedPublicationPlan.retireUniformSetup_exec_within body pub (headerReg 90)
    g.indices.length (g.length*W)
    (by
      intro r hr
      apply hstrideOff r
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      rcases hr with hr | rfl | rfl
      · exact Or.inl hr
      · simp
      · simp)
    [] (lines.flatten++outputTail) S hsetupBlank v₂ depth
  have he₂' := he₂.cast rfl (congrArg (Host.mk v₂) hF)
  have heTotal := execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ 0
    (execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ he₀ he₂') he₃
  have hL : 1 ≤ g.length := by change 1 ≤ width+2*radius-2*radius; omega
  have hrowsVolume : g.indices.length*g.length ≤ s := by
    have hv := windows.gaps_volume 1
    simp only [windows,scatterVolume,PublicationWindows.gaps_length,coreSubsetPublicationWindows,
      PublicationWindows.restrict,List.length_map,Nat.mul_one] at hv
    omega
  have hN : g.indices.length ≤ s := (Nat.le_mul_of_pos_right _ hL).trans hrowsVolume
  have hs : 1 ≤ s := by omega
  have hpacket : g.length*W ≤ 2^b*(s*W) := by
    have hspan : g.length ≤ s := by change width+2*radius-2*radius ≤ s; omega
    exact (Nat.mul_le_mul_right W hspan).trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos b))
  have hcountTraffic : g.indices.length ≤ 2^b*(s*W) := hN.trans
    ((Nat.le_mul_of_pos_right s hW).trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos b)))
  have hpayloadSource : g.indices.length*(g.length*W) ≤ s*W := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right W hrowsVolume
  have hpayload : g.indices.length*(g.length*W) ≤ 2^b*(s*W) :=
    hpayloadSource.trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos b))
  obtain ⟨htSetup,hsSetup⟩ := uniformPublicationSetupCosts_le _ _ _ (2^b*(s*W)) hpayload hcountTraffic hpacket hW
    (Nat.mul_pos (Nat.two_pow_pos b) (Nat.mul_pos hs hW))
  refine ⟨lines,v',_,n₀+n₂+(2*(g.indices.length*(g.length*W))+4*g.indices.length+2*(g.length*W)+9),hu₃.trans (hu₂.trans hu₀),?_,
    heTotal.mono (by intro z state hz; nlinarith only [hz,hsSetup]),?_,?_,hgood,rfl,rfl,rfl,?_⟩
  · have hn₀Real := Nat.cast_le (α := ℝ).mpr hn₀
    have htReal := Nat.cast_le (α := ℝ).mpr htSetup
    simp only [PreparedPublicationPlan.uniformSetupCost,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hn₀Real hn₂ htReal ⊢
    linarith only [hn₀Real,hn₂,htReal]
  · exact (Function.update_of_ne pub.src_ne_dst _ _).trans (Function.update_self _ _ _)
  · exact Function.update_self _ _ _
  · intro r hs hd
    exact (Function.update_of_ne hd _ _).trans (Function.update_of_ne hs _ _)

end IntegerMultBounds.MathlibTM2.Cost
