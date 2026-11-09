module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellExactDyadicArchivePublication
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
variable {Q K : ℕ} {P U : Type}

theorem selectedAmortizedDyadicPublication_exec (body : P → Pr P PackedTranspose.tapeCount Q (prime+K) U)
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
    (hpadReg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (Fs : List (ZMod s → GaussianInt)) (hFs : Fs.length = 2^b)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (batches : List (List (List GaussianInt)))
    (hrows : List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p W width k Fs J rows) (coreBulkIndices s width (PhaseCellBand.width p u) (localityDepth p target)) batches)
    (depth : ℕ)
    (v : HS PackedTranspose.tapeCount Q (prime+K) U) (S : Stacks PackedTranspose.tapeCount (prime+K))
    (hexponent : (S.R exponent).length = a+b) (hpacketWidth : (S.R packet).length = g.length*W)
    (hpad : S.R pad = []) (htmp : S.R tmp = []) (hsaved : S.R saved = [])
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V (g.length*W))
    (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hstageCount : S.R (base (callerGenerator 116)) = []) (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hsrc : S.R (extra 1) = (batches.map (fun rows => cstream (prime+K) W rows.flatten)).flatten)
    (hcount : S.R (extra 4) = [])
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R i = [])
    (dst : Fin PackedTranspose.tapeCount) (pub : PreparedPublicationPlan PackedTranspose.tapeCount (extra 1) dst)
    (clock lineRows : Fin PackedTranspose.tapeCount)
    (hports : (pub.support++[extra 1,dst,clock,lineRows]).Nodup)
    (ambient : Fin Fs.length → List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = s*W)
    (outputTail borrowed : List (Fin (prime+K+4)))
    (pubReady : pub.Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      W (2^a-g.indices.length) borrowed S)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = Fs.length) (hline : (S.R lineRows).length = s),
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ (n : ℝ) ≤ 2*(Sizes.T m : ℝ)+1700*(2^b*(s*W) : ℕ)+
        108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (2^b*(s*W) : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (2*Sizes.T m+(3200+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(2^b*(s*W)))) depth
        (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (PackedTranspose.program hstates)) (pub.replicaProgram clock lineRows)) (Host.mk v S) n (Host.mk v' F) ∧
      F.R (extra 1) = [] ∧ F.R dst = lines.flatten++outputTail ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ extra 1 → r ≠ dst → F.R r = S.R r := by
  dsimp only
  filter_upwards [selectedAmortizedCoreGeometry ct,selectedAmortizedGatherSchedule ct,
    selectedPolynomialPublicationCosts_le hstates cV (816*(ct+5)+18) 8] with m hgeometry hschedule hcost
  intro h i _ u target htarget W hW b V hV hreplicas hbits hfit hA exponent packet pad tmp saved hpadReg
    Fs hFs J batches hrows depth v S hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth
    hblank hstageCount hL hfresh hsrc hcount hcodec dst pub clock lineRows hports ambient hambient
    outputTail borrowed pubReady hdst hclock hline
  let p := Sizes.p m
  let s := Sizes.s m i
  let width := amortizedCoreWidth ct p
  let radius := localityDepth p target*PhaseCellBand.width p u
  let g := gatherPublicationClass s width radius (width+2*radius)
  have hp : 1 ≤ p := by have := h.thirteen_le_p; omega
  obtain ⟨hw,hpow,hr,hroom,hgroups⟩ := hgeometry h i u target htarget
  change 0 < width at hw
  change radius ≤ width at hr
  change 3*width+PhaseCellBand.width p u ≤ s at hroom
  have hspan : g.length ≤ s := by change width+2*radius-2*radius ≤ s; omega
  have hlength : g.length = width := Nat.add_sub_cancel_right _ _
  have hprepare : p^2 ≤ g.length := by
    rw [hlength]
    exact (pow_le_pow_right' hp (by decide : 2 ≤ 8)).trans hpow
  have hpacket : 0 < g.length*W := Nat.mul_pos (by rw [hlength]; exact hw) hW
  have hbulkKeys := (hschedule h i u target htarget).2.2.2.1
  have hclassRows : List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p W width k Fs J rows) g.indices batches := by
    simpa only [g,gatherPublicationClass,hbulkKeys] using hrows
  obtain ⟨lines,v',F,n,hu,ht,he,hs,hd,hgood,hi,ho,hl,hframe⟩ := exactDyadicArchivePublication_bounded_exec
    body p W hW g hw hspan hstates b V hpacket hbits hfit hA exponent packet pad tmp saved hpadReg
    Fs hFs J batches hclassRows depth v S hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth
    hblank hstageCount hL hfresh hsrc hcount hcodec dst pub clock lineRows hports ambient hambient
    outputTail borrowed pubReady hdst hclock hline
  let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
  have hwindowCount : windows.origins.length = (coreGatherIndices s width radius (width+2*radius)).length := by
    simp only [windows,coreSubsetPublicationWindows,PublicationWindows.restrict,List.length_map,g,gatherPublicationClass]
  have hgroup : width+2*radius ∈ coreGatherLengths s width radius := by simp [coreGatherLengths]
  obtain ⟨htSelected,hsSelected⟩ := hcost h i width radius (width+2*radius) b W V windows hw
    (by rfl) hr hgroup hwindowCount hprepare hspan hW hV hreplicas
  have htEnvelope : n ≤ 1700*(2^b*(s*W))+100*V+500+Sizes.T m+
      2*restoringTimeCost hstates (Nat.clog 2 g.indices.length) b (g.length*W) V := by omega
  have htR := Nat.cast_le (α := ℝ).mpr htEnvelope
  have hwindowKeys : windows.origins.length = g.indices.length := by
    simp only [windows,coreSubsetPublicationWindows,PublicationWindows.restrict,List.length_map]
  rw [hwindowKeys] at htSelected hsSelected
  have hsEnvelope : 800*(2^b*(s*W))+200+
      restoringStockAllowance hstates (Nat.clog 2 g.indices.length) b (g.length*W) V ≤
      2*Sizes.T m+(3200+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(2^b*(s*W)) := by
    have hbase : 800*(2^b*(s*W))+200+
        restoringStockAllowance hstates (Nat.clog 2 g.indices.length) b (g.length*W) V ≤
        3200*(2^b*(s*W))+200*V+800+Sizes.T m+
        restoringStockAllowance hstates (Nat.clog 2 g.indices.length) b (g.length*W) V := by omega
    exact hbase.trans hsSelected
  refine ⟨lines,v',F,n,hu,?_,?_,hs,hd,hgood,hi,ho,hl,hframe⟩
  · push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at htR htSelected ⊢
    exact htR.trans htSelected
  · exact he.mono (by intro z state hz; exact hz.trans (Nat.add_le_add_left hsEnvelope _))

end IntegerMultBounds.MathlibTM2.Cost
