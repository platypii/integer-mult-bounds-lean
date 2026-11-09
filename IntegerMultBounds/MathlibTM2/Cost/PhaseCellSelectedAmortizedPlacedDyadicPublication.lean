module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedDyadicPublication
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
    (hpadReg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (Fs : List (ZMod s → GaussianInt)) (hFs : Fs.length = 2^b)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (batches : List (List (List GaussianInt)))
    (hrows : List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p W width k Fs J rows) (coreBulkIndices s width (PhaseCellBand.width p u) (localityDepth p target)) batches)
    (depth : ℕ)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hexponent : ((embStk e S).R exponent).length = a+b) (hpacketWidth : ((embStk e S).R packet).length = g.length*W)
    (hpad : (embStk e S).R pad = []) (htmp : (embStk e S).R tmp = []) (hsaved : (embStk e S).R saved = [])
    (ha : (embStk e S).R (base (callerGenerator 97)) = binSyms V a)
    (hb : (embStk e S).R (base (callerGenerator 98)) = binSyms V b)
    (hseed : (embStk e S).R (base (callerGenerator 102)) = binSyms V (g.length*W))
    (hz : (embStk e S).R (base (callerGenerator 106)) = [])
    (hwidth : ((embStk e S).R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, (embStk e S).R (base (callerGenerator (originReg r))) = [])
    (hstageCount : (embStk e S).R (base (callerGenerator 116)) = []) (hL : ∀ i, (embStk e S).L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → (embStk e S).R (base (callerWorker i)) = [])
    (hsrc : (embStk e S).R (extra 1) = (batches.map (fun rows => cstream (prime+K) W rows.flatten)).flatten)
    (hcount : (embStk e S).R (extra 4) = [])
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], (embStk e S).R i = [])
    (dst : Fin PackedTranspose.tapeCount) (pub : PreparedPublicationPlan PackedTranspose.tapeCount (extra 1) dst)
    (clock lineRows : Fin PackedTranspose.tapeCount)
    (hports : (pub.support++[extra 1,dst,clock,lineRows]).Nodup)
    (ambient : Fin Fs.length → List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = s*W)
    (outputTail borrowed : List (Fin (prime+K+4)))
    (pubReady : pub.Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      W (2^a-g.indices.length) borrowed (embStk e S))
    (hdst : (embStk e S).R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : ((embStk e S).R clock).length = Fs.length) (hline : ((embStk e S).R lineRows).length = s),
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' : HS T Q (prime+K) U, ∃ n : ℕ,
      v'.user = v.user ∧ (n : ℝ) ≤ 2*(Sizes.T m : ℝ)+1700*(2^b*(s*W) : ℕ)+
        108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (2^b*(s*W) : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1) ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (2*Sizes.T m+(3200+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(2^b*(s*W)))) depth
        (embProg e Empty.elim (.seq (.seq
          (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (PackedTranspose.program hstates)) (pub.replicaProgram clock lineRows)))
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update
          (Function.update S.R (e (extra 1)) []) (e dst) (lines.flatten++outputTail))}) := by
  dsimp only
  have hlocal := selectedAmortizedDyadicPublication_exec (fun f : Empty => nomatch f)
    hstates ct cV (U := U) (K := K)
  filter_upwards [hlocal] with m hlocal
  intro h i _ e he u target htarget W hW b V hV hreplicas hbits hfit hA exponent packet pad tmp saved hpadReg
    Fs hFs J batches hrows depth v S hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth
    hblank hstageCount hL hfresh hsrc hcount hcodec dst pub clock lineRows hports ambient hambient
    outputTail borrowed pubReady hdst hclock hline
  obtain ⟨lines,vm,F,n,hu,ht,hwithin,hs,hd,hgood,hi,ho,hl,hframe⟩ := hlocal
    h i u target htarget W hW b V hV hreplicas hbits hfit hA exponent packet pad tmp saved hpadReg
    Fs hFs J batches hrows depth (embDn e v) (embStk e S) hexponent hpacketWidth hpad htmp hsaved
    ha hb hseed hz hwidth hblank hstageCount hL hfresh hsrc hcount hcodec dst pub clock lineRows hports
    ambient hambient outputTail borrowed pubReady hdst hclock hline
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
