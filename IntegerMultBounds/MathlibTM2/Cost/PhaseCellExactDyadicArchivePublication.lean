module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactDyadicArchivePublication
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
variable {Q K s width : ℕ} [NeZero s] {P U : Type}

theorem exactDyadicArchivePublication_bounded_exec (body : P → Pr P PackedTranspose.tapeCount Q (prime+K) U)
    (p W : ℕ) (hW : 1 ≤ W) (g : CorePublicationClass s width) (hw : 0 < width) (hspan : g.length ≤ s)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (b V : ℕ) :
    let a := Nat.clog 2 g.indices.length
    ∀
    (hpacket : 0 < g.length*W) (hbits : a+b < V) (hfit : (g.length*W)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (exponent packet pad tmp saved : Fin PackedTranspose.tapeCount)
    (hpadReg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (Fs : List (ZMod s → GaussianInt)) (hFs : Fs.length = 2^b)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (batches : List (List (List GaussianInt)))
    (hrows : List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p W width k Fs J rows) g.indices batches)
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
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' F n, v'.user = v.user ∧ n ≤ 400*(2^b*(s*W))+100+2*restoringTimeCost hstates a b (g.length*W) V ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (800*(2^b*(s*W))+200+restoringStockAllowance hstates a b (g.length*W) V)) depth
        (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (PackedTranspose.program hstates)) (pub.replicaProgram clock lineRows)) (Host.mk v S) n (Host.mk v' F) ∧
      F.R (extra 1) = [] ∧ F.R dst = lines.flatten++outputTail ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ extra 1 → r ≠ dst → F.R r = S.R r := by
  dsimp only
  intro hpacket hbits hfit hA exponent packet pad tmp saved hpadReg Fs hFs J batches hrows depth v S
    hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth hblank hstageCount hL hfresh hsrc hcount hcodec
    dst pub clock lineRows hports ambient hambient outputTail borrowed pubReady hdst hclock hline
  obtain ⟨lines,v',F,n,hu,ht,he,hs,hd,hgood,hi,ho,hl,hframe⟩ := exactDyadicArchivePublication_exec
    body p W hW g hw hstates b V hpacket hbits hfit hA exponent packet pad tmp saved hpadReg
    Fs hFs J batches hrows depth v S hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth
    hblank hstageCount hL hfresh hsrc hcount hcodec dst pub clock lineRows hports ambient hambient outputTail
    borrowed pubReady hdst hclock hline
  let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
  have hwindowCount : windows.origins.length = g.indices.length := by
    simp only [windows,coreSubsetPublicationWindows,PublicationWindows.restrict,List.length_map]
  have hvolume := exactCoreOutputs_volume g.indices Fs J
    (batches.map (fun rows => cstream (prime+K) W rows.flatten)) ⟨batches,rfl,hrows⟩
    (fun k hk => ((mem_corePublicationIndices _ _ _ _).mp (g.sublist.subset hk)).2)
  have hsourceVolume : (S.R (extra 1)).length = g.indices.length*(2^b*(g.length*W)) := by
    rw [hsrc]
    simpa only [List.length_flatten,List.map_reverse,List.sum_reverse,hFs] using hvolume
  have hOld : (S.R (extra 1)).length ≤ 2^Nat.clog 2 windows.origins.length*(2^b*(g.length*W)) := by
    rw [hsourceVolume,hwindowCount]
    exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
  obtain ⟨htime,hstock⟩ := exactDyadicPublicationCosts_le windows (Nat.pos_of_mul_pos_right hpacket) hspan b W
    (S.R (extra 1)).length
    (restoringTimeCost hstates (Nat.clog 2 g.indices.length) b (g.length*W) V)
    (restoringStockAllowance hstates (Nat.clog 2 g.indices.length) b (g.length*W) V) hW hOld
  simp only [hwindowCount] at htime hstock
  simp only [hFs] at ht he
  refine ⟨lines,v',F,n,hu,ht.trans htime,?_,hs,hd,hgood,hi,ho,hl,hframe⟩
  exact he.mono (by intro z state hz; exact hz.trans (Nat.add_le_add_left hstock _))

end IntegerMultBounds.MathlibTM2.Cost
