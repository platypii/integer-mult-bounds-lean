module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactDyadicGroupedPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreTilePublication
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! Exact grouped publication with independently chosen dyadic core and replica
capacities. Padding the core count does not depend on the replica radix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix PackedTranspose FixedStreamedBank
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {Q K s width : ℕ} [NeZero s] {P U : Type}

theorem exactDyadicArchivePublication_exec (body : P → Pr P PackedTranspose.tapeCount Q (prime+K) U)
    (p W : ℕ) (hW : 1 ≤ W) (g : CorePublicationClass s width) (hw : 0 < width)
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
    let bill := replicaPublicationCost Fs.length s (2^a-g.indices.length) g.length W+37*s*W+6*Fs.length+31
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' F n, v'.user = v.user ∧ n ≤ ((6*(2^(a+b)*(g.length*W))+4*(S.R (extra 1)).length+4*(g.length*W)+9*(a+b)+14)+(26*(2^a*(2^b*(g.length*W)))+24+2*restoringTimeCost hstates a b (g.length*W) V))+bill ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+((2*(6*(2^(a+b)*(g.length*W))+4*(S.R (extra 1)).length+4*(g.length*W)+9*(a+b)+14)+(40*(2^a*(2^b*(g.length*W)))+38+restoringStockAllowance hstates a b (g.length*W) V))+2*bill)) depth
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
  obtain ⟨values,hlen,hbatches,hbytes,hcert⟩ := exactCoreTileRows g.indices Fs J batches hrows
    (fun k hk => ((mem_corePublicationIndices s width g.length k).mp (g.sublist.subset hk)).2)
  have hcast (i : Fin g.indices.length) := congrArg List.flatten
    (List.ofFn_congr hFs (fun j => cstream (prime+K) W (values i j)))
  have hsource : S.R (extra 1) = (List.ofFn fun i => (List.ofFn fun j =>
      cstream (prime+K) W (values i (Fin.cast hFs.symm j))).flatten).flatten := by
    rw [hsrc,hbytes]
    simp_rw [←hcast]
  obtain ⟨v',F,n,hu,ht,he,hs,hd,hgood,hi,ho,hl,hframe⟩ := exactDyadicGroupedPublication_exec
    body p W hW g hw hstates (Nat.clog 2 g.indices.length) b V hpacket hbits hfit hA
    exponent packet pad tmp saved hpadReg Fs hFs J values hcert (Nat.le_pow_clog (by decide) _) depth v S
    hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth hblank hstageCount hL hfresh hsource hcount hcodec
    dst pub clock lineRows hports ambient hambient outputTail borrowed pubReady hdst hclock hline
  exact ⟨_,v',F,n,hu,ht,he,hs,hd,hgood,hi,ho,hl,hframe⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
