module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationTransposeResult
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

theorem exactDyadicGroupedPublication_exec (body : P → Pr P PackedTranspose.tapeCount Q (prime+K) U)
    (p W : ℕ) (hW : 1 ≤ W) (g : CorePublicationClass s width) (hw : 0 < width)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b V : ℕ)
    (hpacket : 0 < g.length*W) (hbits : a+b < V) (hfit : (g.length*W)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (exponent packet pad tmp saved : Fin PackedTranspose.tapeCount)
    (hpadReg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (Fs : List (ZMod s → GaussianInt)) (hFs : Fs.length = 2^b)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (values : Fin g.indices.length → Fin Fs.length → List GaussianInt)
    (hrows : ∀ i : Fin g.indices.length,
      ExactCoreRows (A := (prime+K)) p W width g.indices[i] Fs J (List.ofFn (values i)))
    (hcapacity : g.indices.length ≤ 2^a) (depth : ℕ)
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
    (hsrc : S.R (extra 1) =
      (List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) W (values i (Fin.cast hFs.symm j))).flatten).flatten)
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
    (hclock : (S.R clock).length = Fs.length) (hline : (S.R lineRows).length = s) :
    let lines := List.ofFn fun j => g.output W hw (indexedCoreRows g.indices rfl values j) (ambient j)
    let bill := replicaPublicationCost Fs.length s (2^a-g.indices.length) g.length W+37*s*W+6*Fs.length+31
    ∃ v' F n, v'.user = v.user ∧ n ≤ ((6*(2^(a+b)*(g.length*W))+4*(S.R (extra 1)).length+4*(g.length*W)+9*(a+b)+14)+(26*(2^a*(2^b*(g.length*W)))+24+2*restoringTimeCost hstates a b (g.length*W) V))+bill ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+((2*(6*(2^(a+b)*(g.length*W))+4*(S.R (extra 1)).length+4*(g.length*W)+9*(a+b)+14)+(40*(2^a*(2^b*(g.length*W)))+38+restoringStockAllowance hstates a b (g.length*W) V))+2*bill)) depth
        (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (PackedTranspose.program hstates)) (pub.replicaProgram clock lineRows)) (Host.mk v S) n (Host.mk v' F) ∧
      F.R (extra 1) = [] ∧ F.R dst = lines.flatten++outputTail ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ extra 1 → r ≠ dst → F.R r = S.R r := by
  dsimp only
  have hlength : ∀ i j, (values i j).length = g.length := by
    intro i j
    have hlen := (hrows i).2.1 _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
    exact hlen.trans (((mem_corePublicationIndices s width g.length _).mp
      (g.sublist.subset (List.getElem_mem i.isLt))).2)
  obtain ⟨tileD,hcap,v₁,n₁,hu₁,hn₁,he₁⟩ := prepare_rows_result_exec_within body hstates a b g.length W V
    hpacket hbits hfit hA exponent packet pad tmp saved hpadReg hcapacity
    (fun i j => values i (Fin.cast hFs.symm j)) (fun i j => hlength i _) depth v S
    hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth hblank hstageCount hL hfresh hsrc hcount hcodec
  let tile : ArchiveTilePlan.Result g.length values :=
    ⟨tileD.capacity,tileD.capacity_ge,(fun i j => tileD.padded i (Fin.cast hFs j)),
      (fun i j => tileD.rowLength i _),(by intro i j; simpa using tileD.realRows i (Fin.cast hFs j))⟩
  let M : Stacks PackedTranspose.tapeCount (prime+K) := {S with L := fun _ => [], R := (Function.update S.R (extra 1)
    ((List.ofFn fun j => cstream (prime+K) W (List.ofFn fun i => tileD.padded i j).flatten).flatten))}
  have hsource : M.R (extra 1) = (List.ofFn fun j => cstream (prime+K) W
      (List.ofFn fun i => tile.padded i j).flatten).flatten++[] := by
    simp only [M,Function.update_self,List.append_nil]
    congr 1
    exact List.ofFn_congr hFs.symm _
  have hpubReady : pub.Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      W (tile.capacity-g.indices.length) borrowed M := by
    have h := pubReady.of_frame (F := M) (by intro r hr; exact Function.update_of_ne (pub.support_off hr).1 _ _)
    simpa only [tile,hcap] using h
  have htail : [extra 1,dst,clock,lineRows].Nodup := (List.nodup_append.mp hports).2.1
  have hclockOff : clock ≠ extra 1 := by
    intro heq
    exact (List.nodup_cons.mp htail).1 (heq ▸ (by simp : clock ∈ [dst,clock,lineRows]))
  have hlineOff : lineRows ≠ extra 1 := by
    intro heq
    exact (List.nodup_cons.mp htail).1 (heq ▸ (by simp : lineRows ∈ [dst,clock,lineRows]))
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hs,hd,hgood,hi,ho,hl,hframe⟩ := exactCoreTilePublication_exec
    (body := body) pub clock lineRows hports p W hW g hw Fs J values hrows tile ambient hambient
    [] outputTail borrowed v₁ M hpubReady hsource
    (by simpa only [M,Function.update_of_ne pub.src_ne_dst.symm] using hdst)
    (by simpa only [M,Function.update_of_ne hclockOff] using hclock)
    (by simpa only [M,Function.update_of_ne hlineOff] using hline) depth
  simp only [tile,hcap] at hn₂ he₂
  refine ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ he₁ he₂,hs,hd,hgood,hi,ho,?_,?_⟩
  · exact hl.trans (funext fun i => (hL i).symm)
  · intro r hrs hrd
    exact (hframe r hrs hrd).trans (Function.update_of_ne hrs _ _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
