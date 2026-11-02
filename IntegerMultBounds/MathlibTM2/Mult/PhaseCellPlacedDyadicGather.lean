module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherRouting
public import IntegerMultBounds.MathlibTM2.Host.EmbedOwnedUpdateStock

/-! Place the complete gather router over ambient spectator storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank
variable {T Q K s : ℕ} {P U : Type}

theorem placedGatherRoute_exec_within (body : P → Pr P T Q (prime+K) U)
    (e : Fin tapeCount → Fin T) (he : Function.Injective e)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b width radius L w V : ℕ)
    (hpacket : 0 < L*w) (hbits : a+b < V) (hfit : (L*w)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ 2^b)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a) (depth : ℕ)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (ha : (embStk e S).R (base (callerGenerator 97)) = binSyms V a)
    (hb : (embStk e S).R (base (callerGenerator 98)) = binSyms V b)
    (hseed : (embStk e S).R (base (callerGenerator 102)) = binSyms V (L*w)) (hz : (embStk e S).R (base (callerGenerator 106)) = [])
    (hwidth : ((embStk e S).R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, (embStk e S).R (base (callerGenerator (originReg r))) = [])
    (hstageCount : (embStk e S).R (base (callerGenerator 116)) = []) (hL : ∀ i, (embStk e S).L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → (embStk e S).R (base (callerWorker i)) = [])
    (hsrc : (embStk e S).R (extra 1) = cstream (prime+K) w (coreGatherPayload width radius L Fs))
    (hrows : ((embStk e S).R realRows).length = (coreGatherIndices s width radius L).length)
    (hcap : ((embStk e S).R capacityRows).length = 2^b) (hpw : ((embStk e S).R packetWidth).length = L*w)
    (hrep : ((embStk e S).R replicaCount).length = 2^a)
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 4,extra 5,extra 6], (embStk e S).R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ gatherRouteTimeCost hstates s a b width radius L w V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        gatherRouteStockAllowance hstates s a b width radius L w V) depth
        (embProg e Empty.elim (gatherProgram (P := Empty) hstates)) (mk v S) n
        (mk v' {S with R := (Function.update S.R (e (extra 1))
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  obtain ⟨v₁,n,hu,hn,ht⟩ := gatherRoute_exec_within (fun z : Empty => nomatch z)
    hstates a b width radius L w V hpacket hbits hfit hA hcapacity Fs hreplicas depth
    (embDn e v) (embStk e S) ha hb hseed hz hwidth hblank hstageCount hL hfresh hsrc
    hrows hcap hpw hrep hcodec
  have hleft : (fun _ => []) = (embStk e S).L := funext (fun i => (hL i).symm)
  rw [hleft] at ht
  obtain ⟨v',hu',ht'⟩ := exec_emb_owned_update_within e he (fun z : Empty => nomatch z)
    (extra 1) (coreSupplierStream (prime+K) width radius L w Fs) v S ht
  exact ⟨v',n,hu'.trans hu,hn,ht'⟩

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
