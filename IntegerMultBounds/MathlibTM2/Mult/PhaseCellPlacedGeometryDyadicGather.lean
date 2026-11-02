module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryDyadicGather

/-! Place the complete geometry-driven gather route over ambient storage,
retaining its exact source-only update and complete resource allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedStreamedBank
noncomputable section
variable {T Q K : ℕ} {P U : Type}

theorem placedGeometryGather_exec_within (body : P → Pr P T Q (prime+K) U)
    (e : Fin tapeCount → Fin T) (he : Function.Injective e)
    (hstates : FixedStreamedBank.stateCount ≤ Q)
    (V s a width radius L w : ℕ) (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V)
    (hLfit : L < 2^V) (hA : 4 ≤ prime+K) (hV : 0 < V)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (h37 : ((embStk e S).R (headerReg 37)).length = V)
    (hs : (embStk e S).R (headerReg 32) = binSyms V s) (hw : (embStk e S).R (headerReg 33) = binSyms V width)
    (hr : (embStk e S).R (headerReg 34) = binSyms V radius) (hL : (embStk e S).R (headerReg 35) = binSyms V L)
    (hz : (embStk e S).R (headerReg 36) = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → (embStk e S).R (headerReg k) = [])
    (h104 : (embStk e S).R (headerReg 104) = []) (h106 : (embStk e S).R (headerReg 106) = [])
    (h116 : (embStk e S).R (headerReg 116) = []) (h109 : (embStk e S).R (headerReg 109) = [])
    (hrows : (embStk e S).R realRows = [])
    (hpacket : 0 < L*w)
    (hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < V)
    (hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^V)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a)
    (hword : ((embStk e S).R (headerReg 87)).length = w) (hrouterWidth : ((embStk e S).R (headerReg 115)).length = V)
    (hrep : ((embStk e S).R replicaCount).length = 2^a)
    (hclean : ∀ i ∈ [(82 : Fin 117),86,81,84,85,97,98,102,40,41,42,43,44,45], (embStk e S).R (headerReg i) = [])
    (hready : GatherReady id s a (Nat.clog 2 (coreGatherIndices s width radius L).length) width radius L w V
      (gatherHeaderState (gatherDimensionState (gatherPacketState
        (gatherCoreState (embStk e S) s width radius L) L w) a (coreGatherIndices s width radius L).length)
        a (Nat.clog 2 (coreGatherIndices s width radius L).length) (L*w) V))
    (hsrc : (embStk e S).R (extra 1) = cstream (prime+K) w (coreGatherPayload width radius L Fs)) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ geometryGatherTimeCost hstates V s a width radius L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        geometryGatherStockAllowance hstates V s a width radius L w) depth
        (embProg e Empty.elim (geometryGatherProgram (P := Empty) hstates)) (mk v S) n
        (mk v' {S with R := (Function.update S.R (e (extra 1))
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  obtain ⟨v₁,n,hu,hn,ht⟩ := geometryGather_exec_within (fun z : Empty => nomatch z)
    hstates V s a width radius L w hwidth hwide hLfit hA hV (embDn e v) (embStk e S)
    h37 hs hw hr hL hz hblank h104 h106 h116 h109 hrows hpacket hbits hfit Fs hreplicas
    hword hrouterWidth hrep hclean hready hsrc depth
  obtain ⟨v',hu',ht'⟩ := exec_emb_owned_update_within e he (fun z : Empty => nomatch z)
    (extra 1) (coreSupplierStream (prime+K) width radius L w Fs) v S ht
  exact ⟨v',n,hu'.trans hu,hn,ht'⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
