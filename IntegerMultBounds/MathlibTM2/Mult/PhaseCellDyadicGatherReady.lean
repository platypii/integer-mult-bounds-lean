module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDyadicGather

/-! Retained routing dimensions and fresh scratch, independent of the source
word. Ambient exposure changes only that source. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedStreamedBank
variable {T Q K s : ℕ} {P U : Type}

structure GatherReady (e : Fin tapeCount → Fin T) (s a b width radius L w V : ℕ)
    (S : Stacks T (prime+K)) : Prop where
  ha : S.R (e (base (callerGenerator 97))) = binSyms V a
  hb : S.R (e (base (callerGenerator 98))) = binSyms V b
  hseed : S.R (e (base (callerGenerator 102))) = binSyms V (L*w)
  hz : S.R (e (base (callerGenerator 106))) = []
  hwidth : (S.R (e (base (callerGenerator 115)))).length = V
  hblank : ∀ r, S.R (e (base (callerGenerator (originReg r)))) = []
  hstageCount : S.R (e (base (callerGenerator 116))) = []
  hL : ∀ i, S.L (e i) = []
  hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 →
    S.R (e (base (callerWorker i))) = []
  hrows : (S.R (e realRows)).length = (coreGatherIndices s width radius L).length
  hcap : (S.R (e capacityRows)).length = 2^b
  hpw : (S.R (e packetWidth)).length = L*w
  hrep : (S.R (e replicaCount)).length = 2^a
  hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 4,extra 5,extra 6], S.R (e i) = []

namespace GatherReady
variable {e : Fin tapeCount → Fin T} {a b width radius L w V : ℕ}
  {S F : Stacks T (prime+K)}

theorem of_frame (h : GatherReady e s a b width radius L w V S)
    (hR : ∀ i, i ≠ extra 1 → F.R (e i) = S.R (e i))
    (hL : ∀ i, F.L (e i) = S.L (e i)) :
    GatherReady e s a b width radius L w V F := by
  have hbase (i : Fin kernelT) : F.R (e (base i)) = S.R (e (base i)) := hR _ (base_extra _ 1)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hbase] using h.ha
  · simpa only [hbase] using h.hb
  · simpa only [hbase] using h.hseed
  · simpa only [hbase] using h.hz
  · simpa only [hbase] using h.hwidth
  · simpa only [hbase] using h.hblank
  · simpa only [hbase] using h.hstageCount
  · simpa only [hL] using h.hL
  · simpa only [hbase] using h.hfresh
  · simpa only [realRows,hbase] using h.hrows
  · simpa only [capacityRows,hbase] using h.hcap
  · simpa only [packetWidth,hbase] using h.hpw
  · simpa only [replicaCount,hbase] using h.hrep
  · intro i hi
    have hne : i ≠ extra 1 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact base_extra _ 1
      all_goals simp [planeReg,extra,Fin.ext_iff]
    rw [hR i hne]
    exact h.hcodec i hi

theorem exec (h : GatherReady e s a b width radius L w V S)
    (body : P → Pr P T Q (prime+K) U) (he : Function.Injective e)
    (hstates : FixedStreamedBank.stateCount ≤ Q)
    (hpacket : 0 < L*w) (hbits : a+b < V) (hfit : (L*w)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ 2^b)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a) (depth : ℕ)
    (v : HS T Q (prime+K) U)
    (hsrc : S.R (e (extra 1)) = cstream (prime+K) w (coreGatherPayload width radius L Fs)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ gatherRouteTimeCost hstates s a b width radius L w V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        gatherRouteStockAllowance hstates s a b width radius L w V) depth
        (embProg e Empty.elim (gatherProgram (P := Empty) hstates)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (e (extra 1))
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  exact placedGatherRoute_exec_within body e he hstates a b width radius L w V
    hpacket hbits hfit hA hcapacity Fs hreplicas depth v S
    h.ha h.hb h.hseed h.hz h.hwidth h.hblank h.hstageCount h.hL h.hfresh hsrc
    h.hrows h.hcap h.hpw h.hrep h.hcodec

end GatherReady
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
