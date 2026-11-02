module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedGeometryDyadicGather

/-! Ordinary initial workspace data for the complete geometry-driven router.
Its source-independent frame lets ambient exposure populate the source first. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ} {P U : Type}

def generatedGatherState (S : Stacks tapeCount (prime+K)) (V s a width radius L w : ℕ) :=
  gatherHeaderState (gatherDimensionState (gatherPacketState (gatherCoreState S s width radius L) L w)
    a (coreGatherIndices s width radius L).length) a (Nat.clog 2 (coreGatherIndices s width radius L).length) (L*w) V

structure GeometryReady (e : Fin tapeCount → Fin T) (V s a width radius L w : ℕ)
    (S : Stacks T (prime+K)) : Prop where
  h37 : (S.R (e (headerReg 37))).length = V
  hs : S.R (e (headerReg 32)) = binSyms V s
  hw : S.R (e (headerReg 33)) = binSyms V width
  hr : S.R (e (headerReg 34)) = binSyms V radius
  hL : S.R (e (headerReg 35)) = binSyms V L
  hz : S.R (e (headerReg 36)) = []
  hblank : ∀ k : Fin 117, k.val < 31 → S.R (e (headerReg k)) = []
  h104 : S.R (e (headerReg 104)) = []
  h106 : S.R (e (headerReg 106)) = []
  h116 : S.R (e (headerReg 116)) = []
  h109 : S.R (e (headerReg 109)) = []
  hrows : S.R (e realRows) = []
  hword : (S.R (e (headerReg 87))).length = w
  hrouterWidth : (S.R (e (headerReg 115))).length = V
  hrep : (S.R (e replicaCount)).length = 2^a
  hclean : ∀ i ∈ [(82 : Fin 117),86,81,84,85,97,98,102,40,41,42,43,44,45], S.R (e (headerReg i)) = []
  hready : GatherReady id s a (Nat.clog 2 (coreGatherIndices s width radius L).length) width radius L w V
    (generatedGatherState (embStk e S) V s a width radius L w)

namespace GeometryReady
variable {e : Fin tapeCount → Fin T} {V s a width radius L w : ℕ} {S F : Stacks T (prime+K)}

theorem of_frame (h : GeometryReady e V s a width radius L w S)
    (hR : ∀ i, i ≠ extra 1 → F.R (e i) = S.R (e i))
    (hleft : ∀ i, F.L (e i) = S.L (e i)) : GeometryReady e V s a width radius L w F := by
  have hbase (i : Fin 117) : F.R (e (headerReg i)) = S.R (e (headerReg i)) := hR _ (base_extra _ 1)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hbase] using h.h37
  · simpa only [hbase] using h.hs
  · simpa only [hbase] using h.hw
  · simpa only [hbase] using h.hr
  · simpa only [hbase] using h.hL
  · simpa only [hbase] using h.hz
  · simpa only [hbase] using h.hblank
  · simpa only [hbase] using h.h104
  · simpa only [hbase] using h.h106
  · simpa only [hbase] using h.h116
  · simpa only [hbase] using h.h109
  · exact (hR _ (base_extra _ 1)).trans h.hrows
  · simpa only [hbase] using h.hword
  · simpa only [hbase] using h.hrouterWidth
  · simpa only [show replicaCount = headerReg 83 from rfl,hbase] using h.hrep
  · simpa only [hbase] using h.hclean
  · apply h.hready.of_frame
    · intro i hi
      change (generatedGatherState (embStk e F) V s a width radius L w).R i =
        (generatedGatherState (embStk e S) V s a width radius L w).R i
      simp only [generatedGatherState,gatherHeaderState,gatherDimensionState,gatherPacketState,gatherCoreState,
        Function.update_apply]
      split_ifs <;> first | rfl | exact hR i hi
    · intro i; exact hleft i

theorem exec (h : GeometryReady e V s a width radius L w S)
    (body : P → Pr P T Q (prime+K) U) (he : Function.Injective e)
    (hstates : FixedStreamedBank.stateCount ≤ Q)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hA : 4 ≤ prime+K) (hV : 0 < V) (hpacket : 0 < L*w)
    (hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < V)
    (hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^V)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a)
    (hsrc : S.R (e (extra 1)) = cstream (prime+K) w (coreGatherPayload width radius L Fs))
    (v : HS T Q (prime+K) U) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ geometryGatherTimeCost hstates V s a width radius L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        geometryGatherStockAllowance hstates V s a width radius L w) depth
        (embProg e Empty.elim (geometryGatherProgram (P := Empty) hstates)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (e (extra 1))
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  exact placedGeometryGather_exec_within body e he hstates V s a width radius L w hwidth hwide hLfit hA hV v S
    h.h37 h.hs h.hw h.hr h.hL h.hz h.hblank h.h104 h.h106 h.h116 h.h109 h.hrows hpacket hbits hfit Fs hreplicas
    h.hword h.hrouterWidth h.hrep h.hclean h.hready hsrc depth

end GeometryReady
end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
