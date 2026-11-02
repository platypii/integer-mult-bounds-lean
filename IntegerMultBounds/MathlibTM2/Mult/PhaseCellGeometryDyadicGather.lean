module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherCoreCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketPreparedDyadicGather

/-! Complete geometry-driven routing: generate the core count, packet width,
dimensions and headers, route the payload, then retire all generated metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedStreamedBank
noncomputable section
variable {Q K : ℕ} {P U : Type}

def gatherCoreState (S : Stacks tapeCount (prime+K)) (s width radius L : ℕ) : Stacks tapeCount (prime+K) :=
  {S with R := Function.update S.R realRows (List.replicate (coreGatherIndices s width radius L).length tick)}

def geometryGatherProgram (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P tapeCount Q (prime+K) U :=
  .seq gatherCoreCountProgram (.seq (packetPreparedGatherProgram hstates) (uclear realRows))

def geometryGatherTimeCost (hstates : FixedStreamedBank.stateCount ≤ Q) (V s a width radius L w : ℕ) : ℕ :=
  let rows := (coreGatherIndices s width radius L).length
  (preparedCoreOriginsCost V s width radius L+((2*rows+2)+(2*(rows*V)+2)))+
    ((gatherPacketWidthCost V L w+(countedGatherTimeCost hstates s a width radius L w V+(2*(L*w)+2)))+(2*rows+2))

def geometryGatherStockAllowance (hstates : FixedStreamedBank.stateCount ≤ Q) (V s a width radius L w : ℕ) : ℕ :=
  let rows := (coreGatherIndices s width radius L).length
  (3*preparedCoreOriginsCost V s width radius L+2*(2*rows+2))+
    (3*gatherPacketWidthCost V L w+countedGatherStockAllowance hstates s a width radius L w V)

theorem geometryGather_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q)
    (V s a width radius L w : ℕ) (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V)
    (hLfit : L < 2^V) (hA : 4 ≤ prime+K) (hV : 0 < V)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (h37 : (S.R (headerReg 37)).length = V)
    (hs : S.R (headerReg 32) = binSyms V s) (hw : S.R (headerReg 33) = binSyms V width)
    (hr : S.R (headerReg 34) = binSyms V radius) (hL : S.R (headerReg 35) = binSyms V L)
    (hz : S.R (headerReg 36) = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R (headerReg k) = [])
    (h104 : S.R (headerReg 104) = []) (h106 : S.R (headerReg 106) = [])
    (h116 : S.R (headerReg 116) = []) (h109 : S.R (headerReg 109) = [])
    (hrows : S.R realRows = [])
    (hpacket : 0 < L*w)
    (hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < V)
    (hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^V)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a)
    (hword : (S.R (headerReg 87)).length = w) (hrouterWidth : (S.R (headerReg 115)).length = V)
    (hrep : (S.R replicaCount).length = 2^a)
    (hclean : ∀ i ∈ [(82 : Fin 117),86,81,84,85,97,98,102,40,41,42,43,44,45], S.R (headerReg i) = [])
    (hready : GatherReady id s a (Nat.clog 2 (coreGatherIndices s width radius L).length) width radius L w V
      (gatherHeaderState (gatherDimensionState (gatherPacketState
        (gatherCoreState S s width radius L) L w) a (coreGatherIndices s width radius L).length)
        a (Nat.clog 2 (coreGatherIndices s width radius L).length) (L*w) V))
    (hsrc : S.R (extra 1) = cstream (prime+K) w (coreGatherPayload width radius L Fs)) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ geometryGatherTimeCost hstates V s a width radius L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        geometryGatherStockAllowance hstates V s a width radius L w) depth (geometryGatherProgram hstates)
        (mk v S) n (mk v' {S with R := (Function.update S.R (extra 1)
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  let rows := (coreGatherIndices s width radius L).length
  have hi := headerReg_injective
  have hcore : realRows = headerReg 80 := rfl
  have hreplica : replicaCount = headerReg 83 := rfl
  have haway : realRows ≠ extra 1 := base_extra _ 1
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := gatherCoreCount_exec_within body V s width radius L hwidth hwide hLfit hA hV v S
    h37 hs hw hr hL hz hblank h104 h106 h116 h109 hrows depth
  let M := gatherCoreState S s width radius L
  have hM (i : Fin 117) (hne : i ≠ 80) : M.R (headerReg i) = S.R (headerReg i) := by
    simp [M,gatherCoreState,hcore,hi.eq_iff,hne]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packetPreparedGather_exec_within body hstates a width radius L w V
    hLfit hpacket hbits hfit hA Fs hreplicas depth v₁ M
    (by rw [hM 35 (by decide)]; exact hL)
    (by rw [hM 87 (by decide)]; exact hword)
    (by rw [hM 115 (by decide)]; exact hrouterWidth)
    (by simp [M,gatherCoreState])
    (by rw [hreplica,hM 83 (by decide)]; exact hrep)
    (by
      intro i hi'
      have hne : i ≠ 80 := by intro he; subst i; simp at hi'
      rw [hM i hne]
      exact hclean i hi')
    hready (by simpa [M,gatherCoreState,Function.update_of_ne haway.symm] using hsrc)
  let F : Stacks tapeCount (prime+K) := {M with R := (Function.update M.R (extra 1)
    (coreSupplierStream (prime+K) width radius L w Fs))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) realRows v₂ F
  have hlen : (F.R realRows).length = rows := by simp [F,M,gatherCoreState,Function.update_of_ne haway,rows]
  rw [hlen] at he₃
  have hend : {F with R := Function.update F.R realRows []} =
      {S with R := Function.update S.R (extra 1) (coreSupplierStream (prime+K) width radius L w Fs)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = realRows
    · subst k; simp [Function.update_of_ne haway,hrows]
    · simp [F,M,gatherCoreState,hk,Function.update_apply]
  rw [hend] at he₃
  have he₃' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₂ F)+depth+0) depth
      (uclear realRows) (mk v₂ F) (2*rows+2)
      (mk v₃ {S with R := Function.update S.R (extra 1) (coreSupplierStream (prime+K) width radius L w Fs)}) :=
    mn_native_exec_within he₃ 0 (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (by omega)
  refine ⟨v₃,n₁+(n₂+(2*rows+2)),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · simpa only [geometryGatherTimeCost,rows] using Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _)
  · simpa only [geometryGatherProgram,geometryGatherStockAllowance,M,gatherCoreState,rows,Nat.add_zero] using
      mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃')

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
