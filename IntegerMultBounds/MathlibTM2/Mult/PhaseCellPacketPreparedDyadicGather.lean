module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherPacketWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedDyadicGather

/-! Generate the packet width, run count-driven routing and retire the packet
master. Only the supplier source changes across the whole call. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedStreamedBank
noncomputable section
variable {Q K s : ℕ} {P U : Type}

def gatherPacketState (S : Stacks tapeCount (prime+K)) (L w : ℕ) : Stacks tapeCount (prime+K) :=
  {S with R := Function.update S.R packetWidth (List.replicate (L*w) tick)}

def packetPreparedGatherProgram (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P tapeCount Q (prime+K) U :=
  .seq gatherPacketWidthProgram (.seq (countedGatherProgram hstates) (uclear packetWidth))

theorem packetPreparedGather_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a width radius L w V : ℕ)
    (hLfit : L < 2^V) (hpacket : 0 < L*w)
    (hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < V)
    (hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^V)
    (hA : 4 ≤ prime+K) (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a)
    (depth : ℕ) (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hlength : S.R (headerReg 35) = binSyms V L) (hword : (S.R (headerReg 87)).length = w)
    (hwidth : (S.R (headerReg 115)).length = V)
    (hrows : (S.R realRows).length = (coreGatherIndices s width radius L).length)
    (hrep : (S.R replicaCount).length = 2^a)
    (hblank : ∀ i ∈ [(82 : Fin 117),86,81,84,85,97,98,102,40,41,42,43,44,45], S.R (headerReg i) = [])
    (hready : GatherReady id s a (Nat.clog 2 (coreGatherIndices s width radius L).length) width radius L w V
      (gatherHeaderState (gatherDimensionState (gatherPacketState S L w) a (coreGatherIndices s width radius L).length)
        a (Nat.clog 2 (coreGatherIndices s width radius L).length) (L*w) V))
    (hsrc : S.R (extra 1) = cstream (prime+K) w (coreGatherPayload width radius L Fs)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ gatherPacketWidthCost V L w+(countedGatherTimeCost hstates s a width radius L w V+(2*(L*w)+2)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*gatherPacketWidthCost V L w+countedGatherStockAllowance hstates s a width radius L w V))
        depth (packetPreparedGatherProgram hstates) (mk v S) n
        (mk v' {S with R := (Function.update S.R (extra 1)
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  have hi := headerReg_injective
  have hp : packetWidth = headerReg 82 := rfl
  have haway : packetWidth ≠ extra 1 := base_extra _ 1
  have hcore : realRows = headerReg 80 := rfl
  have hreplica : replicaCount = headerReg 83 := rfl
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := gatherPacketWidth_exec_within body V L w hLfit v S hlength hword
    (by
      intro i hi
      apply hblank
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp) depth
  let M := gatherPacketState S L w
  have hM (i : Fin 117) (hne : i ≠ 82) : M.R (headerReg i) = S.R (headerReg i) := by
    simp [M,gatherPacketState,hp,hi.eq_iff,hne]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := countedGather_exec_within body hstates a width radius L w V
    hpacket hbits hfit hA Fs hreplicas depth v₁ M
    (by rw [hM 115 (by decide)]; exact hwidth)
    (by rw [hcore,hM 80 (by decide)]; exact hrows)
    (by rw [hreplica,hM 83 (by decide)]; exact hrep)
    (by simp [M,gatherPacketState])
    (by
      intro i hi'
      have hne : i ≠ 82 := by intro he; subst i; simp at hi'
      rw [hM i hne]
      exact hblank i (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi')))
    hready (by simpa [M,gatherPacketState,Function.update_of_ne haway.symm] using hsrc)
  let F : Stacks tapeCount (prime+K) := {M with R := (Function.update M.R (extra 1)
    (coreSupplierStream (prime+K) width radius L w Fs))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) packetWidth v₂ F
  have hlen : (F.R packetWidth).length = L*w := by simp [F,M,gatherPacketState,Function.update_of_ne haway]
  rw [hlen] at he₃
  have hzero : S.R packetWidth = [] := by simpa only [hp] using hblank 82 (by simp)
  have hend : {F with R := Function.update F.R packetWidth []} =
      {S with R := Function.update S.R (extra 1) (coreSupplierStream (prime+K) width radius L w Fs)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = packetWidth
    · subst k; simp [Function.update_of_ne haway,hzero]
    · simp [F,M,gatherPacketState,hk,Function.update_apply]
  rw [hend] at he₃
  have he₃' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₂ F)+depth+0) depth
      (uclear packetWidth) (mk v₂ F) (2*(L*w)+2)
      (mk v₃ {S with R := Function.update S.R (extra 1) (coreSupplierStream (prime+K) width radius L w Fs)}) :=
    mn_native_exec_within he₃ 0 (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (by omega)
  refine ⟨v₃,n₁+(n₂+(2*(L*w)+2)),hu₃.trans (hu₂.trans hu₁),Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _),?_⟩
  simpa only [packetPreparedGatherProgram,M,gatherPacketState,Nat.add_zero] using mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃')

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
