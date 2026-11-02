module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherProgram

/-! Execute padding, actual dyadic routing and dummy-core retirement from the
real gathered word. Only the source changes to the supplier stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank
variable {Q K s : ℕ} {P U : Type}

def gatherRouteTimeCost (hstates : FixedStreamedBank.stateCount ≤ Q) (s a b width radius L w V : ℕ) : ℕ :=
  let M := (coreGatherIndices s width radius L).length
  (gatherCounterSetupCost M (2^b) (L*w)+(2^a*(6*(2^b*L*w)+13)+6)+(2*(2^b*L*w)+4))+
    (26*(2^a*(2^b*(L*w)))+24+2*restoringTimeCost hstates a b (L*w) V)+
    retireDummyBatchesCost M (2^b) (2^a) (L*w)

def gatherRouteStockAllowance (hstates : FixedStreamedBank.stateCount ≤ Q) (s a b width radius L w V : ℕ) : ℕ :=
  let M := (coreGatherIndices s width radius L).length
  (2*gatherCounterSetupCost M (2^b) (L*w)+(2^a*((2^b-M)*L*w)+2*(4*(2^b*L*w)+10)))+
    (40*(2^a*(2^b*(L*w)))+38+restoringStockAllowance hstates a b (L*w) V)+
    2*retireDummyBatchesCost M (2^b) (2^a) (L*w)

theorem gatherRoute_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b width radius L w V : ℕ)
    (hpacket : 0 < L*w) (hbits : a+b < V) (hfit : (L*w)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ 2^b)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a) (depth : ℕ)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V (L*w)) (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hstageCount : S.R (base (callerGenerator 116)) = []) (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hsrc : S.R (extra 1) = cstream (prime+K) w (coreGatherPayload width radius L Fs))
    (hrows : (S.R realRows).length = (coreGatherIndices s width radius L).length)
    (hcap : (S.R capacityRows).length = 2^b) (hpw : (S.R packetWidth).length = L*w)
    (hrep : (S.R replicaCount).length = 2^a)
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 4,extra 5,extra 6], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ gatherRouteTimeCost hstates s a b width radius L w V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        gatherRouteStockAllowance hstates s a b width radius L w V) depth (gatherProgram hstates) (mk v S) n
        (mk v' {S with L := (fun _ => []), R := (Function.update S.R (extra 1)
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  have hr := padGather_registers
  regs_ne hr
  have hcb : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R i = [] := by
    intro i hi
    apply hcodec i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generatedPadCoreGatherPayload_exec_within (body := body)
    realRows capacityRows packetWidth (extra 5) (extra 6) (extra 4) (extra 1) (extra 0) (extra 3) (extra 2)
    replicaCount (planeReg false) padGather_registers (2^b) width radius L w hcapacity Fs [] v S
    hrows hcap hpw (hcodec _ (by simp)) (hcodec _ (by simp)) (hcodec _ (by simp))
    (by simpa only [List.append_nil] using hsrc) (hcodec _ (by simp [planeReg]))
    (by simpa only [hreplicas] using hrep) (hcodec _ (by simp)) (hcodec _ (by simp)) (hcodec _ (by simp)) depth
  let M : Stacks tapeCount (prime+K) := {S with R := (Function.update S.R (extra 1)
    (cstream (prime+K) w (paddedCoreGatherPayload (2^b) width radius L Fs)))}
  simp only [List.append_nil,hreplicas] at he₁ hn₁
  have hM (k : Fin tapeCount) (hk : k ≠ extra 1) : M.R k = S.R k := Function.update_of_ne hk _ _
  obtain ⟨rows,hlen,hbatches,v₂,n₂,hu₂,hn₂,he₂⟩ := gathered_exec_within body hstates a b width radius L w V
    hpacket hbits hfit hA hcapacity Fs hreplicas depth v₁ M
    (by rw [hM _ (base_extra _ 1)]; exact ha) (by rw [hM _ (base_extra _ 1)]; exact hb)
    (by rw [hM _ (base_extra _ 1)]; exact hseed) (by rw [hM _ (base_extra _ 1)]; exact hz)
    (by rw [hM _ (base_extra _ 1)]; exact hwidth)
    (by intro r; rw [hM _ (base_extra _ 1)]; exact hblank r)
    (by rw [hM _ (base_extra _ 1)]; exact hstageCount) hL
    (by intro i hip hiq; rw [hM _ (base_extra _ 1)]; exact hfresh i hip hiq) (by simp [M])
    (by rw [hM _ ‹extra 4 ≠ extra 1›]; exact hcodec _ (by simp))
    (by
      intro i hi
      have hne : i ≠ extra 1 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | assumption | (apply Ne.symm; assumption) | exact base_extra _ 1
      rw [hM i hne]
      exact hcb i hi)
  let F : Stacks tapeCount (prime+K) := {S with L := (fun _ => []), R := (Function.update S.R (extra 1)
    ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten))}
  have he₂' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₁ M)+depth+
      (40*(2^a*(2^b*(L*w)))+38+restoringStockAllowance hstates a b (L*w) V)) depth
      (program hstates) (mk v₁ M) n₂ (mk v₂ F) := by
    simpa only [M,F,Function.update_idem] using he₂
  have hF (k : Fin tapeCount) (hk : k ≠ extra 1) : F.R k = S.R k := Function.update_of_ne hk _ _
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := retireRoutedGather_exec_within (body := body)
    realRows capacityRows replicaCount packetWidth (extra 5) (extra 6) (extra 4) (extra 3) (extra 2) (extra 1)
    retireGather_registers width radius L w hcapacity Fs rows hlen hbatches v₂ F
    (by rw [hF _ ‹realRows ≠ extra 1›]; exact hrows)
    (by rw [hF _ ‹capacityRows ≠ extra 1›]; exact hcap)
    (by rw [hF _ ‹extra 1 ≠ replicaCount›.symm]; exact hrep)
    (by rw [hF _ ‹packetWidth ≠ extra 1›]; exact hpw)
    (by rw [hF _ ‹extra 5 ≠ extra 1›]; exact hcodec _ (by simp))
    (by rw [hF _ ‹extra 6 ≠ extra 1›]; exact hcodec _ (by simp))
    (by rw [hF _ ‹extra 4 ≠ extra 1›]; exact hcodec _ (by simp))
    (by rw [hF _ ‹extra 1 ≠ extra 3›.symm]; exact hcodec _ (by simp))
    (by rw [hF _ ‹extra 1 ≠ extra 2›.symm]; exact hcodec _ (by simp)) (by simp [F]) depth
  refine ⟨v₃,n₁+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · simpa only [gatherRouteTimeCost, Nat.add_assoc] using
      Nat.add_le_add hn₁ (Nat.add_le_add hn₂ hn₃)
  · have ht := mn_seq_within_add he₁ (mn_seq_within_add he₂' he₃)
    simpa only [gatherRouteStockAllowance,gatherProgram,padGatherProgram,retireGatherProgram,
      coreSupplierStream,M,F,Function.update_idem,Nat.add_assoc] using ht

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
