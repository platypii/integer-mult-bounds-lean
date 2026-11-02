module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherCapacity
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedDyadicGather

/-! The complete gather router starts from retained counts, derives its own
minimal dyadic dimensions and headers, and retires all generated metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedStreamedBank
noncomputable section
variable {Q K s : ℕ} {P U : Type}

def gatherDimensionState (S : Stacks tapeCount (prime+K)) (a rows : ℕ) : Stacks tapeCount (prime+K) :=
  {S with R := (Function.update (Function.update (Function.update S.R
    (headerReg 84) (List.replicate a tick)) (headerReg 85) (List.replicate (Nat.clog 2 rows) tick))
    capacityRows (List.replicate (2^Nat.clog 2 rows) tick))}

def countedGatherProgram (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P tapeCount Q (prime+K) U :=
  .seq gatherDimensionsProgram (.seq (preparedGatherProgram hstates)
    (clearWords [headerReg 84,headerReg 85,capacityRows]))

def countedGatherTimeCost (hstates : FixedStreamedBank.stateCount ≤ Q)
    (s a width radius L w V : ℕ) : ℕ :=
  let rows := (coreGatherIndices s width radius L).length
  let b := Nat.clog 2 rows
  (((19*2^a+10)+(19*rows+9))+(4*2^b+9*b+5))+
    (((21*(a+b+L*w)+36*V+85)+(gatherRouteTimeCost hstates s a b width radius L w V+(6*V+7)))+
      (2*(a+b+2^b)+7))

def countedGatherStockAllowance (hstates : FixedStreamedBank.stateCount ≤ Q)
    (s a width radius L w V : ℕ) : ℕ :=
  let rows := (coreGatherIndices s width radius L).length
  let b := Nat.clog 2 rows
  ((2*(19*2^a+10)+2*(19*rows+9))+2*(4*2^b+9*b+5))+
    (2*(21*(a+b+L*w)+36*V+85)+gatherRouteStockAllowance hstates s a b width radius L w V)

theorem countedGather_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a width radius L w V : ℕ)
    (hpacket : 0 < L*w)
    (hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < V)
    (hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^V)
    (hA : 4 ≤ prime+K) (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a)
    (depth : ℕ) (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hwidth : (S.R (headerReg 115)).length = V)
    (hrows : (S.R realRows).length = (coreGatherIndices s width radius L).length)
    (hrep : (S.R replicaCount).length = 2^a) (hpacketWidth : (S.R packetWidth).length = L*w)
    (hblank : ∀ i ∈ [(81 : Fin 117),84,85,97,98,102,40,41,42,43,44,45], S.R (headerReg i) = [])
    (hready : GatherReady id s a (Nat.clog 2 (coreGatherIndices s width radius L).length) width radius L w V
      (gatherHeaderState (gatherDimensionState S a (coreGatherIndices s width radius L).length)
        a (Nat.clog 2 (coreGatherIndices s width radius L).length) (L*w) V))
    (hsrc : S.R (extra 1) = cstream (prime+K) w (coreGatherPayload width radius L Fs)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ countedGatherTimeCost hstates s a width radius L w V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        countedGatherStockAllowance hstates s a width radius L w V) depth (countedGatherProgram hstates)
        (mk v S) n (mk v' {S with R := (Function.update S.R (extra 1)
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  let rows := (coreGatherIndices s width radius L).length
  let b := Nat.clog 2 rows
  have hi := headerReg_injective
  have hcap : capacityRows = headerReg 81 := rfl
  have hpw : packetWidth = headerReg 82 := rfl
  have haway (j : Fin 117) : headerReg j ≠ extra 1 := base_extra _ 1
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := gatherDimensions_exec_within body a rows depth v S hrep hrows
    (by
      intro i hi
      apply hblank
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let M := gatherDimensionState S a rows
  have hM (i : Fin 117) (h81 : i ≠ 81) (h84 : i ≠ 84) (h85 : i ≠ 85) : M.R (headerReg i) = S.R (headerReg i) := by
    simp [M,gatherDimensionState,hcap,hi.eq_iff,h81,h84,h85]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := preparedGather_exec_within body hstates a b width radius L w V
    hpacket hbits hfit hA (Nat.le_pow_clog (by decide) rows) Fs hreplicas depth v₁ M
    (by rw [hM 115 (by decide) (by decide) (by decide)]; exact hwidth)
    (by simp [M,gatherDimensionState,hcap,hi.eq_iff])
    (by simp [M,gatherDimensionState,hcap,hi.eq_iff,b])
    (by rw [hpw,hM 82 (by decide) (by decide) (by decide)]; exact hpacketWidth)
    (by
      intro i hi'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [hM _ (by decide) (by decide) (by decide)] <;> apply hblank <;> simp)
    hready (by simpa [M,gatherDimensionState,hcap,Function.update_of_ne (haway _).symm] using hsrc)
  let F : Stacks tapeCount (prime+K) := {M with R := (Function.update M.R (extra 1)
    (coreSupplierStream (prime+K) width radius L w Fs))}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [headerReg 84,headerReg 85,capacityRows]
    (by simp [hcap,List.nodup_cons,hi.eq_iff]) v₂ F
  have hcost : 2*([headerReg 84,headerReg 85,capacityRows].map (fun r => (F.R r).length)).sum+
      2*[headerReg 84,headerReg 85,capacityRows].length+1 = 2*(a+b+2^b)+7 := by
    simp [F,M,gatherDimensionState,hcap,Function.update_of_ne (haway _),hi.eq_iff,b,Nat.add_assoc]
  rw [hcost] at he₃
  have hz81 := hblank 81 (by simp)
  have hz84 := hblank 84 (by simp)
  have hz85 := hblank 85 (by simp)
  have hend : {F with R := fun k => if k ∈ [headerReg 84,headerReg 85,capacityRows] then [] else F.R k} =
      {S with R := Function.update S.R (extra 1) (coreSupplierStream (prime+K) width radius L w Fs)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ [headerReg 84,headerReg 85,capacityRows]
    · simp only [List.mem_cons,List.not_mem_nil,or_false,hcap] at hk
      rcases hk with rfl | rfl | rfl <;> simp [hcap,Function.update_of_ne (haway _),hz81,hz84,hz85]
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
      simp [F,M,gatherDimensionState,hk.1,hk.2.1,hk.2.2,Function.update_apply]
  rw [hend] at he₃
  have he₃' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₂ F)+depth+0) depth
      (clearWords [headerReg 84,headerReg 85,capacityRows]) (mk v₂ F) (2*(a+b+2^b)+7)
      (mk v₃ {S with R := Function.update S.R (extra 1) (coreSupplierStream (prime+K) width radius L w Fs)}) :=
    mn_native_exec_within he₃ 0 (clearWords_native _) depth _ (by omega)
  refine ⟨v₃,n₁+(n₂+(2*(a+b+2^b)+7)),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · simpa only [countedGatherTimeCost,rows,b] using Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _)
  · simpa only [countedGatherProgram,countedGatherStockAllowance,M,gatherDimensionState,rows,b,Nat.add_zero] using
      mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃')

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
