module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Execute header preparation, routing and header retirement. Readiness is
ordinary data about the explicitly prepared boundary state. -/
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

def gatherHeaderState (S : Stacks tapeCount (prime+K)) (a b C V : ℕ) : Stacks tapeCount (prime+K) :=
  {S with R := Function.update (Function.update (Function.update S.R
    (headerReg 97) (binSyms V a)) (headerReg 98) (binSyms V b)) (headerReg 102) (binSyms V C)}

def preparedGatherProgram (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P tapeCount Q (prime+K) U :=
  .seq gatherHeadersProgram (.seq (gatherProgram hstates)
    (clearWords [headerReg 97,headerReg 98,headerReg 102]))

theorem preparedGather_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b width radius L w V : ℕ)
    (hpacket : 0 < L*w) (hbits : a+b < V) (hfit : (L*w)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ 2^b)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a) (depth : ℕ)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hwidth : (S.R (headerReg 115)).length = V)
    (hsourceA : (S.R (headerReg 84)).length = a) (hsourceB : (S.R (headerReg 85)).length = b)
    (hsourceC : (S.R packetWidth).length = L*w)
    (hblank : ∀ i ∈ [(97 : Fin 117),98,102,40,41,42,43,44,45], S.R (headerReg i) = [])
    (hready : GatherReady id s a b width radius L w V (gatherHeaderState S a b (L*w) V))
    (hsrc : S.R (extra 1) = cstream (prime+K) w (coreGatherPayload width radius L Fs)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (21*(a+b+L*w)+36*V+85)+(gatherRouteTimeCost hstates s a b width radius L w V+(6*V+7)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*(21*(a+b+L*w)+36*V+85)+gatherRouteStockAllowance hstates s a b width radius L w V))
        depth (preparedGatherProgram hstates) (mk v S) n
        (mk v' {S with R := (Function.update S.R (extra 1)
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  have ha : Nat.size a ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have hb : Nat.size b ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have hC : Nat.size (L*w) ≤ V := Nat.size_le.mpr
    ((Nat.le_mul_of_pos_right (L*w) (Nat.two_pow_pos (a+b))).trans_lt hfit)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := gatherHeaders_exec_within body a b (L*w) V ha hb hC depth v S
    hwidth hsourceA hsourceB hsourceC hblank
  let M := gatherHeaderState S a b (L*w) V
  have hsrcM : M.R (extra 1) = cstream (prime+K) w (coreGatherPayload width radius L Fs) := by
    simpa [M,gatherHeaderState,headerReg,Function.update_of_ne (base_extra _ 1).symm] using hsrc
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := gatherRoute_exec_within body hstates a b width radius L w V
    hpacket hbits hfit hA hcapacity Fs hreplicas depth v₁ M
    hready.ha hready.hb hready.hseed hready.hz hready.hwidth hready.hblank hready.hstageCount hready.hL
    hready.hfresh hsrcM hready.hrows hready.hcap hready.hpw hready.hrep hready.hcodec
  have hleft : (fun _ => []) = S.L := funext (fun i => (hready.hL i).symm)
  let F : Stacks tapeCount (prime+K) := {M with R := (Function.update M.R (extra 1)
    (coreSupplierStream (prime+K) width radius L w Fs))}
  rw [hleft] at he₂
  have hi := headerReg_injective
  have haway (j : Fin 117) : headerReg j ≠ extra 1 := base_extra _ 1
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [headerReg 97,headerReg 98,headerReg 102]
    (by simp [List.nodup_cons,hi.eq_iff]) v₂ F
  have hcost : 2*([headerReg 97,headerReg 98,headerReg 102].map (fun r => (F.R r).length)).sum+
      2*[headerReg 97,headerReg 98,headerReg 102].length+1 = 6*V+7 := by
    simp [F,M,gatherHeaderState,Function.update_of_ne (haway _),hi.eq_iff,length_binSyms]
    omega
  rw [hcost] at he₃
  have hz97 := hblank 97 (by simp)
  have hz98 := hblank 98 (by simp)
  have hz102 := hblank 102 (by simp)
  have hend : {F with R := fun k => if k ∈ [headerReg 97,headerReg 98,headerReg 102] then [] else F.R k} =
      {S with R := Function.update S.R (extra 1) (coreSupplierStream (prime+K) width radius L w Fs)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ [headerReg 97,headerReg 98,headerReg 102]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;>
        simp [Function.update_of_ne (haway _),hz97,hz98,hz102]
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
      simp [F,M,gatherHeaderState,hk.1,hk.2.1,hk.2.2,Function.update_apply]
  rw [hend] at he₃
  have he₃' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₂ F)+depth+0) depth
      (clearWords [headerReg 97,headerReg 98,headerReg 102]) (mk v₂ F) (6*V+7)
      (mk v₃ {S with R := Function.update S.R (extra 1) (coreSupplierStream (prime+K) width radius L w Fs)}) :=
    mn_native_exec_within he₃ 0 (clearWords_native _) depth _ (by omega)
  have ht := mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃')
  refine ⟨v₃,n₁+(n₂+(6*V+7)),hu₃.trans (hu₂.trans hu₁),Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _),?_⟩
  simpa only [preparedGatherProgram,M,gatherHeaderState,Nat.add_zero] using ht

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
