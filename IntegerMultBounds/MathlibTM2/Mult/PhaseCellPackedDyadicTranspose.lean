module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedTransposePlanes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPayloadStock

/-! Packed complex-symbol transposition through the existing pair codec and
actual shared-bank real/imaginary routes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank
variable {Q K : ℕ} {P U : Type}

theorem codec_registers : [extra 1,planeReg false,planeReg true,extra 2,extra 3,extra 4,extra 5,extra 6].Nodup := by
  have ho := owned.isLt
  simp [List.nodup_cons,planeReg,base,extra,Fin.ext_iff]
  omega

def codecProgram (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P tapeCount Q (prime+K) U :=
  packedRouterUsing (extra 1) (planeReg false) (planeReg true) (extra 2) (extra 3) (extra 4) (extra 5) (extra 6)
    (planesProgram hstates)

theorem codec_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b C V : ℕ)
    (hC : 0 < C) (hbits : a+b < V) (hfit : C*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (realBits imagBits : Fin (2^a) → Fin (2^b) → Fin C → Bool) (depth : ℕ)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V C)
    (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hstageCount : S.R (base (callerGenerator 116)) = []) (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hsrc : S.R (extra 1) = replicaKeyWords (fun r k i => pairSym (prime+K) (realBits r k i) (imagBits r k i)))
    (hcount : (S.R (extra 4)).length = 2^a*(2^b*C))
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 22*(2^a*(2^b*C))+20+2*restoringTimeCost hstates a b C V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (32*(2^a*(2^b*C))+30+restoringStockAllowance hstates a b C V)) depth
        (codecProgram hstates) (mk v S) n
        (mk v' {S with L := (fun _ => []), R := (Function.update (Function.update S.R (extra 1)
          (keyReplicaWords (fun r k i => pairSym (prime+K) (realBits r k i) (imagBits r k i)))) (extra 4) [])}) := by
  obtain ⟨v',n,hu,hn,ht⟩ := packedRouterUsing_exec_within (body := body)
    (extra 1) (planeReg false) (planeReg true) (extra 2) (extra 3) (extra 4) (extra 5) (extra 6)
    codec_registers hA realBits imagBits (planesProgram hstates) (2*restoringTimeCost hstates a b C V)
    (restoringStockAllowance hstates a b C V) depth v S hsrc hcount hcodec (by
      intro u
      let M := packedRouterPlaneInput S (planeReg false) (planeReg true) realBits imagBits
      have hmeta (j : Fin 117) : M.R (base (callerGenerator j)) = S.R (base (callerGenerator j)) := by
        have hr : base (callerGenerator j) ≠ planeReg false := base_injective.ne (payload_off_generator j)
        have hi : base (callerGenerator j) ≠ planeReg true := base_extra _ 0
        simp only [M,packedRouterPlaneInput,Function.update_of_ne hi,Function.update_of_ne hr]
      obtain ⟨u',m,hu,hm,he⟩ := planes_exec_within body hstates a b C V hC hbits hfit realBits imagBits depth u M
        (by rw [hmeta]; exact ha) (by rw [hmeta]; exact hb) (by rw [hmeta]; exact hseed)
        (by rw [hmeta]; exact hz) (by rw [hmeta]; exact hwidth)
        (by intro r; rw [hmeta]; exact hblank r) (by rw [hmeta]; exact hstageCount) hL
        (by
          intro i hip hiq
          have hr : base (callerWorker i) ≠ planeReg false :=
            base_injective.ne (TransposeRegisterPlacement.worker_injective.ne hip)
          have hi : base (callerWorker i) ≠ planeReg true := base_extra _ 0
          simp only [M,packedRouterPlaneInput,Function.update_of_ne hi,Function.update_of_ne hr]
          exact hfresh i hip hiq)
        (by simp only [M,packedRouterPlaneInput,Function.update_of_ne planeReg_ne,Function.update_self,replicaKeyWords_map])
        (by simp only [M,packedRouterPlaneInput,Function.update_self,replicaKeyWords_map])
      refine ⟨u',m,hu,hm,he.cast rfl ?_⟩
      apply congrArg (mk u')
      refine Stacks.ext (by rfl) (by rfl) (funext hL) ?_
      simp only [packedRouterPlaneOutput,M,keyReplicaWords_map])
  refine ⟨v',n,hu,by omega,?_⟩
  exact ht.mono (by intro d z hz; omega)

def program (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P tapeCount Q (prime+K) U :=
  withPayloadCounter (extra 1) (extra 4) (extra 3) (codecProgram hstates)

theorem exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b C V : ℕ)
    (hC : 0 < C) (hbits : a+b < V) (hfit : C*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (realBits imagBits : Fin (2^a) → Fin (2^b) → Fin C → Bool) (depth : ℕ)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V C)
    (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hstageCount : S.R (base (callerGenerator 116)) = []) (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hsrc : S.R (extra 1) = replicaKeyWords (fun r k i => pairSym (prime+K) (realBits r k i) (imagBits r k i)))
    (hcount : S.R (extra 4) = [])
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 26*(2^a*(2^b*C))+24+2*restoringTimeCost hstates a b C V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (40*(2^a*(2^b*C))+38+restoringStockAllowance hstates a b C V)) depth
        (program hstates) (mk v S) n
        (mk v' {S with L := (fun _ => []), R := (Function.update S.R (extra 1)
          (keyReplicaWords (fun r k i => pairSym (prime+K) (realBits r k i) (imagBits r k i))))}) := by
  have hr := codec_registers
  regs_ne hr
  let volume := 2^a*(2^b*C)
  obtain ⟨v',n,hu,hn,ht⟩ := withPayloadCounter_exec_within (body := body) (extra 1) (extra 4) (extra 3)
    (by regs_nodup) volume (keyReplicaWords (fun r k i => pairSym (prime+K) (realBits r k i) (imagBits r k i)))
    (codecProgram hstates) (22*volume+20+2*restoringTimeCost hstates a b C V)
    (32*volume+30+restoringStockAllowance hstates a b C V) depth v S
    (by simp [hsrc,replicaKeyWords,volume]) hcount (hcodec _ (by simp)) (by
      intro u
      have hbases (j : Fin kernelT) :
          (payloadCountedState S (extra 4) volume).R (base j) = S.R (base j) :=
        Function.update_of_ne (base_extra j 4) _ _
      have hcodecOff : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], i ≠ extra 4 := by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | assumption | (apply Ne.symm; assumption)
      have he := codec_exec_within body hstates a b C V hC hbits hfit hA realBits imagBits depth u
        (payloadCountedState S (extra 4) volume)
        (by rw [hbases]; exact ha) (by rw [hbases]; exact hb) (by rw [hbases]; exact hseed)
        (by rw [hbases]; exact hz) (by rw [hbases]; exact hwidth)
        (by intro r; rw [hbases]; exact hblank r) (by rw [hbases]; exact hstageCount) hL
        (by intro i hip hiq; rw [hbases]; exact hfresh i hip hiq)
        (by simpa only [payloadCountedState,Function.update_of_ne ‹extra 1 ≠ extra 4›] using hsrc)
        (by simp [payloadCountedState,volume])
        (by intro i hi; simpa only [payloadCountedState,Function.update_of_ne (hcodecOff i hi)] using hcodec i hi)
      exact he)
  refine ⟨v',n,hu,by dsimp [volume] at hn; omega,?_⟩
  exact ht.mono (by intro d z hz; dsimp [volume] at hz; omega)

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
