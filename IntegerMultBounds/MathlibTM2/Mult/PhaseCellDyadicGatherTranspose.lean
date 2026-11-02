module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicCoefficientTranspose
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherRows

/-! The actual dyadic router consumes the padded gather archive and returns
core-major batches with the existing supplier identities. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q K s : ℕ} {P U : Type}

theorem gathered_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b width radius L w V : ℕ)
    (hpacket : 0 < L*w) (hbits : a+b < V) (hfit : (L*w)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ 2^b)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a) (depth : ℕ)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V (L*w))
    (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hstageCount : S.R (base (callerGenerator 116)) = []) (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hsrc : S.R (extra 1) = cstream (prime+K) w (paddedCoreGatherPayload (2^b) width radius L Fs))
    (hcount : S.R (extra 4) = [])
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R i = []) :
    ∃ rows : Fin (2^b) → Fin (2^a) → List GaussianInt,
      (∀ i j, (rows i j).length = L) ∧
      (∀ i : Fin (coreGatherIndices s width radius L).length,
        (List.ofFn fun j => cstream (prime+K) w (rows (paddedCoreIndex hcapacity i) j)).flatten =
          cstream (prime+K) w (Fs.map (packedInterval
            (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ 26*(2^a*(2^b*(L*w)))+24+2*restoringTimeCost hstates a b (L*w) V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (40*(2^a*(2^b*(L*w)))+38+restoringStockAllowance hstates a b (L*w) V)) depth
        (program hstates) (mk v S) n
        (mk v' {S with L := (fun _ => []), R := (Function.update S.R (extra 1)
          ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten))}) := by
  obtain ⟨rows,hlen,hbatches,hin,hout⟩ := paddedGatherRows_dyadic (A := prime+K)
    a b width radius L w hcapacity Fs hreplicas
  let f := fun j i (k : Fin L) => (rows i j)[k.val]'(by rw [hlen]; exact k.isLt)
  have he := coefficient_exec_within body hstates a b L w V hpacket hbits hfit hA f depth v S
    ha hb hseed hz hwidth hblank hstageCount hL hfresh (hsrc.trans hin) hcount hcodec
  change cstream (prime+K) w (keyReplicaWords f) = _ at hout
  rw [hout] at he
  exact ⟨rows,hlen,hbatches,he⟩

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
