module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicCoefficientTranspose
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileData

/-! Execute the fixed-bank transpose directly on computed list rows. Array
entries and packet identities are derived from uniform row lengths. -/
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

theorem rows_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L w V : ℕ)
    (hpacket : 0 < L*w) (hbits : a+b < V) (hfit : (L*w)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (rows : Fin (2^a) → Fin (2^b) → List GaussianInt)
    (hlen : ∀ i j, (rows i j).length = L) (depth : ℕ)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V (L*w))
    (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hstageCount : S.R (base (callerGenerator 116)) = []) (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hsrc : S.R (extra 1) = (List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten)
    (hcount : S.R (extra 4) = [])
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 26*(2^a*(2^b*(L*w)))+24+2*restoringTimeCost hstates a b (L*w) V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (40*(2^a*(2^b*(L*w)))+38+restoringStockAllowance hstates a b (L*w) V)) depth
        (program hstates) (mk v S) n
        (mk v' {S with L := (fun _ => []), R := (Function.update S.R (extra 1)
          ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => rows i j).flatten).flatten))}) := by
  have he := coefficient_exec_within body hstates a b L w V hpacket hbits hfit hA
    (fun i j (k : Fin L) => (rows i j)[k.val]'(by rw [hlen]; exact k.isLt)) depth v S ha hb hseed hz hwidth hblank hstageCount hL hfresh
    (hsrc.trans (archiveRows_cstream w rows hlen).symm) hcount hcodec
  rw [routedArchiveRows_cstream w rows hlen] at he
  exact he

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
