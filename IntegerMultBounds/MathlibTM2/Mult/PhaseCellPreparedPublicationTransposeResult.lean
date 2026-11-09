module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationTranspose
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTile
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPaddingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! Actual owned-prefix padding followed by the fixed-bank publication
transpose. All transpose readiness follows from the padding program's frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank
variable {Q K N : ℕ} {P U : Type}

theorem prepare_rows_result_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L w V : ℕ)
    (hpacket : 0 < L*w) (hbits : a+b < V) (hfit : (L*w)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (exponent packet pad tmp saved : Fin tapeCount)
    (hpadReg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (hcapacity : N ≤ 2^a)
    (rows : Fin N → Fin (2^b) → List GaussianInt)
    (hlen : ∀ i j, (rows i j).length = L) (depth : ℕ)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hexponent : (S.R exponent).length = a+b) (hpacketWidth : (S.R packet).length = L*w)
    (hpad : S.R pad = []) (htmp : S.R tmp = []) (hsaved : S.R saved = [])
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V (L*w))
    (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hstageCount : S.R (base (callerGenerator 116)) = []) (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hsrc : S.R (extra 1) =
      (List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten)
    (hcount : S.R (extra 4) = [])
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R i = []) :
    ∃ tile : ArchiveTilePlan.Result L rows, tile.capacity = 2^a ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ (6*(2^(a+b)*(L*w))+4*(S.R (extra 1)).length+4*(L*w)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*w)))+24+2*restoringTimeCost hstates a b (L*w) V) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*(6*(2^(a+b)*(L*w))+4*(S.R (extra 1)).length+4*(L*w)+9*(a+b)+14)+
        (40*(2^a*(2^b*(L*w)))+38+restoringStockAllowance hstates a b (L*w) V))) depth
        (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (program hstates)) (mk v S) n
        (mk v' {S with L := (fun _ => []), R := (Function.update S.R (extra 1)
          ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => tile.padded i j).flatten).flatten))}) := by
  obtain ⟨padded,hp,hreal,v',n,hu,ht,he⟩ := prepare_rows_exec_within body hstates a b L w V
    hpacket hbits hfit hA exponent packet pad tmp saved hpadReg hcapacity rows hlen depth v S
    hexponent hpacketWidth hpad htmp hsaved ha hb hseed hz hwidth hblank hstageCount hL hfresh hsrc hcount hcodec
  exact ⟨⟨2^a,hcapacity,padded,hp,hreal⟩,rfl,v',n,hu,ht,he⟩

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
