module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicPublicationTranspose
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

theorem prepare_rows_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
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
    ∃ paddedRows : Fin (2^a) → Fin (2^b) → List GaussianInt,
      (∀ i j, (paddedRows i j).length = L) ∧
      (∀ i j, paddedRows (paddedCoreIndex hcapacity i) j = rows i j) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ (6*(2^(a+b)*(L*w))+4*(S.R (extra 1)).length+4*(L*w)+9*(a+b)+14)+
        (26*(2^a*(2^b*(L*w)))+24+2*restoringTimeCost hstates a b (L*w) V) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*(6*(2^(a+b)*(L*w))+4*(S.R (extra 1)).length+4*(L*w)+9*(a+b)+14)+
        (40*(2^a*(2^b*(L*w)))+38+restoringStockAllowance hstates a b (L*w) V))) depth
        (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (program hstates)) (mk v S) n
        (mk v' {S with L := (fun _ => []), R := (Function.update S.R (extra 1)
          ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => paddedRows i j).flatten).flatten))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := ownedPrefixPadding_exec_within body exponent packet (extra 1) pad tmp saved
    hpadReg (pairSym (prime+K) false false) (a+b) (L*w) v S hexponent hpacketWidth hpad htmp hsaved depth
  let M : Stacks tapeCount (prime+K) := {S with R := (Function.update S.R (extra 1)
    (tilePrefixPad (2^(a+b)*(L*w)) (pairSym (prime+K) false false) (S.R (extra 1))))}
  have hstable (i : Fin tapeCount) (hi : i ≠ extra 1) : M.R i = S.R i := by
    simp only [M,Function.update_of_ne hi]
  have hvolume : 2^(a+b)*(L*w) = 2^a*(2^b*(L*w)) := by rw [pow_add,Nat.mul_assoc]
  have hcodecOff : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], i ≠ extra 1 := by
    have hr := codec_registers
    regs_ne hr
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | (apply Ne.symm; assumption)
  obtain ⟨paddedRows,hp,hreal,v₂,n₂,hu₂,hn₂,he₂⟩ := padded_rows_exec_within body hstates a b L w V
    hpacket hbits hfit hA hcapacity rows hlen depth v₁ M
    (by rw [hstable _ (base_extra _ _)]; exact ha)
    (by rw [hstable _ (base_extra _ _)]; exact hb)
    (by rw [hstable _ (base_extra _ _)]; exact hseed)
    (by rw [hstable _ (base_extra _ _)]; exact hz)
    (by rw [hstable _ (base_extra _ _)]; exact hwidth)
    (by intro r; rw [hstable _ (base_extra _ _)]; exact hblank r)
    (by rw [hstable _ (base_extra _ _)]; exact hstageCount) hL
    (by intro i hi hj; rw [hstable _ (base_extra _ _)]; exact hfresh i hi hj)
    (by simp only [M,Function.update_self,hvolume,hsrc])
    (by rw [hstable _ (by simp [extra,Fin.ext_iff])]; exact hcount)
    (by intro i hi; rw [hstable _ (hcodecOff i hi)]; exact hcodec i hi)
  refine ⟨paddedRows,hp,hreal,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  simpa only [M,Function.update_idem] using mn_seq_within_add he₁ he₂

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
