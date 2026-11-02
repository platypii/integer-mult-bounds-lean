module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherHeaderRetirement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Load, route and retire in the concrete numerical/routing layout. The whole
call changes only the numerical supplier source and returns a fresh suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ} {P U : Type}

def restoringAllocatedGather (bank : ComputedClassBank → Fin T) (src : Fin 7 → Fin T)
    (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P (T+PackedTranspose.tapeCount) Q (prime+K) U :=
  .seq (loadGatherHeaders src) (.seq
    (embProg (gatherPlacement bank) Empty.elim (geometryGatherProgram (P := Empty) hstates))
    (clearWords ((gatherHeaderCopies src).map Prod.snd)))

theorem restoringAllocatedGather_exec_within
    (body : P → Pr P (T+PackedTranspose.tapeCount) Q (prime+K) U)
    (bank : ComputedClassBank → Fin T) (src : Fin 7 → Fin T)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (V s a width radius L w : ℕ)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hA : 4 ≤ prime+K) (hVpos : 0 < V) (hpacket : 0 < L*w)
    (hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < V)
    (hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^V)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a)
    (v : HS (T+PackedTranspose.tapeCount) Q (prime+K) U) (S : Stacks (T+PackedTranspose.tapeCount) (prime+K))
    (hs : S.R (Fin.castAdd PackedTranspose.tapeCount (src 0)) = binSyms V s)
    (hw : S.R (Fin.castAdd PackedTranspose.tapeCount (src 1)) = binSyms V width)
    (hr : S.R (Fin.castAdd PackedTranspose.tapeCount (src 2)) = binSyms V radius)
    (hL : S.R (Fin.castAdd PackedTranspose.tapeCount (src 3)) = binSyms V L)
    (hV : (S.R (Fin.castAdd PackedTranspose.tapeCount (src 4))).length = V)
    (hword : (S.R (Fin.castAdd PackedTranspose.tapeCount (src 5))).length = w)
    (hrep : (S.R (Fin.castAdd PackedTranspose.tapeCount (src 6))).length = 2^a)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) (hleft : ∀ i, S.L (Fin.natAdd T i) = [])
    (hsourceLeft : S.L (control (extendedBank bank) .source) = [])
    (hsource : S.R (control (extendedBank bank) .source) = cstream (prime+K) w (coreGatherPayload width radius L Fs))
    (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (6*gatherMetadataVolume src S+49)+(geometryGatherTimeCost hstates V s a width radius L w+
        (2*gatherMetadataVolume src S+17)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*(6*gatherMetadataVolume src S+49)+geometryGatherStockAllowance hstates V s a width radius L w)) depth
        (restoringAllocatedGather bank src hstates) (mk v S) n
        (mk v' {S with R := (Function.update S.R (control (extendedBank bank) .source)
          (coreSupplierStream (prime+K) width radius L w Fs))}) := by
  obtain ⟨v₁,hu₁,he₁,hread,hprefix⟩ := loadGatherHeaders_exec_within body src v S hblank depth
  rw [gatherHeaderLoadCost_eq] at he₁
  let M := loadedGatherHeaders src S
  have hready := loadedGatherHeaders_ready bank src V s a width radius L w S hs hw hr hL hV hword hrep hblank hleft hsourceLeft
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hready.exec body (gatherPlacement_injective bank) hstates
    hwidth hwide hLfit hA hVpos hpacket hbits hfit Fs hreplicas
    (by rw [gatherPlacement_source]; exact (hprefix (bank (.control .source))).trans hsource) v₁ depth
  simp only [gatherPlacement_source] at he₂
  obtain ⟨v₃,hu₃,he₃'⟩ := retireGatherHeaders_exec_within body src (bank (.control .source))
    (coreSupplierStream (prime+K) width radius L w Fs) v₂ S hblank depth
  rw [← show control (extendedBank bank) .source =
    Fin.castAdd PackedTranspose.tapeCount (bank (.control .source)) by
      simp only [control, extendedBank]] at he₃'
  refine ⟨v₃,(6*gatherMetadataVolume src S+49)+(n₂+(2*gatherMetadataVolume src S+17)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _,?_⟩
  unfold restoringAllocatedGather
  have he := mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃')
  rw [Nat.add_zero] at he
  exact he

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
