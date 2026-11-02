module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedRestoringExposure
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringAllocatedGather

/-! Actual exposure and geometry routing use disjoint private suffixes.
Both suffixes are restored and only the numerical supplier source changes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T : ℕ}

noncomputable def exposureIntoRouting (T : ℕ) : Fin (T+175) → Fin ((T+175)+PackedTranspose.tapeCount) :=
  Fin.castAdd PackedTranspose.tapeCount


theorem restoringExposedGather_exec_within {Q K : ℕ} {P U : Type}
    (body : P → Pr P ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U)
    (src : Fin 8 → Fin T)
    (input output : Fin T) (hne : input ≠ output)
    (V s width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (borrowed : List (Fin (prime+K+4))) (S : Stacks ((T+175)+PackedTranspose.tapeCount) (prime+K))
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ prime+K) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (hs : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (src 0)) = binSyms V s)
    (hw : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (src 1)) = binSyms V width)
    (hr : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (src 2)) = binSyms V radius)
    (hL : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (src 3)) = binSyms V L)
    (hV : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (src 4))).length = V)
    (hword : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (src 5))).length = w)
    (hcount : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (src 6))).length = s*w)
    (hreplicas : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (src 7))).length = Fs.length)
    (hsource : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 input) = Fs.flatMap (fun C => cstream (prime+K) w (chirpLine s C))++borrowed)
    (hblank : ∀ i, (embStk (exposureIntoRouting T) S).R (Fin.natAdd T i) = [])
    (houtput : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 output) = [])
    (bank : ComputedClassBank → Fin (T+175)) (routeSrc : Fin 7 → Fin (T+175))
    (hstates : FixedStreamedBank.stateCount ≤ Q) (D a : ℕ)
    (houtputBank : control (extendedBank bank) .source = exposureIntoRouting T (Fin.castAdd 175 output))
    (hmetaOff : ∀ i, routeSrc i ≠ bank (.control .source))
    (hDwide : s+width+2*radius < 2^D) (hDLfit : L < 2^D) (hDpos : 0 < D)
    (hpacket : 0 < L*w) (hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < D)
    (hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^D)
    (hpower : Fs.length = 2^a)
    (hRs : S.R (Fin.castAdd PackedTranspose.tapeCount (routeSrc 0)) = binSyms D s)
    (hRw : S.R (Fin.castAdd PackedTranspose.tapeCount (routeSrc 1)) = binSyms D width)
    (hRr : S.R (Fin.castAdd PackedTranspose.tapeCount (routeSrc 2)) = binSyms D radius)
    (hRL : S.R (Fin.castAdd PackedTranspose.tapeCount (routeSrc 3)) = binSyms D L)
    (hRV : (S.R (Fin.castAdd PackedTranspose.tapeCount (routeSrc 4))).length = D)
    (hRword : (S.R (Fin.castAdd PackedTranspose.tapeCount (routeSrc 5))).length = w)
    (hRrep : (S.R (Fin.castAdd PackedTranspose.tapeCount (routeSrc 6))).length = 2^a)
    (hRblank : ∀ i, S.R (Fin.natAdd (T+175) i) = [])
    (hRleft : ∀ i, S.L (Fin.natAdd (T+175) i) = [])
    (hsourceLeft : S.L (control (extendedBank bank) .source) = [])
    (v : HS ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ ((6*exposureMetadataVolume src (embStk (exposureIntoRouting T) S)+49)+
        (replicaCoreGatherLoopCost V s width radius L w Fs.length+
          (2*exposureMetadataVolume src (embStk (exposureIntoRouting T) S)+17)))+
        ((6*gatherMetadataVolume routeSrc S+49)+(geometryGatherTimeCost hstates D s a width radius L w+
          (2*gatherMetadataVolume routeSrc S+17))) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((2*(6*exposureMetadataVolume src (embStk (exposureIntoRouting T) S)+49)+
          (Fs.length*(coreGatherIndices s width radius L).length*L*w+
            3*(replicaCoreGatherStepCost V s width radius L w+2)))+
          (2*(6*gatherMetadataVolume routeSrc S+49)+geometryGatherStockAllowance hstates D s a width radius L w))) depth
        (.seq (embProg (exposureIntoRouting T) Empty.elim (restoringAllocatedExposure (P := Empty) src input output))
          (restoringAllocatedGather bank routeSrc hstates)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (control (extendedBank bank) .source)
          (coreSupplierStream (prime+K) width radius L w Fs.reverse))}) := by
  have hinj : Function.Injective (exposureIntoRouting T) := by
    intro i j he
    apply Fin.ext
    have hv := congrArg (fun k : Fin ((T+175)+PackedTranspose.tapeCount) => k.val) he
    simpa only [exposureIntoRouting,Fin.val_castAdd] using hv
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := placedRestoringAllocatedExposure_exec_within body
    (exposureIntoRouting T) hinj src input output hne V s width radius L w Fs borrowed S
    hwidth hwide hLfit hwV hvol hA hVpos hgroup hs hw hr hL hV hword hcount hreplicas hsource hblank houtput v depth
  rw [←houtputBank] at he₁
  let F : Stacks ((T+175)+PackedTranspose.tapeCount) (prime+K) := {S with R :=
    (Function.update S.R (control (extendedBank bank) .source)
      (cstream (prime+K) w (coreGatherPayload width radius L Fs.reverse)))}
  have hmeta (i : Fin 7) : F.R (Fin.castAdd PackedTranspose.tapeCount (routeSrc i)) =
      S.R (Fin.castAdd PackedTranspose.tapeCount (routeSrc i)) := by
    apply Function.update_of_ne
    intro he
    apply hmetaOff i
    simp only [ComputedClassBanks.control,extendedBank] at he
    apply Fin.ext
    have hv := congrArg (fun j : Fin ((T+175)+PackedTranspose.tapeCount) => j.val) he
    simpa only [Fin.val_castAdd] using hv
  have hfresh (i) : F.R (Fin.natAdd (T+175) i) = [] := by
    rw [show F.R (Fin.natAdd (T+175) i) = S.R (Fin.natAdd (T+175) i) from
      Function.update_of_ne (prefix_ne_routing (bank (.control .source)) i).symm _ _]
    exact hRblank i
  have hvolume : gatherMetadataVolume routeSrc F = gatherMetadataVolume routeSrc S := by
    unfold gatherMetadataVolume gatherHeaderCopies
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro r hr
    exact congrArg List.length (hmeta r.1)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := restoringAllocatedGather_exec_within body bank routeSrc hstates
    D s a width radius L w hwidth hDwide hDLfit hA hDpos hpacket hbits hfit
    Fs.reverse (by simpa only [List.length_reverse] using hpower) v₁ F
    ((hmeta 0).trans hRs) ((hmeta 1).trans hRw) ((hmeta 2).trans hRr) ((hmeta 3).trans hRL)
    (by rw [hmeta 4]; exact hRV) (by rw [hmeta 5]; exact hRword) (by rw [hmeta 6]; exact hRrep)
    hfresh hRleft hsourceLeft (Function.update_self _ _ _) depth
  rw [hvolume] at hn₂ he₂
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  simpa only [F,Function.update_idem] using mn_seq_within_add he₁ he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
