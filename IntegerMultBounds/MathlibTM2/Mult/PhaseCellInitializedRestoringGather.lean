module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposedClassGeometryFrame

/-! Execute the actual restoring exposure/router preparation after numerical
geometry initialization. All preparation readbacks and bills are transported. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T : ℕ}

theorem initializedRestoringGather_exec_within {Q K : ℕ} {P U : Type}
    (body : P → Pr P ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U)
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (exposeSrc : Fin 8 → Fin T) (hExposeOff : ∀ i k, exposeSrc i ≠ bank k)
    (input : Fin T) (hInputOff : ∀ k, input ≠ bank k)
    (V s width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (borrowed : List (Fin (prime+K+4))) (S : Stacks ((T+175)+PackedTranspose.tapeCount) (prime+K))
    (initSrc : Fin 4 → Fin ((T+175)+PackedTranspose.tapeCount))
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ prime+K) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (hs : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 0)) = binSyms V s)
    (hw : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 1)) = binSyms V width)
    (hr : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 2)) = binSyms V radius)
    (hL : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 3)) = binSyms V L)
    (hV : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 4))).length = V)
    (hword : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 5))).length = w)
    (hcount : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 6))).length = s*w)
    (hreplicas : ((embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc 7))).length = Fs.length)
    (hsource : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 input) = Fs.flatMap (fun C => cstream (prime+K) w (chirpLine s C))++borrowed)
    (hblank : ∀ i, (embStk (exposureIntoRouting T) S).R (Fin.natAdd T i) = [])
    (houtput : (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (bank (.control .source))) = [])
    (routeSrc : Fin 7 → Fin T) (hRouteOff : ∀ i k, routeSrc i ≠ bank k)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (D a : ℕ)
    (hDwide : s+width+2*radius < 2^D) (hDLfit : L < 2^D) (hDpos : 0 < D)
    (hpacket : 0 < L*w) (hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < D)
    (hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^D)
    (hpower : Fs.length = 2^a)
    (hRs : S.R (classCallerRegister (routeSrc 0)) = binSyms D s)
    (hRw : S.R (classCallerRegister (routeSrc 1)) = binSyms D width)
    (hRr : S.R (classCallerRegister (routeSrc 2)) = binSyms D radius)
    (hRL : S.R (classCallerRegister (routeSrc 3)) = binSyms D L)
    (hRV : (S.R (classCallerRegister (routeSrc 4))).length = D)
    (hRword : (S.R (classCallerRegister (routeSrc 5))).length = w)
    (hRrep : (S.R (classCallerRegister (routeSrc 6))).length = 2^a)
    (hRblank : ∀ i, S.R (Fin.natAdd (T+175) i) = [])
    (hRleft : ∀ i, S.L (Fin.natAdd (T+175) i) = [])
    (hsourceLeft : S.L (control (fullExposedClassBank bank) .source) = [])
    (v : HS ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U) (depth : ℕ) :
    let M := loadedClassGeometry (fullExposedClassBank bank) initSrc S
    ∃ v' n, v'.user = v.user ∧
      n ≤ ((6*exposureMetadataVolume exposeSrc (embStk (exposureIntoRouting T) S)+49)+
        (replicaCoreGatherLoopCost V s width radius L w Fs.length+
          (2*exposureMetadataVolume exposeSrc (embStk (exposureIntoRouting T) S)+17)))+
        ((6*gatherMetadataVolume (fun i => Fin.castAdd 175 (routeSrc i)) S+49)+(geometryGatherTimeCost hstates D s a width radius L w+
          (2*gatherMetadataVolume (fun i => Fin.castAdd 175 (routeSrc i)) S+17))) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v M)+depth+
        ((2*(6*exposureMetadataVolume exposeSrc (embStk (exposureIntoRouting T) S)+49)+
          (Fs.length*(coreGatherIndices s width radius L).length*L*w+
            3*(replicaCoreGatherStepCost V s width radius L w+2)))+
          (2*(6*gatherMetadataVolume (fun i => Fin.castAdd 175 (routeSrc i)) S+49)+geometryGatherStockAllowance hstates D s a width radius L w))) depth
        (.seq (embProg (exposureIntoRouting T) Empty.elim (restoringAllocatedExposure (P := Empty) exposeSrc input (bank (.control .source))))
          (restoringAllocatedGather (exposedClassBank bank) (fun i => Fin.castAdd 175 (routeSrc i)) hstates)) (Host.mk v M) n
        (Host.mk v' {M with R := (Function.update M.R (control (fullExposedClassBank bank) .source)
          (coreSupplierStream (prime+K) width radius L w Fs.reverse))}) := by
  dsimp only
  let M := loadedClassGeometry (fullExposedClassBank bank) initSrc S
  have hcaller (k : Fin T) (hk : ∀ i, k ≠ bank i) :
      M.R (classCallerRegister k) = S.R (classCallerRegister k) :=
    loadedClassGeometry_caller bank initSrc S k hk
  have hE (i : Fin 8) : (embStk (exposureIntoRouting T) M).R (Fin.castAdd 175 (exposeSrc i)) =
      (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 (exposeSrc i)) := by
    simpa only [embStk,classCallerRegister,Function.comp_apply] using hcaller _ (hExposeOff i)
  have hR (i : Fin 7) : M.R (classCallerRegister (routeSrc i)) = S.R (classCallerRegister (routeSrc i)) :=
    hcaller _ (hRouteOff i)
  have hOut : (embStk (exposureIntoRouting T) M).R (Fin.castAdd 175 (bank (.control .source))) = [] := by
    have hh := loadedClassGeometry_bank_off (fullExposedClassBank bank)
      (fullExposedClassBank_injective bank hinj) initSrc S (.control .source) (by decide)
    rw [fullExposedClassBank_apply] at hh
    exact hh.trans houtput
  have hEB (i) : (embStk (exposureIntoRouting T) M).R (Fin.natAdd T i) = [] :=
    (loadedClassGeometry_exposure bank initSrc S i).trans (hblank i)
  have hRB (i) : M.R (Fin.natAdd (T+175) i) = [] :=
    (loadedClassGeometry_routing bank initSrc S i).trans (hRblank i)
  have hmetaOff (i : Fin 7) : Fin.castAdd 175 (routeSrc i) ≠ exposedClassBank bank (.control .source) := by
    intro he
    apply hRouteOff i (.control .source)
    apply Fin.ext
    have hv := congrArg (fun j : Fin (T+175) => j.val) he
    simpa only [exposedClassBank,Fin.val_castAdd] using hv
  have hEV : exposureMetadataVolume exposeSrc (embStk (exposureIntoRouting T) M) =
      exposureMetadataVolume exposeSrc (embStk (exposureIntoRouting T) S) := by
    unfold exposureMetadataVolume exposureHeaderCopies
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro r hr
    exact congrArg List.length (hE r.1)
  have hRV' : gatherMetadataVolume (fun i => Fin.castAdd 175 (routeSrc i)) M =
      gatherMetadataVolume (fun i => Fin.castAdd 175 (routeSrc i)) S := by
    unfold gatherMetadataVolume gatherHeaderCopies
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro r hr
    exact congrArg List.length (hR r.1)
  obtain ⟨v',n,hu,hn,he⟩ := restoringExposedGather_exec_within body exposeSrc input (bank (.control .source))
    (hInputOff (.control .source)) V s width radius L w Fs borrowed M
    hwidth hwide hLfit hwV hvol hA hVpos hgroup
    ((hE 0).trans hs) ((hE 1).trans hw) ((hE 2).trans hr) ((hE 3).trans hL)
    (by rw [hE 4]; exact hV) (by rw [hE 5]; exact hword)
    (by rw [hE 6]; exact hcount) (by rw [hE 7]; exact hreplicas)
    ((hcaller input hInputOff).trans hsource) hEB hOut
    (exposedClassBank bank) (fun i => Fin.castAdd 175 (routeSrc i)) hstates D a
    (exposedClassBank_source bank) hmetaOff hDwide hDLfit hDpos hpacket hbits hfit hpower
    ((hR 0).trans hRs) ((hR 1).trans hRw) ((hR 2).trans hRr) ((hR 3).trans hRL)
    (by simpa only [classCallerRegister,exposureIntoRouting] using (congrArg List.length (hR 4)).trans hRV) (by simpa only [classCallerRegister,exposureIntoRouting] using (congrArg List.length (hR 5)).trans hRword) (by simpa only [classCallerRegister,exposureIntoRouting] using (congrArg List.length (hR 6)).trans hRrep)
    hRB hRleft hsourceLeft v depth
  rw [hEV,hRV'] at hn he
  exact ⟨v',n,hu,hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
