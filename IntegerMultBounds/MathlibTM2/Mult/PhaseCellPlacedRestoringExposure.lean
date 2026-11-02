module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringAllocatedExposure
public import IntegerMultBounds.MathlibTM2.Host.EmbedOwnedUpdateStock

/-! Place complete restoring exposure over arbitrary surrounding storage.
The exact output update and full resource allowance survive the embedding. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T A : ℕ}

theorem placedRestoringAllocatedExposure_exec_within {T' Q : ℕ} {P U : Type}
    (body : P → Pr P T' Q A U)
    (e : Fin (T+175) → Fin T') (he : Function.Injective e) (src : Fin 8 → Fin T)
    (input output : Fin T) (hne : input ≠ output)
    (V s width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (borrowed : List (Fin (A+4))) (S : Stacks T' A)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (hs : (embStk e S).R (Fin.castAdd 175 (src 0)) = binSyms V s)
    (hw : (embStk e S).R (Fin.castAdd 175 (src 1)) = binSyms V width)
    (hr : (embStk e S).R (Fin.castAdd 175 (src 2)) = binSyms V radius)
    (hL : (embStk e S).R (Fin.castAdd 175 (src 3)) = binSyms V L)
    (hV : ((embStk e S).R (Fin.castAdd 175 (src 4))).length = V)
    (hword : ((embStk e S).R (Fin.castAdd 175 (src 5))).length = w)
    (hcount : ((embStk e S).R (Fin.castAdd 175 (src 6))).length = s*w)
    (hreplicas : ((embStk e S).R (Fin.castAdd 175 (src 7))).length = Fs.length)
    (hsource : (embStk e S).R (Fin.castAdd 175 input) = Fs.flatMap (fun C => cstream A w (chirpLine s C))++borrowed)
    (hblank : ∀ i, (embStk e S).R (Fin.natAdd T i) = [])
    (houtput : (embStk e S).R (Fin.castAdd 175 output) = [])
    (v : HS T' Q A U) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (6*exposureMetadataVolume src (embStk e S)+49)+
        (replicaCoreGatherLoopCost V s width radius L w Fs.length+(2*exposureMetadataVolume src (embStk e S)+17)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (2*(6*exposureMetadataVolume src (embStk e S)+49)+
          (Fs.length*(coreGatherIndices s width radius L).length*L*w+
            3*(replicaCoreGatherStepCost V s width radius L w+2)))) depth
        (embProg e Empty.elim (restoringAllocatedExposure (P := Empty) src input output)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (e (Fin.castAdd 175 output))
          (cstream A w (coreGatherPayload width radius L Fs.reverse)))}) := by
  obtain ⟨v₁,n,hu,hn,ht⟩ := restoringAllocatedExposure_exec_within (fun z : Empty => nomatch z)
    src input output hne V s width radius L w Fs borrowed (embStk e S)
    hwidth hwide hLfit hwV hvol hA hVpos hgroup hs hw hr hL hV hword hcount hreplicas hsource hblank houtput
    (embDn e v) depth
  obtain ⟨v',hu',ht'⟩ := exec_emb_owned_update_within e he (fun z : Empty => nomatch z)
    (Fin.castAdd 175 output) (cstream A w (coreGatherPayload width radius L Fs.reverse)) v S ht
  exact ⟨v',n,hu'.trans hu,hn,ht'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
