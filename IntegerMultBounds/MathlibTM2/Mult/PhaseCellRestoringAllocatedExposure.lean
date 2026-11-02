module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLoadedExposureReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposureHeaderRetirement

/-! Load caller metadata, expose all replicas and retire the copied headers.
The exact final state changes only the caller output and restores the private bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T A : ℕ}

noncomputable def restoringAllocatedExposure {Q : ℕ} {P U : Type}
    (src : Fin 8 → Fin T) (input output : Fin T) : Pr P (T+175) Q A U :=
  .seq (loadExposureHeaders src) (.seq
    (replicaCoreGatherLoop (exposurePlacement output) (exposureControl input 0)
      (exposureControl input 1) (exposureControl input 2) (exposureControl input 3)
      (exposureControl input 4) (exposureControl input 5) (exposureControl input 6))
    (clearWords ((exposureHeaderCopies src).map Prod.snd)))

theorem restoringAllocatedExposure_exec_within {Q : ℕ} {P U : Type}
    (body : P → Pr P (T+175) Q A U) (src : Fin 8 → Fin T)
    (input output : Fin T) (hne : input ≠ output)
    (V s width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (borrowed : List (Fin (A+4))) (S : Stacks (T+175) A)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (hs : S.R (Fin.castAdd 175 (src 0)) = binSyms V s)
    (hw : S.R (Fin.castAdd 175 (src 1)) = binSyms V width)
    (hr : S.R (Fin.castAdd 175 (src 2)) = binSyms V radius)
    (hL : S.R (Fin.castAdd 175 (src 3)) = binSyms V L)
    (hV : (S.R (Fin.castAdd 175 (src 4))).length = V)
    (hword : (S.R (Fin.castAdd 175 (src 5))).length = w)
    (hcount : (S.R (Fin.castAdd 175 (src 6))).length = s*w)
    (hreplicas : (S.R (Fin.castAdd 175 (src 7))).length = Fs.length)
    (hsource : S.R (Fin.castAdd 175 input) = Fs.flatMap (fun C => cstream A w (chirpLine s C))++borrowed)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = [])
    (houtput : S.R (Fin.castAdd 175 output) = [])
    (v : HS (T+175) Q A U) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (6*exposureMetadataVolume src S+49)+
        (replicaCoreGatherLoopCost V s width radius L w Fs.length+(2*exposureMetadataVolume src S+17)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (2*(6*exposureMetadataVolume src S+49)+
          (Fs.length*(coreGatherIndices s width radius L).length*L*w+
            3*(replicaCoreGatherStepCost V s width radius L w+2)))) depth
        (restoringAllocatedExposure src input output) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (Fin.castAdd 175 output)
          (cstream A w (coreGatherPayload width radius L Fs.reverse)))}) := by
  obtain ⟨v₁,hu₁,he₁,hread,hprefix⟩ := loadExposureHeaders_exec_within body src v S hblank depth
  rw [exposureHeaderLoadCost_eq] at he₁
  let g := loadedExposureHeaders_ready src input output hne V s width radius L w Fs borrowed S
    hwidth hwide hLfit hwV hvol hA hVpos hgroup hs hw hr hL hV hword hcount hreplicas hsource hblank
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := g.exec body v₁ depth
  change n₂ ≤ replicaCoreGatherLoopCost V s width radius L w Fs.length at hn₂
  have hp : g.program (P := P) (U := U) (Q := Q) = replicaCoreGatherLoop (exposurePlacement output) (exposureControl input 0)
      (exposureControl input 1) (exposureControl input 2) (exposureControl input 3)
      (exposureControl input 4) (exposureControl input 5) (exposureControl input 6) := rfl
  simp only [hp,RealGatherExposureData.stockAllowance] at he₂
  have hg : g.e = exposurePlacement output := rfl
  rw [hg,exposurePlacement_output,hprefix output,houtput,List.append_nil] at he₂
  obtain ⟨v₃,hu₃,he₃⟩ := retireExposureHeaders_exec_within body src output
    (cstream A w (coreGatherPayload width radius L Fs.reverse)) v₂ S hblank depth
  refine ⟨v₃,(6*exposureMetadataVolume src S+49)+(n₂+(2*exposureMetadataVolume src S+17)),
    hu₃.trans (hu₂.trans hu₁),Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _,?_⟩
  have he := mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃)
  simpa only [restoringAllocatedExposure,Nat.add_zero] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
