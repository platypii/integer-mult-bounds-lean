module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLoadedStandardBoundaryCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTablePairRetirement
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredStandardBoundaryCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundaryCounters

/-! Concrete seed initialization in the existing bank. Retained binary masters
55--57, width ruler 58 and empty zero source 59 are outside the metadata table. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix BoundaryCropMetadata
variable {Q A : ℕ} {P U : Type}

def preparedStandardBoundaryCounters (last : Bool) : Pr P 117 Q A U :=
  (.seq (.seq (chirpBankLoad boundaryCounterRegister (seedSources boundarySeedGlobals 59) 58 59)
        (.seq (standardBoundaryCounterProgram last) (tblCompile boundaryCounterRegister restoreCode))) (clearWords (inputTableWords boundaryCounterRegister)))

theorem preparedStandardBoundaryCounters_native (last : Bool) :
    mnNativePushBound 3 (preparedStandardBoundaryCounters (P := P) (Q := Q) (A := A) (U := U) last) := by
  exact ⟨⟨chirpBankLoad_native _ _ _ _,⟨counterProgram_native _ _ _ _,tblCompile_native _ _⟩⟩,
    mnNativePushBound_mono (by decide) (clearWords_native _)⟩

theorem preparedStandardBoundaryCounters_exec (body : P → Pr P 117 Q A U)
    (last : Bool) (D s width W : ℕ)
    (hwidthPos : 0 < width) (hwordPos : 0 < W) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D) (value : Fin 117 → ℕ)
    (hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, value (boundarySeedGlobals j) < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hwidth : (S.R 58).length = D) (hzero : S.R 59 = [])
    (hwords : ∀ j, S.R (boundarySeedGlobals j) = binSyms D (value (boundarySeedGlobals j)))
    (hblank : ∀ r, S.R (boundaryCounterRegister r) = [])
    (hmasters : S.R 26 = [] ∧ S.R 24 = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (64*D+81)+(16*tblC D 0+6*(s*W)+22*D+13)+(20*D+21) ∧
      Exec body (preparedStandardBoundaryCounters last)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R 26
          (List.replicate (coreStart width (index last s width)*W) tick)) 24
          (List.replicate (coreLength s width (index last s width)*W) tick))}) := by
  obtain ⟨u,n,hu,hn,hex⟩ := loadedStandardBoundaryCounters_exec body last D s width W
    hwidthPos hwordPos hroom hvolumeFit value hvalues hfit v S hwidth hzero hwords hblank hmasters depth
  obtain ⟨v',hv,hretire⟩ := retireInputTable_pair_exec_within body boundaryCounterRegister
    boundaryCounterRegister_injective (seedSources boundarySeedGlobals 59) D (seedSourceValue value 59)
    26 24 (fun r => (boundaryCounterRegister_off_masters r).1)
    (fun r => (boundaryCounterRegister_off_masters r).2)
    (List.replicate (coreStart width (index last s width)*W) tick)
    (List.replicate (coreLength s width (index last s width)*W) tick) u S hblank depth
  refine ⟨v',n+(20*D+21),hv.trans hu,by omega,?_⟩
  simpa only [preparedStandardBoundaryCounters,Nat.reduceMul,Nat.reduceAdd] using Exec.seq hex hretire.toExec

theorem preparedStandardBoundaryCounters_within (last : Bool)
    (v v' : HS 117 Q A U) (S F : Stacks 117 A) (n depth : ℕ)
    (he : Exec body (preparedStandardBoundaryCounters last) (mk v S) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*n) depth
      (preparedStandardBoundaryCounters last) (mk v S) n (mk v' F) :=
  mn_native_exec_within he 3 (preparedStandardBoundaryCounters_native last) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
