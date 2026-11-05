module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGatherSeed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedClassProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputComputedClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableClassRun

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement ScalarPlacement.ComputedClassBanks
  CommonClassGeometry PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ} {P U : Type}
noncomputable section

/-- Shared class syntax contains only caller ports and fixed machine bounds. -/
def sharedClassSetupProgram (T : ℕ) : Pr P (MachineTapes T) Q (prime+K) U :=
  .seq (prepareMasters (seedReg T) (globals T) (fullHeader T .zero) (globals T 0)
    false (fullHeader T .core) (fullHeader T .halo))
    (copyBinaryFormats (fullHeader T .halo) (seedReg T (.z 0)) (seedReg T (.z 1)) (formats T))

def sharedClassRetireProgram (T : ℕ) : Pr P (MachineTapes T) Q (prime+K) U :=
  .seq (clearWords ((formats T).map Prod.snd)) (clearWords [fullHeader T .core,fullHeader T .halo])

def sharedGatherProgram (bank : ComputedClassBank → Fin T) (hstates : FixedStreamedBank.stateCount ≤ Q) :
    Pr P (MachineTapes T) Q (prime+K) U :=
  .seq (embProg (exposureIntoRouting (T+headerCount)) Empty.elim
    (restoringAllocatedExposure (P := Empty) (exposure T) (header T .input) ((CallerLayout.bank bank) (.control .source))))
    (restoringAllocatedGather (exposedClassBank (CallerLayout.bank bank))
      (fun i => Fin.castAdd 175 (routing T i)) hstates)

def sharedProperProgram (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q) :
    Pr P (MachineTapes T) Q (prime+K) U :=
  let physicalBank := CallerLayout.bank bank
  let physicalInj := bank_injective bank hinj
  let numerical := inputTableClassProgram (numericTable T) (masterSources T) (globals T 0) (fullHeader T .zero)
    (initializedClassProgram (fullExposedClassBank physicalBank) (geometrySources T)
      (.seq (sharedGatherProgram bank hstates)
        (inputClassProgram (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj) b (numericTable T))))
  .seq (sharedClassSetupProgram T)
    (.seq (publishedClassProgram numerical (routing T) (publication T)
      (physicalBank (.recovery (.control .result))) (header T .output) hstates) (sharedClassRetireProgram T))

variable {D p u l target s t B W N radius width Vg Vr L a : ℕ}
  {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
  {S : Stacks (MachineTapes T) (prime+K)}

theorem makeSetup_program_eq
    (input : SetupInput T (prime+K) D p u l target s t B W N radius width Vg Vr S)
    (hw : 0 < width) (hg : width+2*radius < 2^D)
    (hf : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hb : ∀ f, formatWidths B Vg Vr f ≤ D) :
    (makeSetup input false hw hg hf hb).program (P := P) (Q := Q) (U := U) = sharedClassSetupProgram T := rfl

theorem makeSetup_retire_eq
    (input : SetupInput T (prime+K) D p u l target s t B W N radius width Vg Vr S)
    (hw : 0 < width) (hg : width+2*radius < 2^D)
    (hf : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hb : ∀ f, formatWidths B Vg Vr f ≤ D) :
    (makeSetup input false hw hg hf hb).retire (P := P) (Q := Q) (U := U) = sharedClassRetireProgram T := rfl

theorem callerGatherInput_program_eq
    (input : SetupInput T (prime+K) D p u l target s t B W N radius width Vg Vr S)
    (hwords : ∀ f i, S.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i))
    (bank : ComputedClassBank → Fin T) (retained : GatherRetainedInput T K s W bank Fs borrowed S)
    (bounds : GatherBounds Q Vg Vr s width radius L W a Fs) (hL : L ≤ width+2*radius)
    (hg : width+2*radius < 2^D)
    (hf : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hb : ∀ f, formatWidths B Vg Vr f ≤ D) (hA : 4 ≤ prime+K)
    (gatherInput : (makeSetup input false bounds.widthPositive hg hf hb).GatherInput
      (makeGatherSeed input hwords bank retained bounds hL hA)
      (numericTable T) (masterSources T) (geometrySources T 3))
    (hstates : FixedStreamedBank.stateCount ≤ Q) :
    gatherInput.ready.program (P := P) (U := U) = sharedGatherProgram bank hstates := rfl

theorem callerGatherInput_routeSrc_eq
    (input : SetupInput T (prime+K) D p u l target s t B W N radius width Vg Vr S)
    (hwords : ∀ f i, S.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i))
    (bank : ComputedClassBank → Fin T) (retained : GatherRetainedInput T K s W bank Fs borrowed S)
    (bounds : GatherBounds Q Vg Vr s width radius L W a Fs) (hL : L ≤ width+2*radius)
    (hg : width+2*radius < 2^D)
    (hf : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hb : ∀ f, formatWidths B Vg Vr f ≤ D) (hA : 4 ≤ prime+K)
    (gatherInput : (makeSetup input false bounds.widthPositive hg hf hb).GatherInput
      (makeGatherSeed input hwords bank retained bounds hL hA)
      (numericTable T) (masterSources T) (geometrySources T 3)) :
    gatherInput.ready.routeSrc = routing T := rfl

/-- The proper producer assembled from actual preparation contracts is the
same fixed program for every state, word width, geometry and replica list. -/
theorem sharedProperProgram_eq
    (input : SetupInput T (prime+K) D p u l target s t B W N radius width Vg Vr S)
    (hwords : ∀ f i, S.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i))
    (bank : ComputedClassBank → Fin T) (retained : GatherRetainedInput T K s W bank Fs borrowed S)
    (bounds : GatherBounds Q Vg Vr s width radius L W a Fs) (hL : L ≤ width+2*radius)
    (hg : width+2*radius < 2^D)
    (hf : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hb : ∀ f, formatWidths B Vg Vr f ≤ D) (hA : 4 ≤ prime+K)
    (gatherInput : (makeSetup input false bounds.widthPositive hg hf hb).GatherInput
      (makeGatherSeed input hwords bank retained bounds hL hA)
      (numericTable T) (masterSources T) (geometrySources T 3))
    (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q) :
    let c := makeSetup input false bounds.widthPositive hg hf hb
    let g := gatherInput.ready
    let physicalBank := CallerLayout.bank bank
    let physicalInj := bank_injective bank hinj
    .seq c.program (.seq (publishedClassProgram
      (inputTableClassProgram (numericTable T) (masterSources T) c.widthMaster c.zero
        (initializedClassProgram (fullExposedClassBank physicalBank) (geometrySources T)
          (.seq g.program (inputClassProgram (fullExposedClassBank physicalBank)
            (fullExposedClassBank_injective physicalBank physicalInj) b (numericTable T)))))
      g.routeSrc (publication T) (physicalBank (.recovery (.control .result))) (header T .output) hstates) c.retire) =
      sharedProperProgram (P := P) bank hinj b hstates := by
  dsimp only
  rw [makeSetup_program_eq,makeSetup_retire_eq,
    callerGatherInput_program_eq input hwords bank retained bounds hL hg hf hb hA gatherInput hstates,
    callerGatherInput_routeSrc_eq]
  rfl

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
