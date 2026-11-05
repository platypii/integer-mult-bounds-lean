module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPublicationPorts
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGatherPreparation

/-! Produce numerical, retained gather and publication readiness together on the
shared actual endpoint, without requiring a nonempty class before preparation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellMatrix
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K D p u l target s t B W radius width Vg Vr : ℕ} {P U : Type}

theorem prepareSharedPublishedCaller_exec_within
    (body : P → Pr P (MachineTapes T) Q (prime+K) U)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (widths : Fin 3 → Fin T)
    (b : ComputedClassBank → Fin T) (Fs : List (ZMod s → GaussianInt))
    (borrowed : List (Fin (prime+K+4)))
    (v : HS (MachineTapes T) Q (prime+K) U) (S : Stacks (MachineTapes T) (prime+K))
    (raw : RawInput T (prime+K) D p u l target s t B W Fs.length radius width Vg Vr src widthSource widths S)
    (hword : S.R (fullHeader T .word) = []) (hreplicas : S.R (fullHeader T .replicas) = [])
    (hvolume : S.R (fullHeader T .volume) = [])
    (hsource : S.R (fullHeader T .input) = Fs.flatMap (fun C => cstream (prime+K) W (chirpLine s C))++borrowed)
    (hexposure : ∀ i : Fin 175, S.R (Fin.castAdd tapeCount (Fin.natAdd (T+headerCount) i)) = [])
    (houtput : S.R (fullExposedClassBank (bank b) (.control .source)) = [])
    (hroutingLeft : ∀ i : Fin tapeCount, S.L (Fin.natAdd ((T+headerCount)+175) i) = [])
    (hsourceLeft : S.L (control (fullExposedClassBank (bank b)) .source) = [])
    (htable : ∀ r, S.R (numericTable T r) = [])
    (hbank : ∀ j, j ≠ .control .source → S.R (fullExposedClassBank (bank b) j) = [])
    (hleft : ∀ j, S.L (recovery (fullExposedClassBank (bank b)) (.work j)) = [])
    (hpubBlank : ∀ i : Fin 7, S.R (fullHeader T (.publication i)) = [])
    (hresultLeft : S.L (fullExposedClassBank (bank b) (.recovery (.control .result))) = [])
    (hambientLeft : S.L (fullHeader T .output) = []) (depth : ℕ) :
    ∃ v' F, ∃ input : SetupInput T (prime+K) D p u l target s t B W Fs.length radius width Vg Vr F,
      v'.user = v.user ∧
      (∀ clipped, (makeSetup input clipped raw.widthPositive raw.geometryFit raw.fit raw.bitsFit).NumericalInput
        (fullExposedClassBank (bank b)) (numericTable T) (geometrySources T) (masterSources T)) ∧
      GatherRetainedInput T K s W b Fs borrowed F ∧
      PublicationCallerReady (classCallerRegister ∘ publication T)
        (selectedPublicationPlacement (bank b) (header T .output)) F ∧
      (∀ f i, F.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i)) ∧
      F.L = S.L ∧
      (∀ k, k ≠ fullHeader T .word → k ≠ fullHeader T .replicas → k ≠ fullHeader T .volume →
        (∀ i, k ≠ globals T i) → (∀ f, k ≠ rulers T f) →
        (∀ f i, k ≠ fullHeader T (.geometry f i)) → F.R k = S.R k) ∧
      ∃ n, n ≤ gatherPreparationCost D p u l target s t B W Fs.length radius width Vg Vr ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          3*gatherPreparationCost D p u l target s t B W Fs.length radius width Vg Vr) depth
          (gatherPreparationProgram src widthSource widths) (Host.mk v S) n (Host.mk v' F) := by
  obtain ⟨v',F,input,hu,numerical,retained,hwords,hL,hframe,n,hn,he⟩ :=
    prepareSharedGatherCaller_exec_within body src widthSource widths b Fs borrowed v S raw hword hreplicas hvolume
      hsource hexposure houtput hroutingLeft hsourceLeft htable hbank hleft depth
  have publicationReady := publicationReady_of_prepared b S F hpubBlank hresultLeft hambientLeft hroutingLeft hL hframe
  exact ⟨v',F,input,hu,numerical,retained,publicationReady,hwords,hL,hframe,n,hn,he⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
