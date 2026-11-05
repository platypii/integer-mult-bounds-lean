module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerRawInput

/-! A connected raw-input trace prepares the shared numerical and retained gather
inputs before class eligibility is tested. Initialized controls are conclusions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellMatrix
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K D p u l target s t B W radius width Vg Vr a : ℕ} {P U : Type}

def gatherPreparationProgram (src : Fin 11 → Fin T) (widthSource : Fin T) (widths : Fin 3 → Fin T) :
    Pr P (MachineTapes T) Q (prime+K) U :=
  .seq (movementControlProgram src) (callerInputProgram src widthSource widths)

def gatherPreparationCost (D p u l target s t B W N radius width Vg Vr : ℕ) : ℕ :=
  movementControlCost s W N+callerInputCost D p u l target s t B W N radius width Vg Vr

theorem prepareSharedGatherCaller_exec_within
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
    (depth : ℕ) :
    ∃ v' F, ∃ input : SetupInput T (prime+K) D p u l target s t B W Fs.length radius width Vg Vr F,
      v'.user = v.user ∧
      (∀ clipped, (makeSetup input clipped raw.widthPositive raw.geometryFit raw.fit raw.bitsFit).NumericalInput
        (fullExposedClassBank (bank b)) (numericTable T) (geometrySources T) (masterSources T)) ∧
      GatherRetainedInput T K s W b Fs borrowed F ∧
      (∀ f i, F.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i)) ∧
      F.L = S.L ∧
      (∀ k, k ≠ fullHeader T .word → k ≠ fullHeader T .replicas → k ≠ fullHeader T .volume →
        (∀ i, k ≠ globals T i) → (∀ f, k ≠ rulers T f) →
        (∀ f i, k ≠ fullHeader T (.geometry f i)) → F.R k = S.R k) ∧
      ∃ n, n ≤ gatherPreparationCost D p u l target s t B W Fs.length radius width Vg Vr ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          3*gatherPreparationCost D p u l target s t B W Fs.length radius width Vg Vr) depth
          (gatherPreparationProgram src widthSource widths) (Host.mk v S) n (Host.mk v' F) := by
  obtain ⟨v₁,M,n₁,hu₁,retained,hL₁,hframe₁,hn₁,he₁⟩ := prepareGatherControls_exec_within body src b v S
    (raw.values 4) (raw.values 7) (raw.values 8) hword hreplicas hvolume (raw.routingBlank _) (raw.routingBlank _)
    hsource hexposure houtput hroutingLeft hsourceLeft 0
  have rawM := raw.reframeMovement hframe₁
  have hh (r : Role) (hw : r ≠ .word) (hr : r ≠ .replicas) (hv : r ≠ .volume) :
      M.R (fullHeader T r) = S.R (fullHeader T r) :=
    hframe₁ _ ((fullHeader_injective T).ne hw) ((fullHeader_injective T).ne hr) ((fullHeader_injective T).ne hv)
  have htableM : ∀ r, M.R (numericTable T r) = [] := by
    intro r
    rw [show numericTable T r = fullHeader T (tableRole r) from rfl,hh]
    · exact htable r
    all_goals cases r <;> intro h <;> cases h
  have hbankM : ∀ j, j ≠ .control .source → M.R (fullExposedClassBank (bank b) j) = [] := by
    intro j hj
    rw [hframe₁]
    · exact hbank j hj
    · exact (fullHeader_ne_numerical b .word j).symm
    · exact (fullHeader_ne_numerical b .replicas j).symm
    · exact (fullHeader_ne_numerical b .volume j).symm
  obtain ⟨v₂,F,input,hu₂,baseNumerical,hwords,hL₂,hframe₂,n₂,hn₂,he₂⟩ :=
    prepareCallerInputs_exec_within body src widthSource widths rawM.widthOff v₁ M rawM.widthLength rawM.values rawM.widths
      rawM.scalarBlank rawM.rulerBlank rawM.geometryBlank rawM.ownedBlank rawM.zeroBlank rawM.routingBlank
      false rawM.widthPositive rawM.geometryFit rawM.fit rawM.bitsFit b htableM hbankM
      (by rw [hL₁]; exact hleft) 0
  let retainedF := retained.reframe hL₂ hframe₂
  have numerical (clipped : Bool) :
      (makeSetup input clipped raw.widthPositive raw.geometryFit raw.fit raw.bitsFit).NumericalInput
        (fullExposedClassBank (bank b)) (numericTable T) (geometrySources T) (masterSources T) :=
    ⟨baseNumerical.mastersInjective,baseNumerical.geometryWords,baseNumerical.zeroOff,
      baseNumerical.tableOff,baseNumerical.bankOff,baseNumerical.tableBlank,
      baseNumerical.numericalBlank,baseNumerical.leftBlank⟩
  have hn : n₁+n₂ ≤ gatherPreparationCost D p u l target s t B W Fs.length radius width Vg Vr :=
    Nat.add_le_add hn₁ hn₂
  have hnative : mnNativePushBound 3 (gatherPreparationProgram (P := P) (U := U) (Q := Q) (K := K) src widthSource widths) := by
    refine ⟨?_,?_,?_⟩
    · exact mnNativePushBound_mono (by decide)
        (show mnNativePushBound 2 (movementControlProgram src) from ⟨copyUnaryHeaders_native _ _,unaryProduct_native _ _ _ _ _⟩)
    · exact ⟨mnNativePushBound_mono (by decide) (copyUnaryHeaders_native _ _),binaryHeaderBank_native _ _ _ _ _⟩
    · exact geometryBankProgram_native _ _
  refine ⟨v₂,F,input,hu₂.trans hu₁,numerical,retainedF,hwords,hL₂.trans hL₁,?_,_,hn,?_⟩
  · intro k hw hr hv hs hf hg
    exact (hframe₂ k hs hf hg).trans (hframe₁ k hw hr hv)
  · exact mn_native_exec_within (Exec.seq he₁.toExec he₂.toExec) 3 hnative depth _ (by omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
