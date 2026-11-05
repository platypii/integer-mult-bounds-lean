module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerRulers
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGeometryBank

/-! Connect the executed raw-counter baseline to the actual consumer-geometry
bank and construct numerical readiness on the returned state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
noncomputable section
variable {T A D p u l target s t B W N radius width Vg Vr : ℕ}

theorem baselineLoaded_off (src : Fin 11 → Fin T) (widths : Fin 3 → Fin T)
    (S : Stacks (MachineTapes T) A) (k : Fin (MachineTapes T))
    (hscalar : ∀ i, k ≠ globals T i) (hruler : ∀ f, k ≠ rulers T f) :
    (baselineLoaded D src widths S).R k = S.R k := by
  change binaryHeaderBankR D (fun j => ((rulersLoaded widths S).R j).length)
    (rulersLoaded widths S).R (globalCopies T src) k = S.R k
  rw [binaryHeaderBankR_off]
  · apply unaryCopiesR_off
    intro q hq
    obtain ⟨f,rfl⟩ := List.mem_ofFn.mp hq
    exact (hruler f).symm
  · intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact hscalar i

def callerInputProgram {Q : ℕ} {P U : Type} (src : Fin 11 → Fin T) (widthSource : Fin T)
    (widths : Fin 3 → Fin T) : Pr P (MachineTapes T) Q A U :=
  .seq (baselineProgram src widthSource widths) (geometryBankProgram T (List.finRange 3))

def callerInputCost (D p u l target s t B W N radius width Vg Vr : ℕ) : ℕ :=
  ((4*(B+Vg+Vr)+13)+globalConversionCost D p u l target s t B W N radius width)+(30*(B+Vg+Vr)+94)

/-- One actual execution constructs the retained scalar/ruler bank and all
consumer geometry, then supplies numerical readiness from that returned state.
Only raw counters, fit facts and fresh storage are input hypotheses. -/
theorem prepareCallerInputs_exec_within {Q : ℕ} {P U : Type}
    (body : P → Pr P (MachineTapes T) Q A U)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (widths : Fin 3 → Fin T)
    (hwidthOff : ∀ i, src i ≠ widthSource)
    (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hwidth : (S.R (unarySource T widthSource)).length = D)
    (hvalues : ∀ i, (S.R (unarySource T (src i))).length = globalValues p u l target s t B W N radius width i)
    (hwidths : ∀ f, (S.R (unarySource T (widths f))).length = formatWidths B Vg Vr f)
    (hscalarBlank : ∀ i, S.R (globals T i) = [])
    (hrulerBlank : ∀ f, S.R (rulers T f) = [])
    (hgeometryBlank : ∀ f i, S.R (fullHeader T (.geometry f i)) = [])
    (howned : ∀ r ∈ ownedRoles, S.R (fullHeader T r) = [])
    (hzero : S.R (fullHeader T .zero) = [])
    (hrouting : ∀ i, S.R (Fin.natAdd ((T+headerCount)+175) i) = [])
    (clipped : Bool) (hcoreWidth : 0 < width) (hgeometry : width+2*radius < 2^D)
    (hfit : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D)
    (b : ComputedClassBank → Fin T)
    (htable : ∀ r, S.R (numericTable T r) = [])
    (hbank : ∀ j, j ≠ .control .source → S.R (fullExposedClassBank (bank b) j) = [])
    (hleft : ∀ j, S.L (recovery (fullExposedClassBank (bank b)) (.work j)) = []) (depth : ℕ) :
    ∃ v' F, ∃ input : SetupInput T A D p u l target s t B W N radius width Vg Vr F,
      v'.user = v.user ∧
      (makeSetup input clipped hcoreWidth hgeometry hfit hbits).NumericalInput
        (fullExposedClassBank (bank b)) (numericTable T) (geometrySources T) (masterSources T) ∧
      (∀ f i, F.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i)) ∧
      F.L = S.L ∧
      (∀ k, (∀ i, k ≠ globals T i) → (∀ f, k ≠ rulers T f) →
        (∀ f i, k ≠ fullHeader T (.geometry f i)) → F.R k = S.R k) ∧
      ∃ n, n ≤ callerInputCost D p u l target s t B W N radius width Vg Vr ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          3*callerInputCost D p u l target s t B W N radius width Vg Vr) depth
          (callerInputProgram src widthSource widths) (Host.mk v S) n (Host.mk v' F) := by
  let M := baselineLoaded D src widths S
  have input : SetupInput T A D p u l target s t B W N radius width Vg Vr M :=
    baselineSetupInput src widths S hvalues hwidths hrulerBlank howned hzero hrouting
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareBaseline_exec_within body src widthSource widths hwidthOff v S
    hwidth hvalues hwidths hscalarBlank hrouting 0
  obtain ⟨v₂,F,hu₂,hi,hwords,hL,hframe,he₂⟩ := prepareAllGeometry_exec_within body M input hbits
    (by
      intro f i
      rw [baselineLoaded_off src widths S _]
      · exact hgeometryBlank f i
      · intro j
        exact (fullHeader_injective T).ne (by intro h; cases h)
      · intro g
        exact (fullHeader_injective T).ne (by intro h; cases h)) v₁ 0
  have htableM : ∀ r, M.R (numericTable T r) = [] := by
    intro r
    rw [baselineLoaded_off src widths S _]
    · exact htable r
    · intro i
      exact (fullHeader_injective T).ne (by intro h; cases r <;> cases h)
    · intro f
      exact (fullHeader_injective T).ne (by intro h; cases r <;> cases h)
  have hbankM : ∀ j, j ≠ .control .source → M.R (fullExposedClassBank (bank b) j) = [] := by
    intro j hj
    rw [baselineLoaded_off src widths S _]
    · exact hbank j hj
    · intro i
      exact (fullHeader_ne_numerical b (.scalar i) j).symm
    · intro f
      exact (fullHeader_ne_numerical b (.ruler f) j).symm
  have hready := allGeometryNumericalInput hi hwords hL hframe clipped hcoreWidth hgeometry hfit hbits b htableM hbankM hleft
  have hn : n₁+(30*(B+Vg+Vr)+94) ≤ callerInputCost D p u l target s t B W N radius width Vg Vr :=
    Nat.add_le_add_right hn₁ _
  have he := Exec.seq he₁.toExec he₂.toExec
  have hnative : mnNativePushBound 3 (callerInputProgram (Q := Q) (P := P) (A := A) (U := U) src widthSource widths) :=
    ⟨⟨mnNativePushBound_mono (by decide) (copyUnaryHeaders_native _ _),binaryHeaderBank_native _ _ _ _ _⟩,
      geometryBankProgram_native _ _⟩
  refine ⟨v₂,F,hi,hu₂.trans hu₁,hready,hwords,hL,?_,_,hn,?_⟩
  · intro k hs hr hg
    exact (hframe k hg).trans (baselineLoaded_off src widths S k hs hr)
  · exact mn_native_exec_within he 3 hnative depth _ (by omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
