import IntegerMultBounds.Machine.NativeUniformPolynomialRotation
import IntegerMultBounds.Machine.UnitPhaseSigned

/-! Exact native word and guarded signed semantics of the runtime-column
uniform correction. This concerns the actual emitted polynomial stream and
includes private-flag cleanup and a uniform linear physical-cost bound. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotationSemantics
noncomputable section
open ButterflyStreamData (Coefficient)
open NativeUniformPolynomialRotation (phase flagged cleared)
open UnitPhasePolynomialLoop (state coreBlank)
open ButterflySigned (signedValue complexValue)
variable {N : ℕ}

def array (columns : ℕ) (xs : Fin N → Coefficient) :=
  UnitPhasePolynomialArray.result (phase columns) xs

theorem cost_linear (R w : ℕ) (hR : 0<R) :
    R*(24*w+89)+11*(RecursiveChildQuotientsConstant.bits R).length+40≤
      100*(R*(2*(w+1))) := by
  have hb : (RecursiveChildQuotientsConstant.bits R).length≤R+1 := by
    have h := GrowingCounterData.empty_width R
    have hl := Nat.log2_le_self R
    rw [RecursiveChildQuotientsConstant.bits_eq_advance]
    omega
  nlinarith

theorem phase_complex (columns : ℕ) :
    Networks.BinaryPhase.phase ((phase columns).val : ZMod 4)=Complex.I^(27*columns) := by
  unfold Networks.BinaryPhase.phase phase
  rw [ZMod.val_natCast,Nat.mod_mod]
  exact (Complex.I_pow_eq_pow_mod _).symm

theorem width (columns : ℕ) (xs : Fin N → Coefficient) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) (i : Fin N) :
    (array columns xs i).1.length=w ∧ (array columns xs i).2.length=w :=
  UnitPhasePolynomialArray.result_width _ _ w hw i

theorem decoded (columns : ℕ) (xs : Fin N → Coefficient) (b n : ℕ)
    (hw : ∀ i,(xs i).1.length=b+1 ∧ (xs i).2.length=b+1)
    (hg : ∀ i : Fin N, |signedValue b (xs i).1|<(2^b : ℕ) ∧
      |signedValue b (xs i).2|<(2^b : ℕ)) (i : Fin N) :
    complexValue (signedValue b (array columns xs i).1) (signedValue b (array columns xs i).2) n=
      Complex.I^(27*columns)*complexValue (signedValue b (xs i).1) (signedValue b (xs i).2) n := by
  have h := UnitPhaseSigned.words_phase (phase columns)
    (UnitPhasePolynomialArray.components (xs i)) b n (by
      intro j
      unfold UnitPhasePolynomialArray.components
      split_ifs <;> first | exact (hw i).1 | exact (hw i).2) (by
      intro j
      fin_cases j <;> first | exact (hg i).1 | exact (hg i).2)
  rw [phase_complex] at h
  exact h

theorem negative_decoded (xs : Fin N → Coefficient) (b n : ℕ)
    (hw : ∀ i,(xs i).1.length=b+1 ∧ (xs i).2.length=b+1)
    (hg : ∀ i : Fin N, |signedValue b (xs i).1|<(2^b : ℕ) ∧
      |signedValue b (xs i).2|<(2^b : ℕ)) (i : Fin N) :
    complexValue
      (signedValue b ((UnitPhasePolynomialArray.result 2 xs i).1))
      (signedValue b ((UnitPhasePolynomialArray.result 2 xs i).2)) n=
      -complexValue (signedValue b (xs i).1) (signedValue b (xs i).2) n := by
  have h := UnitPhaseSigned.words_phase 2 (UnitPhasePolynomialArray.components (xs i)) b n (by
      intro j
      unfold UnitPhasePolynomialArray.components
      split_ifs <;> first | exact (hw i).1 | exact (hw i).2) (by
      intro j
      fin_cases j <;> first | exact (hg i).1 | exact (hg i).2)
  have hp : Networks.BinaryPhase.phase ((2 : Fin 4).val : ZMod 4)=(-1 : ℂ) := by
    change Complex.I^2=(-1 : ℂ)
    exact Complex.I_sq
  rw [hp,neg_one_mul] at h
  exact h

theorem output_endpoint (v : Tapes 60 2) (columns : ℕ) (f g : ℤ → Fin 6) (p r : ℤ)
    (xs : Fin N → Coefficient) (hcore : coreBlank v)
    (ho : v.tape 58=g ∧ v.head 58=r) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    let out := cleared (state (flagged v (phase columns))
      (UnitPhaseStreamData.contexts f p xs) (phase columns) N)
    out.tape 58=ButterflyStreamData.full g r (array columns xs) ∧
      out.head 58=r+N*(2*(w+1)) := by
  have h := UnitPhasePolynomialArray.output_endpoint (flagged v (phase columns))
    (phase columns) f g p r xs (NativeUniformPolynomialRotation.flagged_flags _ _)
    (NativeUniformPolynomialRotation.flagged_core _ _ hcore)
    (by simpa [flagged,SharedPlacementAlphabet.setTape] using ho) w hw
  simpa [cleared,SharedPlacementAlphabet.setTape,array] using h

theorem fixed_output_endpoint (v : Tapes 60 2) (q : Fin 4) (f g : ℤ → Fin 6) (p r : ℤ)
    (xs : Fin N → Coefficient) (hcore : coreBlank v)
    (ho : v.tape 58=g ∧ v.head 58=r) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    let out := cleared (state (flagged v q) (UnitPhaseStreamData.contexts f p xs) q N)
    out.tape 58=ButterflyStreamData.full g r (UnitPhasePolynomialArray.result q xs) ∧
      out.head 58=r+N*(2*(w+1)) := by
  have h := UnitPhasePolynomialArray.output_endpoint (flagged v q) q f g p r xs
    (NativeUniformPolynomialRotation.flagged_flags _ _)
    (NativeUniformPolynomialRotation.flagged_core _ _ hcore)
    (by simpa [flagged,SharedPlacementAlphabet.setTape] using ho) w hw
  simpa [cleared,SharedPlacementAlphabet.setTape] using h

/-- Original header/flag ports outside the two private phase flags and the
native source/output ports remain literal tapes with their original heads. -/
theorem frame (v : Tapes 60 2) (q : Fin 4) (ctx : ℕ → DelimitedRadixRecord.Context 2)
    (hcore : coreBlank v) (R : ℕ) (i : Fin 60)
    (h48 : i≠48) (h49 : i≠49) (h56 : i≠56) (h58 : i≠58) :
    (cleared (state (flagged v q) ctx q R)).head i=v.head i ∧
      (cleared (state (flagged v q) ctx q R)).tape i=v.tape i := by
  have hstate : (state (flagged v q) ctx q R).head i=(flagged v q).head i ∧
      (state (flagged v q) ctx q R).tape i=(flagged v q).tape i := by
    induction R with
    | zero => exact ⟨rfl,rfl⟩
    | succ R ih =>
      rw [state,UnitPhaseSharedCoefficient.output_eq _ _ _
        (UnitPhasePolynomialLoop.state_flags _ _ _
          (NativeUniformPolynomialRotation.flagged_flags _ _) R)
        (UnitPhasePolynomialLoop.state_core _ _ _
          (NativeUniformPolynomialRotation.flagged_core _ _ hcore) R)]
      simpa [UnitPhaseSharedCoefficient.streamOutput,SharedPlacementAlphabet.setTape,h56,h58] using ih
  simpa [cleared,flagged,SharedPlacementAlphabet.setTape,h48,h49] using hstate

end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotationSemantics
