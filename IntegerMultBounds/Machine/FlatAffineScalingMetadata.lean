import IntegerMultBounds.Machine.FlatAffineScalingPayload

/-! Scaling-stage private input storage depends only on its fixed coefficient
and dimensional words. The common payload array never needs to be computed in
advance to prepare a later scaling stage. -/
namespace IntegerMultBounds.Machine.FlatAffineScalingMetadata
open Networks
open SharedPlacementAlphabet (setTape)
open ActualAffineScaling (modulus)
variable {P B b radix : ℕ}

private theorem setTape_append_right {l r a : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p = v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals rename_i k; intro h; have hk := k.isLt; omega

/-- The original source occurs in exactly its one physical source slot. -/
private theorem bank_set_source (r : ℚ) (bs qs ns : List Bool) (source replacement dest : ℤ → Fin 4) :
    setTape (FlatAffineScalingBootstrap.bank r.num.natAbs r.den (ActualAffineScaling.negative r)
      bs qs ns source dest) (FlatAffineScaling.sourceSlot r) replacement 0 =
    FlatAffineScalingBootstrap.bank r.num.natAbs r.den (ActualAffineScaling.negative r)
      bs qs ns replacement dest := by
  unfold FlatAffineScalingBootstrap.bank SignedScalingDimensionsStream.input SignedScalingDimensions.input
    FlatAffineScaling.sourceSlot
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun v : Tapes (SignedScalingDimensions.FrontTapes r.num.natAbs r.den) 0 => ((v.append _).append _).append _)
  change setTape (((_ : Tapes (ScalingPreparedExecution.TapeCount r.num.natAbs) 0).append
    (_ : Tapes (ScalingPreparedExecution.TapeCount r.den) 0)).append (_ : Tapes 5 0)) _ replacement 0 = _
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun v : Tapes (ScalingPreparedExecution.TapeCount r.num.natAbs) 0 => (v.append _).append _)
  change setTape ((_ : Tapes (ScalingPreparedExecution.SynthesisTapes r.num.natAbs) 0).append
    (((_ : Tapes 4 0).append (_ : Tapes r.num.natAbs 0)).append (_ : Tapes 2 0))) _ replacement 0 = _
  rw [setTape_append_right,SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun v : Tapes 4 0 => Tapes.append _ ((v.append _).append _))
  unfold setTape CountedCopyReuse.bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [SignedScalingStream.fibers,ScalingStream.fibers,ScalingExecution.inputWord,putWord]

private theorem raw_clear {t : ℕ} (template v : Tapes t 0) (i : Fin t) :
    StaticMarkerInit.raw template (setTape v i (fun _ => blank) 0) =
      setTape (StaticMarkerInit.raw template v) i (fun _ => blank) 0 := by
  unfold StaticMarkerInit.raw setTape
  apply congrArg₂ Tapes.mk
  · funext j; simp [Function.update_apply]
  · funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]

private theorem map_clear {t a q : ℕ} (e : Alphabet.Encoding a q) (he : e.encode blank = blank)
    (v : Tapes t a) (i : Fin t) :
    Alphabet.mapTapes e (setTape v i (fun _ => blank) 0) =
      setTape (Alphabet.mapTapes e v) i (fun _ => blank) 0 := by
  unfold Alphabet.mapTapes setTape
  apply congrArg₂ Tapes.mk
  · rfl
  · funext j z
    by_cases hj : j = i <;> simp [hj,he]

/-- After the permanent payload pair is removed, the complete lifted scaling
input is identical for any original array of the same dimensions. -/
theorem strip_input_eq {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a a' : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) :
    SharedPayload.strip (FlatAffineScalingPayload.input (radix := radix) hr a bs qs ns)
      (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r) =
    SharedPayload.strip (FlatAffineScalingPayload.input (radix := radix) hr a' bs qs ns)
      (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r) := by
  unfold SharedPayload.strip FlatAffineScalingPayload.input FlatAffineScalingReady.input FlatAffineScalingBootstrap.input
  apply congrArg (fun v => setTape v (ActualAffineScalingStream.destinationSlot r) (fun _ => blank) 0)
  rw [← map_clear _ (by rfl),← raw_clear,bank_set_source,
      ← map_clear _ (by rfl),← raw_clear,bank_set_source]

end IntegerMultBounds.Machine.FlatAffineScalingMetadata
