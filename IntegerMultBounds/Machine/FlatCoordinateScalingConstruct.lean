import IntegerMultBounds.Machine.FlatAffineScalingInstall
import IntegerMultBounds.Machine.FlatCoordinateDimensions

/-! A complete physical coordinate scaling from only b/W and the array payload:
construct dimensions, install all raw descriptor copies, then run and normalize
an actual occurring affine scaler. -/
namespace IntegerMultBounds.Machine.FlatCoordinateScalingConstruct
open Networks
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateLayout
open FlatCoordinateSchedule (bits)
open FlatAffineScalingInstall (LocalTapes)
noncomputable section
variable {d b W : ℕ}

private def source (a : FlatCoordinateStages.Array d b W) (t : Fin d) : ℤ → Fin 4 :=
  putWord (fun _ => blank) 0 (List.ofFn (fiberView a t))

def workspace {r : ℚ} (a : FlatCoordinateStages.Array d b W) (t : Fin d) :=
  FlatAffineScalingInstall.liftedBank prime r.num.natAbs r.den (source a t) [] [] []

def input {r : ℚ} (a : FlatCoordinateStages.Array d b W) (t : Fin d) :=
  (FlatCoordinateDimensions.input b W).append (workspace (r := r) a t)

def output {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : FlatCoordinateStages.Array d b W) (t : Fin d) :=
  (FlatCoordinateDimensions.output t b W).append
    (FlatAffineScalingPayload.output hr (fiberView a t)
      (bits (suffixSize (Q := modulus b) (W := W) t)) (bits (modulus b))
      (bits (prefixSize (Q := modulus b) t)))

def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (t : Fin d) :=
  seq (seq (extend (FlatCoordinateDimensions.program t) (LocalTapes r.num.natAbs r.den))
    (FlatAffineScalingInstall.program prime r.num.natAbs r.den))
    (Placement.placed (FlatAffineScalingPayload.program (radix := prime) hr) finAddFlip)

private theorem left_frame {n s q radix k : ℕ} {M : Program n s radix} {x y : Tapes n radix}
    (h : HoareTime M (fun v => v = x) (fun v => v = y) k) (v : Tapes q radix) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+q) ≃ Fin (q+n)))
      (fun w => w = v.append x) (fun w => w = v.append y) k := by
  have he (z : Tapes n radix) : Placement.combine finAddFlip z v = v.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x v)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun w hw => hw.trans (he x).symm) _ le_rfl
  rintro w ⟨z,hz,rfl⟩
  subst z
  simpa only [Placement.replace,Placement.extra_combine] using he y

private theorem dimensions_ready (t : Fin d) (b W : ℕ) (k : FlatAffineScalingInputLayout.Kind) :
    (FlatCoordinateDimensions.output t b W).head (FlatAffineScalingInstall.sourceSlot k) = 1 ∧
    (FlatCoordinateDimensions.output t b W).tape (FlatAffineScalingInstall.sourceSlot k) =
      RadixZeroFill.encodedBinary
        (FlatAffineScalingInstall.sourceWords
          (bits (suffixSize (Q := modulus b) (W := W) t)) (bits (modulus b))
          (bits (prefixSize (Q := modulus b) t)) (FlatAffineScalingInstall.sourceSlot k)) := by
  obtain ⟨hq,hp,hb⟩ := FlatCoordinateDimensions.output_descriptors t b W
  obtain ⟨hq',hp',hb'⟩ := FlatCoordinateDimensions.output_heads t b W
  cases k <;> first | exact ⟨hq',hq⟩ | exact ⟨hb',hb⟩ | exact ⟨hp',hp⟩

/-- No prepared Q/P/B inputs are assumed. Program and tape count depend only on
fixed target and coefficient; every runtime dimension is computed on tapes. -/
theorem constructs_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : FlatCoordinateStages.Array d b W) (t : Fin d) (hW : 0 < W) :
    HoareTime (program hr t) (fun v => v = input (r := r) a t)
      (fun v => v = output hr a t)
      ((24*t.val+24*suffixFields t+333+22*LocalTapes r.num.natAbs r.den+
        (2064+120*(r.num.natAbs+r.den))+256)*((modulus b)^d*W)) := by
  let bs := bits (suffixSize (Q := modulus b) (W := W) t)
  let qs := bits (modulus b)
  let ns := bits (prefixSize (Q := modulus b) t)
  have hdim := hoare_extend_eq (FlatCoordinateDimensions.construct_hoare t b W hW) (workspace (r := r) a t)
  have hins := FlatAffineScalingInstall.installs_hoare prime r.num.natAbs r.den
    (FlatCoordinateDimensions.output t b W) (source a t) bs qs ns (dimensions_ready t b W)
  have hin : FlatAffineScalingInstall.liftedBank prime r.num.natAbs r.den (source a t) bs qs ns =
      FlatAffineScalingPayload.input hr (fiberView a t) bs qs ns :=
    (FlatAffineScalingInputLayout.payload_input hr (fiberView a t) bs qs ns).symm
  rw [hin] at hins
  have hs := FlatAffineScalingPayload.realizes_hoare (radix := prime) hr (fiberView a t)
    (Nat.mul_pos (pow_pos (ActualAffineScaling.modulus_pos b) _) hW)
    (pow_pos (ActualAffineScaling.modulus_pos b) _)
    bs qs ns (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_canonical _)
    (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
  rw [← split_volume t] at hs
  have hh := (hdim.seq hins).seq (left_frame hs (FlatCoordinateDimensions.output t b W))
  apply hh.consequence (fun _ h => h) (fun _ h => h) ?_
  have hV : 0 < (modulus b)^d*W := Nat.mul_pos (pow_pos (ActualAffineScaling.modulus_pos b) _) hW
  obtain ⟨_,hql,hnl,hbl⟩ := FlatCoordinateDimensions.descriptor_length_bounds t b W hW
  have hc := FlatAffineScalingInstall.cost_volume r.num.natAbs r.den (2*((modulus b)^d*W))
    bs qs ns (by omega) hbl hql hnl
  nlinarith

/-- The sole array payload starts on the actual source/scratch pair. -/
theorem input_payload {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : FlatCoordinateStages.Array d b W) (t : Fin d) :
    SharedPayload.payload (input (r := r) a t)
      (Fin.natAdd 9 (FlatAffineScaling.sourceSlot r))
      (Fin.natAdd 9 (ActualAffineScalingStream.destinationSlot r)) = FlatAffineScalingPayload.pair a := by
  have hw : workspace (r := r) a t = FlatAffineScalingPayload.input (radix := prime) hr (fiberView a t) [] [] [] :=
    (FlatAffineScalingInputLayout.payload_input hr (fiberView a t) [] [] []).symm
  unfold input SharedPayload.payload
  simp only [Tapes.append,Fin.addCases_right,hw]
  change SharedPayload.payload (FlatAffineScalingPayload.input hr (fiberView a t) [] [] []) _ _ = _
  rw [FlatAffineScalingPayload.input_payload]
  unfold FlatAffineScalingPayload.pair
  rw [fiberView_word]

/-- The same physical pair returns the canonical scaled array with blank scratch. -/
theorem output_payload {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : FlatCoordinateStages.Array d b W) (t : Fin d) :
    SharedPayload.payload (output hr a t)
      (Fin.natAdd 9 (FlatAffineScaling.sourceSlot r))
      (Fin.natAdd 9 (ActualAffineScalingStream.destinationSlot r)) =
        FlatAffineScalingPayload.pair (FlatCoordinateScaling.array hr a t) := by
  unfold output SharedPayload.payload
  simp only [Tapes.append,Fin.addCases_right]
  change SharedPayload.payload (FlatAffineScalingPayload.output hr (fiberView a t) _ _ _) _ _ = _
  rw [FlatAffineScalingPayload.output_payload]
  unfold FlatAffineScalingPayload.pair
  rw [FlatCoordinateScaling.array_word]

/-- Every local non-payload input tape is genuinely blank at head zero. -/
theorem input_workspace_blank {r : ℚ} (a : FlatCoordinateStages.Array d b W) (t : Fin d)
    (i : Fin (LocalTapes r.num.natAbs r.den))
    (hi : FlatAffineScalingInputLayout.kinds r.num.natAbs r.den i ≠ .payload) :
    (input (r := r) a t).head (Fin.natAdd 9 i) = 0 ∧
    (input (r := r) a t).tape (Fin.natAdd 9 i) = fun _ => blank := by
  simp only [input,Tapes.append,Fin.addCases_right]
  constructor
  · rfl
  · unfold workspace FlatAffineScalingInstall.liftedBank Alphabet.mapTapes FlatAffineScalingInputLayout.bank
    dsimp only
    funext z
    cases hk : FlatAffineScalingInputLayout.kinds r.num.natAbs r.den i
    all_goals first
      | exact (hi hk).elim
      | (by_cases hz : z = 0 <;>
          simp [FlatAffineScalingInputLayout.word,BinaryDescriptorInstallRaw.rawWord,
            RadixZeroFill.encodedBinary,RadixToBinary.binaryEncoding,CountedCopyReuse.binary,
            CountedCopyReuse.empty,putBits,hz,blank])

end
end IntegerMultBounds.Machine.FlatCoordinateScalingConstruct
