import IntegerMultBounds.Machine.FlatAffineScalingArray
import IntegerMultBounds.Machine.SharedPayload

/-! The actual affine scaler over the shared radix alphabet exposes precisely
the permanent canonical source/scratch pair, with no duplicated payload tapes. -/
namespace IntegerMultBounds.Machine.FlatAffineScalingPayload
open Networks
open ActualAffineScaling (modulus)
noncomputable section
variable {P B b radix n : ℕ}

/-- Common physical payload pair: canonical word, blank scratch, zero heads. -/
def pair (a : Fin n → Fin 4) : Tapes 2 radix :=
  ⟨fun _ => 0,![fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
    (putWord (fun _ => blank) 0 (List.ofFn a) z),fun _ => blank]⟩

theorem slots_distinct (r : ℚ) :
    FlatAffineScaling.sourceSlot r ≠ ActualAffineScalingStream.destinationSlot r := by
  rw [← FlatAffineScalingNormalize.sourceSlot_eq,← FlatAffineScalingNormalize.destinationSlot_eq]
  intro h
  have hh := FlatAffineScalingNormalize.slots_injective r h
  exact (by decide : (1 : Fin 8) ≠ 0) hh

private theorem coefficient_source (a : ℕ) :
    ScalingPreparedExecution.executionPlacement a
      (Fin.castAdd 1 (Fin.castAdd (ScalingExecution.AuxTapes a) (Fin.castAdd (a+a) (0 : Fin 4)))) =
      Fin.natAdd (ScalingPreparedExecution.SynthesisTapes a) (Fin.castAdd 2 (Fin.castAdd a (0 : Fin 4))) := by
  apply (ScalingPreparedExecution.synthesisPlacement a).injective
  change (ScalingPreparedExecution.synthesisPlacement a)
    ((ScalingPreparedExecution.synthesisPlacement a).symm _) = _
  rw [Equiv.apply_symm_apply]
  symm
  unfold ScalingPreparedExecution.synthesisPlacement
  simp only [Equiv.coe_fn_mk,Fin.addCases_right]
  change Fin.addCases (motive := fun _ => Fin (ScalingExecution.TapeCount a+1)) (m := 4+a) (n := 2) _ _
    (Fin.castAdd 2 (Fin.castAdd a (0 : Fin 4))) = _
  rw [Fin.addCases_left]
  change Fin.addCases (motive := fun _ => Fin (ScalingExecution.TapeCount a+1)) (m := 4) (n := a) _ _
    (Fin.castAdd a (0 : Fin 4)) = _
  rw [Fin.addCases_left]

private theorem dimensions_front (a d : ℕ) (i : Fin (SignedScalingDimensions.FrontTapes a d)) :
    SignedScalingDimensions.executionPlacement a d (Fin.castAdd 9 (Fin.castAdd 5 (Fin.castAdd 8 i))) =
      Fin.castAdd 5 (Fin.castAdd (11+6) i) := by
  unfold SignedScalingDimensions.executionPlacement
  simp only [FamilyPlacement.withFrame,Equiv.coe_fn_mk,Fin.addCases_left]
  change Fin.castAdd 5 (Fin.addCases (m := SignedScalingDimensions.FrontTapes a d+8) (n := 9) _ _
    (Fin.castAdd 9 (Fin.castAdd 8 i))) = _
  rw [Fin.addCases_left]
  change Fin.castAdd 5 (Fin.addCases (m := SignedScalingDimensions.FrontTapes a d) (n := 8) _ _ (Fin.castAdd 8 i)) = _
  rw [Fin.addCases_left]

private theorem dimensions_sign (a d : ℕ) :
    SignedScalingDimensions.executionPlacement a d
      (Fin.castAdd 9 (Fin.castAdd 5 (Fin.natAdd (SignedScalingDimensions.FrontTapes a d) (1 : Fin 8)))) =
      Fin.castAdd 5 (Fin.natAdd (SignedScalingDimensions.FrontTapes a d) (12 : Fin (11+6))) := by
  unfold SignedScalingDimensions.executionPlacement
  simp only [FamilyPlacement.withFrame,Equiv.coe_fn_mk,Fin.addCases_left]
  change Fin.castAdd 5 (Fin.addCases (m := SignedScalingDimensions.FrontTapes a d+8) (n := 9) _ _
    (Fin.castAdd 9 (Fin.natAdd (SignedScalingDimensions.FrontTapes a d) (1 : Fin 8)))) = _
  rw [Fin.addCases_left]
  change Fin.castAdd 5 (Fin.addCases (m := SignedScalingDimensions.FrontTapes a d) (n := 8) _ _
    (Fin.natAdd (SignedScalingDimensions.FrontTapes a d) (1 : Fin 8))) = _
  rw [Fin.addCases_right]
  rfl

private theorem bank_destination (r : ℚ) (bs qs ns : List Bool) (source : ℤ → Fin 4) :
    (FlatAffineScalingBootstrap.bank r.num.natAbs r.den (ActualAffineScaling.negative r)
      bs qs ns source (fun _ => blank)).tape (ActualAffineScalingStream.destinationSlot r) =
        (fun _ => blank) := by
  unfold FlatAffineScalingBootstrap.bank ActualAffineScalingStream.destinationSlot
    SignedScalingDimensionsStream.destinationSlot SignedScalingDimensionsStream.outerPlacement
    SignedScalingDimensionsStream.innerPlacement SignedScalingSign.destinationSlot
  cases hn : ActualAffineScaling.negative r <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,SignedScalingPrepared.executionPlacement,
      SignedScalingExecution.destinationSlot,ScalingInverseExecution.destinationSlot,
      FamilyPlacement.withFrame,FamilyPlacement.pair,Equiv.coe_fn_mk,
      Fin.addCases_left,Fin.addCases_right]
  · rw [coefficient_source,dimensions_front]
    simp only [SignedScalingDimensionsStream.input,SignedScalingDimensions.input,Tapes.append,Fin.addCases_left]
    change (((_ : Tapes (ScalingPreparedExecution.TapeCount r.num.natAbs) 0).append
      (_ : Tapes (ScalingPreparedExecution.TapeCount r.den) 0)).append (_ : Tapes 5 0)).tape _ = _
    simp only [Tapes.append,Fin.addCases_left,Fin.addCases_right]
    change ((_ : Tapes (ScalingPreparedExecution.SynthesisTapes r.den) 0).append
      (((_ : Tapes 4 0).append (_ : Tapes r.den 0)).append (_ : Tapes 2 0))).tape _ = _
    simp only [Tapes.append,Fin.addCases_left,Fin.addCases_right]
    rfl
  · rw [dimensions_sign]
    simp only [SignedScalingDimensionsStream.input,SignedScalingDimensions.input,Tapes.append,
      Fin.addCases_left,Fin.addCases_right]
    rfl

/-- The actual raw ready input preserves its genuinely blank destination. -/
theorem input_destination {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) :
    (FlatAffineScalingReady.input hr a bs qs ns (fun _ => blank) (fun _ => blank)).tape
      (ActualAffineScalingStream.destinationSlot r) = (fun _ => blank) := by
  unfold FlatAffineScalingReady.input FlatAffineScalingBootstrap.input StaticMarkerInit.raw
  dsimp only
  rw [bank_destination]
  split_ifs <;> simp

def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) :=
  Alphabet.program (RadixToBinary.binaryEncoding (q := radix)) (FlatAffineScalingReady.program hr)

def input {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) :=
  Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
    (FlatAffineScalingReady.input hr a bs qs ns (fun _ => blank) (fun _ => blank))

def output {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) :=
  Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
    (FlatAffineScalingReady.output hr a bs qs ns (fun _ => blank) (fun _ => blank))

theorem input_payload {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) :
    SharedPayload.payload (input (radix := radix) hr a bs qs ns)
      (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r) = pair a := by
  unfold SharedPayload.payload input Alphabet.mapTapes pair
  dsimp only
  congr 1
  · funext i; fin_cases i <;> rfl
  · rw [show (FlatAffineScalingReady.input hr a bs qs ns (fun _ => blank) (fun _ => blank)).tape
      (FlatAffineScaling.sourceSlot r) = _ from FlatAffineScalingBootstrap.source_tape hr a bs qs ns _ _,
      input_destination]
    rfl

theorem output_payload {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) :
    SharedPayload.payload (output (radix := radix) hr a bs qs ns)
      (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r) =
        pair (FlatAffineScalingArray.array hr a) := by
  have hp := FlatAffineScalingReady.output_payload hr a bs qs ns (fun _ => blank) (fun _ => blank)
  unfold SharedPayload.payload output Alphabet.mapTapes pair
  dsimp only at hp ⊢
  rw [hp.2.2.1,hp.2.2.2,hp.2.1,FlatAffineScalingArray.output_source]
  congr 1
  funext i; fin_cases i <;> rfl

/-- Alphabet encoding preserves the exact concrete ready-machine time bound. -/
theorem realizes_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (hB : 0 < B) (hP : 0 < P)
    (bs qs ns : List Bool) (hb : Counter.value bs = B) (hq : Counter.value qs = modulus b)
    (hn : Counter.value ns = P) (cb : GrowingCounterData.Canonical bs)
    (cq : GrowingCounterData.Canonical qs) (cn : GrowingCounterData.Canonical ns) :
    HoareTime (program (radix := radix) hr)
      (fun v => v = input hr a bs qs ns) (fun v => v = output hr a bs qs ns)
      ((2064+120*(r.num.natAbs+r.den))*(P*(modulus b*B))+254) := by
  have hs := FlatAffineScalingReady.realizes_hoare hr a hB hP bs qs ns hb hq hn cb cq cn
    (fun _ => blank) (fun _ => blank) (by intros; rfl)
  have he := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := radix)) hs
  apply he.consequence ?_ ?_ le_rfl
  · rintro v rfl
    exact ⟨_,rfl,rfl⟩
  · rintro v ⟨original,⟨rfl,_⟩,rfl⟩
    rfl

end
end IntegerMultBounds.Machine.FlatAffineScalingPayload
