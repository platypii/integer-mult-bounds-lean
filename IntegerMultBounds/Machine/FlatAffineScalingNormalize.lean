import IntegerMultBounds.Machine.FlatAffineScaling
import IntegerMultBounds.Machine.FlatArrayNormalize
import IntegerMultBounds.Machine.InjectivePlacement

/-! Normalize an actual affine-scale bank using its existing payload slots and
its B/Q/P clocks and descriptors. Generated arithmetic metadata remains framed. -/
namespace IntegerMultBounds.Machine.FlatAffineScalingNormalize
open Networks
open SignedScalingPrepared (Setup)
open SignedScalingDimensions (Scratch)
open ActualAffineScaling (modulus negative)
noncomputable section

private def localSource (a d : ℕ) : Fin (SignedScalingSign.TapeCount a d) :=
  Fin.castAdd 5 (Fin.castAdd 8 (Fin.castAdd 5 (Fin.castAdd (ScalingExecution.TapeCount d)
    (Fin.castAdd (ScalingExecution.AuxTapes a) (Fin.castAdd (a+a) (0 : Fin 4))))))

/-- Local source/destination, trailing span B/Q controls, outer P controls. -/
def localSlots (a d : ℕ) (neg : Bool) : Fin 8 → Fin (SignedScalingStream.TapeCount a d) :=
  ![Fin.castAdd 2 (SignedScalingSign.destinationSlot a d neg),Fin.castAdd 2 (localSource a d),
    Fin.castAdd 2 (Fin.natAdd (SignedScalingExecution.TapeCount a d+8) (1 : Fin 5)),
    Fin.castAdd 2 (Fin.natAdd (SignedScalingExecution.TapeCount a d+8) (2 : Fin 5)),
    Fin.castAdd 2 (Fin.natAdd (SignedScalingExecution.TapeCount a d+8) (3 : Fin 5)),
    Fin.castAdd 2 (Fin.natAdd (SignedScalingExecution.TapeCount a d+8) (4 : Fin 5)),
    Fin.natAdd (SignedScalingSign.TapeCount a d) (0 : Fin 2),
    Fin.natAdd (SignedScalingSign.TapeCount a d) (1 : Fin 2)]

theorem localSlots_injective (a d : ℕ) (neg : Bool) : Function.Injective (localSlots a d neg) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  cases neg <;> fin_cases i <;> fin_cases j <;>
    simp [localSlots,localSource,SignedScalingSign.destinationSlot,SignedScalingExecution.destinationSlot,
      ScalingInverseExecution.destinationSlot,ScalingExecution.SplitTapes,ScalingExecution.AuxTapes,
      ScalingExecution.TapeCount,SignedScalingExecution.TapeCount,SignedScalingSign.TapeCount] at hv ⊢ <;> omega

def slots (r : ℚ) (i : Fin 8) : Fin (ActualAffineScalingStream.TapeCount r) :=
  SignedScalingDimensionsStream.outerPlacement r.num.natAbs r.den (Fin.castAdd 9
    (SignedScalingDimensionsStream.innerPlacement r.num.natAbs r.den (Fin.castAdd 2
      (localSlots r.num.natAbs r.den (negative r) i))))

theorem slots_injective (r : ℚ) : Function.Injective (slots r) :=
  (SignedScalingDimensionsStream.outerPlacement _ _).injective.comp ((Fin.castAdd_injective _ _).comp
    ((SignedScalingDimensionsStream.innerPlacement _ _).injective.comp
      ((Fin.castAdd_injective _ _).comp (localSlots_injective _ _ _))))

private theorem size (r : ℚ) : 8+(ActualAffineScalingStream.TapeCount r-8) = ActualAffineScalingStream.TapeCount r := by
  rw [ActualAffineScalingStream.tapeCount_eq]
  omega

def placement (r : ℚ) : Fin (8+(ActualAffineScalingStream.TapeCount r-8)) ≃ Fin (ActualAffineScalingStream.TapeCount r) :=
  InjectivePlacement.placement (slots r) (slots_injective r) (size r)

@[simp] theorem placement_active (r : ℚ) (i : Fin 8) :
    placement r (Fin.castAdd (ActualAffineScalingStream.TapeCount r-8) i) = slots r i :=
  InjectivePlacement.active_slot _ _ _ _

def sourceSlot (r : ℚ) := slots r 1

theorem destinationSlot_eq (r : ℚ) : slots r 0 = ActualAffineScalingStream.destinationSlot r := rfl

private theorem local_source {a d : ℕ} (A : SignedScalingExecution.Controls a) (D : SignedScalingExecution.Controls d)
    (S : SignedScalingSign.SignControls) (neg : Bool) (source dest : ℤ → Fin 4) (p q : ℤ)
    (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ) :
    (SignedScalingStream.bank neg A D S source p middle s signMiddle t dest q).tape (localSource a d) = source ∧
    (SignedScalingStream.bank neg A D S source p middle s signMiddle t dest q).head (localSource a d) = p := by
  simp only [SignedScalingStream.bank,localSource,Tapes.append,Fin.addCases_left]
  change (((_ : Tapes (ScalingExecution.TapeCount a) 0).append (_ : Tapes (ScalingExecution.TapeCount d) 0)).append
    (_ : Tapes 5 0)).tape _ = source ∧
    (((_ : Tapes (ScalingExecution.TapeCount a) 0).append (_ : Tapes (ScalingExecution.TapeCount d) 0)).append
    (_ : Tapes 5 0)).head _ = p
  simp only [Tapes.append,Fin.addCases_left]
  change ((_ : Tapes (ScalingExecution.SplitTapes a) 0).append (_ : Tapes (ScalingExecution.AuxTapes a) 0)).tape _ = source ∧
    ((_ : Tapes (ScalingExecution.SplitTapes a) 0).append (_ : Tapes (ScalingExecution.AuxTapes a) 0)).head _ = p
  simp only [Tapes.append,Fin.addCases_left]
  simp only [ScalingSplit.bank,Tapes.append,Fin.addCases_left]
  exact ⟨rfl,rfl⟩

private theorem normalize_bank (f g : ℤ → Fin 4) (p q : ℤ) (bs qs ps : List Bool) :
    FlatArrayNormalize.bank f g p q bs qs ps =
      (⟨![p,q,1,1,1,1,1,1],![f,g,CountedLoopReuseAlphabet.empty,CountedLoopReuseAlphabet.binary bs,
        CountedLoopReuseAlphabet.empty,CountedLoopReuseAlphabet.binary qs,
        CountedLoopReuseAlphabet.empty,CountedLoopReuseAlphabet.binary ps]⟩ : Tapes 8 0) := by
  unfold FlatArrayNormalize.bank CountedVolumeLoop.bank CountedLoopReuseAlphabet.bank Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem local_active {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (neg : Bool)
    (A : SignedScalingExecution.Controls a) (D : SignedScalingExecution.Controls d) (S : SignedScalingSign.SignControls)
    (Q B n : ℕ) (ns : List Bool) (source dest : ℤ → Fin 4) (p q : ℤ)
    (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (payload : ℕ → ℕ → List (Fin 4)) :
    let v := CountedLoopReuse.bank
      (SignedScalingStream.state ha hd neg A D S Q B n source p middle s signMiddle t dest q payload n)
      CountedCopyReuse.empty (CountedCopyReuse.binary ns) 1 1
    (⟨fun i => v.head (localSlots a d neg i),fun i => v.tape (localSlots a d neg i)⟩ : Tapes 8 0) =
      FlatArrayNormalize.bank
        (putWord dest q (SignedScalingStream.outputPrefix ha Q d neg n payload))
        (putWord source p (SignedScalingStream.fibers Q n payload).flatten)
        (q+((n*(Q*B) : ℕ) : ℤ)) (p+((n*(Q*B) : ℕ) : ℤ)) A.blockBits A.countBits ns := by
  have hd' := SignedScalingStream.state_destination ha hd neg A D S Q B n source p middle s signMiddle t dest q payload n
  have hs' := local_source (SignedScalingStream.controlsAt ha Q n A) (SignedScalingStream.controlsAt hd Q n D) S neg
    (putWord source p (SignedScalingStream.fibers Q n payload).flatten)
    (putWord dest q (SignedScalingStream.outputPrefix ha Q d neg n payload))
    (p+((n*(Q*B) : ℕ) : ℤ)) (q+((n*(Q*B) : ℕ) : ℤ)) middle s signMiddle t
  dsimp only
  rw [normalize_bank]
  congr 1 <;> funext i <;> fin_cases i
  all_goals simp only [localSlots,Matrix.cons_val_zero',Matrix.cons_val_succ',
    CountedLoopReuse.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  · exact hd'.2
  · exact hs'.2
  · simp only [SignedScalingStream.state,SignedScalingStream.bank,Tapes.append,Fin.addCases_right]; rfl
  · simp only [SignedScalingStream.state,SignedScalingStream.bank,Tapes.append,Fin.addCases_right]; rfl
  · simp only [SignedScalingStream.state,SignedScalingStream.bank,Tapes.append,Fin.addCases_right]; rfl
  · simp only [SignedScalingStream.state,SignedScalingStream.bank,Tapes.append,Fin.addCases_right]; rfl
  · rfl
  · rfl
  · exact hd'.1
  · exact hs'.1
  · simp only [SignedScalingStream.state,SignedScalingStream.bank,Tapes.append,Fin.addCases_right]; rfl
  · simp only [SignedScalingStream.state,SignedScalingStream.bank,Tapes.append,Fin.addCases_right]
    exact CountedLoopReuseAlphabet.encoding_binary _
  · simp only [SignedScalingStream.state,SignedScalingStream.bank,Tapes.append,Fin.addCases_right]; rfl
  · simp only [SignedScalingStream.state,SignedScalingStream.bank,Tapes.append,Fin.addCases_right]
    exact CountedLoopReuseAlphabet.encoding_binary _
  · rfl
  · exact CountedLoopReuseAlphabet.encoding_binary _

variable {P B b : ℕ}

def word {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) :=
  ActualAffineScalingStream.outputPrefix hr b P (FlatAffineScaling.payload a)

@[simp] theorem word_length {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) : (word hr a).length = P*(modulus b*B) := by
  exact SignedScalingStream.prefix_length (ActualAffineScaling.modulus_pos b) (ActualAffineScaling.numerator_pos hr)
    (Shared50AffineCoefficients.unit_recipe hr b).2.2.1 r.den (negative r) P
    (fun i y => FlatAffineScaling.payload a i (y : ZMod (modulus b)))
    (fun i y => FlatAffineScaling.payload_length a i _)

/-- Existing physical clock and descriptor cells supply the normalizer exactly. -/
theorem output_active {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) :
    Placement.active (placement r) (FlatAffineScaling.output hr a ns A D S source p middle s signMiddle t dest q) =
      FlatArrayNormalize.bank (putWord dest q (word hr a)) (putWord source p (List.ofFn a))
        (q+((P*(modulus b*B) : ℕ) : ℤ)) (p+((P*(modulus b*B) : ℕ) : ℤ)) A.blockBits A.countBits ns := by
  unfold placement
  rw [InjectivePlacement.active_bank]
  simp only [FlatAffineScaling.output,ActualAffineScalingStream.output,SignedScalingDimensionsStream.state,slots,
    Placement.combine_head_active,Placement.combine_tape_active]
  have hh := local_active (ActualAffineScaling.numerator_pos hr) r.den_pos (negative r)
    (SignedScalingPrepared.prepared (ActualAffineScaling.numerator_pos hr) A (modulus b) B)
    (SignedScalingPrepared.prepared r.den_pos D (modulus b) B) (SignedScalingDimensions.generated S (modulus b) B)
    (modulus b) B P ns source dest p q middle s signMiddle t
    (fun i y => FlatAffineScaling.payload a i (y : ZMod (modulus b)))
  rw [FlatAffineScaling.source_eq] at hh
  exact hh

/-- Complete retained bank after normalization, including all generated scaling
metadata and residues. Only the two payload tapes change from the scale output. -/
def output {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) :=
  Placement.replace (placement r) (FlatAffineScaling.output hr a ns A D S source p middle s signMiddle t dest q)
    (FlatArrayNormalize.bank dest (putWord (putWord source p (List.ofFn a)) p (word hr a))
      q p A.blockBits A.countBits ns)

def normalizeProgram (r : ℚ) := Placement.placed (FlatArrayNormalize.program (a := 0)) (placement r)

/-- Actual copy, erase and rewind attached to the scale's physical endpoint. -/
theorem normalize_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (hB : 0 < B) (hP : 0 < P)
    (ns : List Bool) (hn : Counter.value ns = P) (cn : GrowingCounterData.Canonical ns)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch) (hA : A.Valid (modulus b) B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ)
    (hblank : ∀ z, q ≤ z → z < q+((P*(modulus b*B) : ℕ) : ℤ) → dest z = blank) :
    HoareTime (normalizeProgram r)
      (fun v => v = FlatAffineScaling.output hr a ns A D S source p middle s signMiddle t dest q)
      (fun v => v = output hr a ns A D S source p middle s signMiddle t dest q)
      (327*(P*(modulus b*B))+2) := by
  have hh := FlatArrayNormalize.normalize_hoare dest (putWord source p (List.ofFn a)) q p (word hr a)
    P (modulus b) B A.blockBits A.countBits ns (word_length hr a) hA.block_value hA.count_value hn
    hP (ActualAffineScaling.modulus_pos b) hB hA.block_canonical hA.count_canonical cn
    (by intro z hz hz'; rw [word_length hr a] at hz'; exact hblank z hz hz')
  rw [word_length hr a] at hh
  have hp := Placement.hoare_at hh (placement r)
    (FlatAffineScaling.output hr a ns A D S source p middle s signMiddle t dest q)
    (output_active hr a ns A D S source p middle s signMiddle t dest q)
  apply hp.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rfl

def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) :=
  seq (ActualAffineScalingStream.program hr) (normalizeProgram r)

/-- Full concrete scale and charged payload normalization, with all metadata
retained and the result returned to the original common input tape. -/
theorem realizes_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (hB : 0 < B) (hP : 0 < P)
    (ns : List Bool) (hn : Counter.value ns = P) (cn : GrowingCounterData.Canonical ns)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (hA : A.Valid (modulus b) B) (hD : D.Valid (modulus b) B)
    (hS : negative r = true → ∀ z, S.origin ≤ z → z < S.origin+(((modulus b-1)*B : ℕ) : ℤ) → S.tape z = blank)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ)
    (hblank : ∀ z, s ≤ z → z < s+((modulus b*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative r = true → ∀ z, t ≤ z → z < t+((modulus b*B : ℕ) : ℤ) → signMiddle z = blank)
    (hdblank : ∀ z, q ≤ z → z < q+((P*(modulus b*B) : ℕ) : ℤ) → dest z = blank) :
    HoareTime (program hr)
      (fun v => v = FlatAffineScaling.input hr a ns A D S source p middle s signMiddle t dest q)
      (fun v => v = output hr a ns A D S source p middle s signMiddle t dest q)
      ((2064+120*(r.num.natAbs+r.den))*(P*(modulus b*B))+252) := by
  have hs := (FlatAffineScaling.realizes_hoare hr a hB hP ns hn cn A D S hA hD hS
    source p middle s signMiddle t dest q hblank hsblank).consequence (fun _ h => h) (fun _ h => h.1) le_rfl
  have hn' := normalize_hoare hr a hB hP ns hn cn A D S hA source p middle s signMiddle t dest q hdblank
  apply (hs.seq hn').consequence (fun _ h => h) (fun _ h => h) _
  unfold ActualAffineScalingStream.nonemptyConstant
  ring_nf
  rfl

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

/-- The statically selected source is the original physical source slot. -/
theorem sourceSlot_eq (r : ℚ) : sourceSlot r = FlatAffineScaling.sourceSlot r := by
  change SignedScalingDimensionsStream.outerPlacement r.num.natAbs r.den (Fin.castAdd 9
    (SignedScalingDimensionsStream.innerPlacement r.num.natAbs r.den (Fin.castAdd 2
      (Fin.castAdd 2 (localSource r.num.natAbs r.den))))) = _
  unfold SignedScalingDimensionsStream.innerPlacement
  simp only [FamilyPlacement.withFrame,Equiv.coe_fn_mk,Fin.addCases_left]
  unfold SignedScalingPrepared.executionPlacement localSource
  simp only [FamilyPlacement.withFrame,Equiv.coe_fn_mk,FamilyPlacement.pair,Fin.addCases_left,coefficient_source]
  unfold SignedScalingDimensionsStream.outerPlacement
  simp only [FamilyPlacement.withFrame,Equiv.coe_fn_mk,Fin.addCases_left,dimensions_front]
  rfl

/-- Every complementary physical tape and head is exactly the scaling output. -/
theorem output_frame {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) :
    Placement.extra (placement r) (output hr a ns A D S source p middle s signMiddle t dest q) =
      Placement.extra (placement r) (FlatAffineScaling.output hr a ns A D S source p middle s signMiddle t dest q) := by
  simp only [output,Placement.replace,Placement.extra_combine]

/-- Precise common payload interface on the original source and destination. -/
theorem output_payload {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) :
    let v := output hr a ns A D S source p middle s signMiddle t dest q
    v.tape (FlatAffineScaling.sourceSlot r) = putWord (putWord source p (List.ofFn a)) p (word hr a) ∧
    v.tape (ActualAffineScalingStream.destinationSlot r) = dest ∧
    v.head (FlatAffineScaling.sourceSlot r) = p ∧ v.head (ActualAffineScalingStream.destinationSlot r) = q := by
  dsimp only
  rw [← sourceSlot_eq,← destinationSlot_eq]
  unfold sourceSlot
  rw [← placement_active r 0,← placement_active r 1]
  simp only [output,Placement.replace,Placement.combine_tape_active,Placement.combine_head_active,normalize_bank]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Every scaled symbol is now on the original source tape, ready for the next
fixed affine operation, with prefix and entire suffix positions retained. -/
theorem output_symbol {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (i : Fin P) (y : Fin (modulus b)) (j : Fin B) :
    (output hr a ns A D S source p middle s signMiddle t dest q).tape (FlatAffineScaling.sourceSlot r)
      (p+((i.val*(modulus b*B)+(Swap.Modular.ratMod (modulus b) r*(y.val : ZMod (modulus b))).val*B+j.val : ℕ) : ℤ)) =
      a (FiberLayoutData.index i y j) := by
  let : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
  have hy := ZMod.val_lt (Swap.Modular.ratMod (modulus b) r*(y.val : ZMod (modulus b)))
  have hj : (Swap.Modular.ratMod (modulus b) r*(y.val : ZMod (modulus b))).val*B+j.val < modulus b*B := by
    nlinarith [j.isLt]
  have hidx : i.val*(modulus b*B)+(Swap.Modular.ratMod (modulus b) r*(y.val : ZMod (modulus b))).val*B+j.val <
      (word hr a).length := by
    rw [word_length]
    have hh := Nat.mul_le_mul_right (modulus b*B) (show i.val+1 ≤ P by omega)
    nlinarith
  have hh := FlatAffineScaling.output_symbol hr a ns A D S source p middle s signMiddle t dest q i y j
  unfold FlatAffineScaling.output at hh
  rw [(ActualAffineScalingStream.output_tape hr b B P ns A D S source p middle s signMiddle t dest q
    (FlatAffineScaling.payload a)).1] at hh
  change putWord dest q (word hr a) _ = _ at hh
  rw [WordSegments.get _ _ _ _ hidx] at hh
  rw [(output_payload hr a ns A D S source p middle s signMiddle t dest q).1,
    WordSegments.get _ _ _ _ hidx]
  exact hh

end
end IntegerMultBounds.Machine.FlatAffineScalingNormalize
