import IntegerMultBounds.Machine.FlatCoordinateDimensions
import IntegerMultBounds.Machine.ControlledShiftDimensionInstall
import IntegerMultBounds.Machine.PrefixWidthCopiesAt

/-! An actual controlled shift from one exponent, one record-width descriptor,
one payload array, and wholly blank generated storage. Dimensional arithmetic,
all width/B/Q/P descriptor copies, prefix initialization and the shift itself
execute as fixed finite-state programs with a charged linear-volume bound. -/
namespace IntegerMultBounds.Machine.FlatCoordinateShiftFromDimensions
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateLayout
open FlatCoordinateSchedule (bits)
open FlatControlledShiftLayout (suffix)
noncomputable section
variable {d : ℕ}
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩

abbrev fields (t : Fin d) := (t.val-1)+1
abbrev prefixTapes (t : Fin d) := PrefixCounterInit.tapeCount (fields t)
abbrev TapeCount (t : Fin d) := (9+prefixTapes t)+17

private def suffixPlacement (n : ℕ) : Fin ((9+17)+n) ≃ Fin ((9+n)+17) where
  toFun := Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd 17 (Fin.castAdd n i)) (Fin.natAdd (9+n)))
    (fun i => Fin.castAdd 17 (Fin.natAdd 9 i))
  invFun := Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd n (Fin.castAdd 17 i)) (Fin.natAdd (9+17)))
    (fun i => Fin.castAdd n (Fin.natAdd 9 i))
  left_inv := by
    intro i; induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i; induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp

private theorem suffix_active {n : ℕ} (dim : Tapes 9 prime) (pre : Tapes n prime) (suf : Tapes 17 prime) :
    Placement.active (suffixPlacement n) ((dim.append pre).append suf) = dim.append suf := by
  unfold Placement.active suffixPlacement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

private theorem suffix_extra {n : ℕ} (dim : Tapes 9 prime) (pre : Tapes n prime) (suf : Tapes 17 prime) :
    Placement.extra (suffixPlacement n) ((dim.append pre).append suf) = pre := by
  unfold Placement.extra suffixPlacement Tapes.append
  congr 1 <;> funext i <;> simp

private theorem suffix_combine {n : ℕ} (dim : Tapes 9 prime) (pre : Tapes n prime) (suf : Tapes 17 prime) :
    Placement.combine (suffixPlacement n) (dim.append suf) pre = (dim.append pre).append suf := by
  simpa only [suffix_active,suffix_extra] using Placement.view (suffixPlacement n) ((dim.append pre).append suf)

/-- Original stage tapes are retained; only a fixed nine-tape dimension bank is
framed outside its transition table. No data or head moves occur at this wiring. -/
def stagePlacement (n : ℕ) : Fin ((n+17)+9) ≃ Fin ((9+n)+17) where
  toFun := Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd 17 (Fin.natAdd 9 i)) (Fin.natAdd (9+n)))
    (fun i => Fin.castAdd 17 (Fin.castAdd n i))
  invFun := Fin.addCases
    (Fin.addCases (Fin.natAdd (n+17)) (fun i => Fin.castAdd 9 (Fin.castAdd 17 i)))
    (fun i => Fin.castAdd 9 (Fin.natAdd n i))
  left_inv := by
    intro i; induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i; induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp

theorem stage_active {n : ℕ} (dim : Tapes 9 prime) (pre : Tapes n prime) (suf : Tapes 17 prime) :
    Placement.active (stagePlacement n) ((dim.append pre).append suf) = pre.append suf := by
  unfold Placement.active stagePlacement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem stage_extra {n : ℕ} (dim : Tapes 9 prime) (pre : Tapes n prime) (suf : Tapes 17 prime) :
    Placement.extra (stagePlacement n) ((dim.append pre).append suf) = dim := by
  unfold Placement.extra stagePlacement Tapes.append
  congr 1 <;> funext i <;> simp

theorem stage_combine {n : ℕ} (dim : Tapes 9 prime) (pre : Tapes n prime) (suf : Tapes 17 prime) :
    Placement.combine (stagePlacement n) (pre.append suf) dim = (dim.append pre).append suf := by
  simpa only [stage_active,stage_extra] using Placement.view (stagePlacement n) ((dim.append pre).append suf)

def primitive (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) := FlatCoordinateSchedule.instantiate (.shift t k hk r hr) b W hW

private theorem primitive_input (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :
    (primitive r hr t k hk b W hW).input a =
      (PrefixCounterInit.input (q := prime) (fields t) (fun _ => bits b)).append
        (suffix prime (putWord (fun _ => blank) 0 (List.ofFn a)) (fun _ => blank) 0 0
          (some (bits (suffixSize (Q := modulus b) (W := W) t)))
          (some (bits (modulus b))) (some (bits (prefixSize (Q := modulus b) t)))) := by
  dsimp only [FlatCoordinateStages.Array,modulus] at a ⊢
  change RationalPrefixTranslationBootstrap.input _ _ _ _ _ _ _ _ _ _ _ _ = _
  rw [FlatControlledShiftLayout.input_layout,FlatCoordinateShift.view_word]
  rfl

/-- Exactly two dimensional input words, one payload array, and blank storage. -/
def input (t : Fin d) (b W : ℕ) (a : FlatCoordinateStages.Array d b W) : Tapes (TapeCount t) prime :=
  ((FlatCoordinateDimensions.input b W).append (PrefixWidthCopies.blankBank prime (prefixTapes t))).append
    (suffix prime (putWord (fun _ => blank) 0 (List.ofFn a)) (fun _ => blank) 0 0 none none none)

def prepared (t : Fin d) (b W : ℕ) (a : FlatCoordinateStages.Array d b W) : Tapes (TapeCount t) prime :=
  ((FlatCoordinateDimensions.output t b W).append
    (PrefixCounterInit.input (q := prime) (fields t) (fun _ => bits b))).append
    (suffix prime (putWord (fun _ => blank) 0 (List.ofFn a)) (fun _ => blank) 0 0
      (some (bits (suffixSize (Q := modulus b) (W := W) t)))
      (some (bits (modulus b))) (some (bits (prefixSize (Q := modulus b) t))))

def setup (t : Fin d) :=
  seq (seq (extend (extend (FlatCoordinateDimensions.program t) (prefixTapes t)) 17)
    (extend (PrefixWidthCopiesAt.program prime (2 : Fin 9) (fields t)) 17))
    (Placement.placed (ControlledShiftDimensionInstall.program prime) (suffixPlacement (prefixTapes t)))

/-- Every arithmetic and descriptor-copy transition has an explicit budget. -/
theorem setup_hoare (t : Fin d) (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :
    HoareTime (setup t) (fun v => v = input t b W a) (fun v => v = prepared t b W a)
      ((24*t.val+24*suffixFields t+333)*((modulus b)^d*W)+fields t*(2*(bits b).length+6)+
        2*((bits (suffixSize (Q := modulus b) (W := W) t)).length+(bits (modulus b)).length+
          (bits (prefixSize (Q := modulus b) t)).length)+19) := by
  let suf := suffix prime (putWord (fun _ => blank) 0 (List.ofFn a)) (fun _ => blank) 0 0 none none none
  have hd := FamilyPlacementAlphabet.extend_hoare
    (FamilyPlacementAlphabet.extend_hoare (FlatCoordinateDimensions.construct_hoare t b W hW)
      (PrefixWidthCopies.blankBank prime (prefixTapes t))) suf
  have hp := FamilyPlacementAlphabet.extend_hoare
    (PrefixWidthCopiesAt.copies_hoare (2 : Fin 9) (fields t) (FlatCoordinateDimensions.output t b W) (bits b)
      (FlatCoordinateDimensions.inputs_preserved t b W).1 (FlatCoordinateDimensions.inputs_preserved t b W).2.1) suf
  have ht := FlatCoordinateDimensions.output_descriptors t b W
  have hh := FlatCoordinateDimensions.output_heads t b W
  have hb := ControlledShiftDimensionInstall.install_hoare (FlatCoordinateDimensions.output t b W)
    (bits (suffixSize (Q := modulus b) (W := W) t)) (bits (modulus b)) (bits (prefixSize (Q := modulus b) t))
    ht.2.2 hh.2.2 ht.1 hh.1 ht.2.1 hh.2.1
    (putWord (fun _ => blank) 0 (List.ofFn a)) (fun _ => blank) 0 0
  have hb' := Placement.hoare_at hb (suffixPlacement (prefixTapes t))
    (((FlatCoordinateDimensions.output t b W).append
      (PrefixCounterInit.input (q := prime) (fields t) (fun _ => bits b))).append suf)
    (suffix_active _ _ _)
  have hb'' : HoareTime (Placement.placed (ControlledShiftDimensionInstall.program prime) (suffixPlacement (prefixTapes t)))
      (fun v => v = ((FlatCoordinateDimensions.output t b W).append
        (PrefixCounterInit.input (q := prime) (fields t) (fun _ => bits b))).append suf)
      (fun v => v = prepared t b W a)
      (2*((bits (suffixSize (Q := modulus b) (W := W) t)).length+(bits (modulus b)).length+
        (bits (prefixSize (Q := modulus b) t)).length)+17) := by
    apply hb'.consequence (fun _ h => h) ?_ le_rfl
    rintro v ⟨small,hsmall,rfl⟩
    subst small
    rw [Placement.replace,suffix_extra,suffix_combine]
    rfl
  exact ((hd.seq hp).seq hb'').consequence (fun _ h => h) (fun _ h => h) (by omega)

def program (r : ℚ) (t k : Fin d) :=
  seq (setup t) (Placement.placed
    (FlatControlledShiftReady.program (radix := prime) r
      (FlatCoordinateShift.low t k++0::FlatCoordinateShift.high t k) (by simp))
    (stagePlacement (prefixTapes t)))

def output (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) : Tapes (TapeCount t) prime :=
  Placement.combine (stagePlacement (prefixTapes t)) ((primitive r hr t k hk b W hW).output a)
    (FlatCoordinateDimensions.output t b W)

/-- The full blank-workspace-to-normalized-array execution. The dimensions and
all generated metadata are retained literally in the exact final bank. -/
theorem realizes_hoare_exact (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :
    HoareTime (program r t k) (fun v => v = input t b W a)
      (fun v => v = output r hr t k hk b W hW a)
      ((24*t.val+24*suffixFields t+333)*((modulus b)^d*W)+fields t*(2*(bits b).length+6)+
        2*((bits (suffixSize (Q := modulus b) (W := W) t)).length+(bits (modulus b)).length+
          (bits (prefixSize (Q := modulus b) t)).length)+20+
        (878+4*(t.val-1))*((modulus b)^d*W)+29*t.val+29) := by
  have hs := (primitive r hr t k hk b W hW).realizes a
  have ha : Placement.active (stagePlacement (prefixTapes t)) (prepared t b W a) =
      (primitive r hr t k hk b W hW).input a := by
    rw [prepared,stage_active,primitive_input]
  have hh := Placement.hoare_at hs (stagePlacement (prefixTapes t)) (prepared t b W a) ha
  have hh' : HoareTime (Placement.placed (primitive r hr t k hk b W hW).program (stagePlacement (prefixTapes t))) (fun v => v = prepared t b W a)
      (fun v => v = output r hr t k hk b W hW a)
      ((878+4*(t.val-1))*((modulus b)^d*W)+29*t.val+29) := by
    apply hh.consequence (fun _ h => h) ?_ le_rfl
    rintro v ⟨small,hsmall,rfl⟩
    subst small
    exact congrArg (Placement.combine (stagePlacement (prefixTapes t))
      (show Tapes (prefixTapes t+17) prime from (primitive r hr t k hk b W hW).output a))
      (show Placement.extra (stagePlacement (prefixTapes t)) (prepared t b W a) =
        FlatCoordinateDimensions.output t b W from stage_extra _ _ _)
  exact ((setup_hoare t b W hW a).seq hh').consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Physical payload slots of the complete initialized machine. -/
def sourceSlot (t : Fin d) : Fin (TapeCount t) :=
  stagePlacement (prefixTapes t) (Fin.castAdd 9 (FlatControlledShiftPayload.sourceSlot (t.val-1)))
def destSlot (t : Fin d) : Fin (TapeCount t) :=
  stagePlacement (prefixTapes t) (Fin.castAdd 9 (FlatControlledShiftPayload.destSlot (t.val-1)))

theorem output_payload (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :
    SharedPayload.payload (output r hr t k hk b W hW a) (sourceSlot t) (destSlot t) =
      FlatAffineScalingPayload.pair (FlatCoordinateShift.array (radix := prime) r a t k hk) := by
  change SharedPayload.payload
    (Placement.active (stagePlacement (prefixTapes t)) (output r hr t k hk b W hW a))
    (FlatControlledShiftPayload.sourceSlot (t.val-1)) (FlatControlledShiftPayload.destSlot (t.val-1)) = _
  have hp := Placement.active_combine (stagePlacement (prefixTapes t))
    (show Tapes (prefixTapes t+17) prime from (primitive r hr t k hk b W hW).output a)
    (FlatCoordinateDimensions.output t b W)
  exact (congrArg (fun v : Tapes (prefixTapes t+17) prime => SharedPayload.payload v
    (FlatControlledShiftPayload.sourceSlot (t.val-1)) (FlatControlledShiftPayload.destSlot (t.val-1))) hp).trans
    ((primitive r hr t k hk b W hW).output_payload a)

/-- All computed dimensions and the original b/W inputs remain explicit frame. -/
theorem output_dimensions (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :
    Placement.extra (stagePlacement (prefixTapes t)) (output r hr t k hk b W hW a) =
      FlatCoordinateDimensions.output t b W := Placement.extra_combine _ _ _

/-- This constant depends only on the fixed coordinate layout. -/
def constant (t : Fin d) : ℕ :=
  (24*t.val+24*suffixFields t+333)+10*fields t+(878+4*(t.val-1))+29*t.val+61

/-- No supplied stage descriptors: one exponent, one trailing width, and the
array suffice. A single dimension-independent program returns the entire
canonical transformed array in linear volume time. -/
theorem realizes_hoare (r : ℚ) (hr : Shared50AffineCoefficients.Occurs r) (t k : Fin d) (hk : k < t)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array d b W) :
    HoareTime (program r t k) (fun v => v = input t b W a)
      (fun v => v = output r hr t k hk b W hW a ∧
        SharedPayload.payload v (sourceSlot t) (destSlot t) =
          FlatAffineScalingPayload.pair (FlatCoordinateShift.array (radix := prime) r a t k hk))
      (constant t*((modulus b)^d*W)) := by
  apply (realizes_hoare_exact r hr t k hk b W hW a).consequence (fun _ h => h) ?_ ?_
  · rintro v rfl
    exact ⟨rfl,output_payload r hr t k hk b W hW a⟩
  · have hl := FlatCoordinateDimensions.descriptor_length_bounds t b W hW
    have hv : 0 < (modulus b)^d*W := Nat.mul_pos (pow_pos (ActualAffineScaling.modulus_pos b) _) hW
    have hwidth : 2*(bits b).length+6 ≤ 10*((modulus b)^d*W) := by omega
    have hcopies := Nat.mul_le_mul_left (fields t) hwidth
    have hfixed : 29*t.val+49 ≤ (29*t.val+49)*((modulus b)^d*W) := Nat.le_mul_of_pos_right _ hv
    unfold constant
    nlinarith [hl.2.1,hl.2.2.1,hl.2.2.2]

end
end IntegerMultBounds.Machine.FlatCoordinateShiftFromDimensions