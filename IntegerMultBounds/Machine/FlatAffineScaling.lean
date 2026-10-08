import IntegerMultBounds.Machine.ActualAffineScalingStream
import IntegerMultBounds.Machine.FlatControlledShift

/-! Actual network scaling on a concrete row-major physical array. Each fiber
is extracted from the input itself; no address family is supplied. The exact
full-bank contract includes descriptor synthesis, counted streaming and sign. -/
namespace IntegerMultBounds.Machine.FlatAffineScaling

open Networks
open SignedScalingPrepared (Setup)
open SignedScalingDimensions (Scratch)
open ActualAffineScaling (modulus negative)

noncomputable section
variable {P B b : ℕ}

/-- The modular view of the actual finite array used by the stream. -/
def payload (a : Fin (P*(modulus b*B)) → Fin 4) (i : ℕ) (y : ZMod (modulus b)) : List (Fin 4) :=
  FlatControlledShift.payload a i y.val

@[simp] theorem payload_length (a : Fin (P*(modulus b*B)) → Fin 4) (i : ℕ) (y : ZMod (modulus b)) :
    (payload a i y).length = B := FlatControlledShift.payload_length a i y.val

/-- Splitting the actual physical word into stream fibers reproduces that word. -/
theorem source_eq (a : Fin (P*(modulus b*B)) → Fin 4) :
    (SignedScalingStream.fibers (modulus b) P (fun i y => payload a i (y : ZMod (modulus b)))).flatten = List.ofFn a := by
  have he : SignedScalingStream.fibers (modulus b) P (fun i y => payload a i (y : ZMod (modulus b))) =
      TranslationStream.fibers (modulus b) P (FlatControlledShift.payload a) := by
    unfold SignedScalingStream.fibers ScalingStream.fibers TranslationStream.fibers
    apply List.map_congr_left
    intro i hi
    unfold ScalingExecution.inputWord TranslationStream.blocks
    congr 1
    apply List.map_congr_left
    intro y hy
    have hyQ : y < modulus b := List.mem_range.mp hy
    let : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    simp only [payload,ZMod.val_natCast,Nat.mod_eq_of_lt hyQ]
  rw [he,FlatControlledShift.source_eq]

def input {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) :=
  ActualAffineScalingStream.input hr b P ns A D S source p middle s signMiddle t dest q (payload a)

def output {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) :=
  ActualAffineScalingStream.output hr b B P ns A D S source p middle s signMiddle t dest q (payload a)

/-- Physical source slot inside the actual descriptor-synthesis bank. -/
def sourceSlot (r : ℚ) : Fin (ActualAffineScalingStream.TapeCount r) :=
  Fin.castAdd 2 (Fin.castAdd 5 (Fin.castAdd (11+6) (Fin.castAdd 5
    (Fin.castAdd (ScalingPreparedExecution.TapeCount r.den)
      (Fin.natAdd (ScalingPreparedExecution.SynthesisTapes r.num.natAbs)
        (Fin.castAdd 2 (Fin.castAdd r.num.natAbs (0 : Fin 4))))))))

/-- The executing machine starts with exactly the supplied flat input word. -/
theorem source_tape {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) :
    (input hr a ns A D S source p middle s signMiddle t dest q).tape (sourceSlot r) =
      putWord source p (List.ofFn a) := by
  simp only [input,ActualAffineScalingStream.input,SignedScalingDimensionsStream.input,
    SignedScalingDimensions.input,sourceSlot,Tapes.append,Fin.addCases_left]
  change (((_ : Tapes (ScalingPreparedExecution.TapeCount r.num.natAbs) 0).append
    (_ : Tapes (ScalingPreparedExecution.TapeCount r.den) 0)).append (_ : Tapes 5 0)).tape _ = _
  simp only [Tapes.append,Fin.addCases_left]
  change ((_ : Tapes (ScalingPreparedExecution.SynthesisTapes r.num.natAbs) 0).append
    (((_ : Tapes 4 0).append (_ : Tapes r.num.natAbs 0)).append (_ : Tapes 2 0))).tape _ = _
  simp only [Tapes.append,Fin.addCases_left,Fin.addCases_right]
  change putWord (putWord source p
    (SignedScalingStream.fibers (modulus b) P (fun i y => payload a i (y : ZMod (modulus b)))).flatten)
      p (ScalingExecution.inputWord (modulus b) (fun _ => [])) = _
  simp [ScalingExecution.inputWord,source_eq,putWord]

/-- Prefix and suffix positions are unchanged; the target is multiplied by the
actual coefficient, including its sign and denominator. -/
theorem output_symbol {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (ns : List Bool)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (i : Fin P) (y : Fin (modulus b)) (j : Fin B) :
    (output hr a ns A D S source p middle s signMiddle t dest q).tape (ActualAffineScalingStream.destinationSlot r)
      (q+((i.val*(modulus b*B)+(Swap.Modular.ratMod (modulus b) r*(y.val : ZMod (modulus b))).val*B+j.val : ℕ) : ℤ)) =
      a (FiberLayoutData.index i y j) := by
  have hh := ActualAffineScalingStream.output_symbol hr b B P ns A D S source p middle s signMiddle t dest q
    (payload a) (payload_length a) i.val i.isLt (y.val : ZMod (modulus b)) j.val j.isLt
  let : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
  simpa only [output,payload,ZMod.val_natCast,Nat.mod_eq_of_lt y.isLt,FlatControlledShift.payload,
    dite_eq_left i.isLt,dite_eq_left y.isLt,List.getElem_ofFn,Fin.eta] using hh

/-- Full-bank execution and every physical symbol address, with synthesis
charged once. A nonempty prefix family absorbs setup into the whole volume. -/
theorem realizes_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (hB : 0 < B) (hP : 0 < P)
    (ns : List Bool) (hn : Counter.value ns = P) (cn : GrowingCounterData.Canonical ns)
    (A : Setup r.num.natAbs) (D : Setup r.den) (S : Scratch)
    (hA : A.Valid (modulus b) B) (hD : D.Valid (modulus b) B)
    (hS : negative r = true → ∀ z, S.origin ≤ z → z < S.origin+(((modulus b-1)*B : ℕ) : ℤ) → S.tape z = blank)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (s : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ)
    (hblank : ∀ z, s ≤ z → z < s+((modulus b*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative r = true → ∀ z, t ≤ z → z < t+((modulus b*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (ActualAffineScalingStream.program hr)
      (fun v => v = input hr a ns A D S source p middle s signMiddle t dest q)
      (fun v => v = output hr a ns A D S source p middle s signMiddle t dest q ∧
        ∀ (i : Fin P) (y : Fin (modulus b)) (j : Fin B),
        v.tape (ActualAffineScalingStream.destinationSlot r)
          (q+((i.val*(modulus b*B)+(Swap.Modular.ratMod (modulus b) r*(y.val : ZMod (modulus b))).val*B+j.val : ℕ) : ℤ)) =
          a (FiberLayoutData.index i y j))
      (ActualAffineScalingStream.nonemptyConstant r*(P*(modulus b*B))+249) := by
  apply (ActualAffineScalingStream.scaling_hoare_linear hr b B P hB hP ns hn cn A D S hA hD hS
    source p middle s signMiddle t dest q (payload a) (payload_length a) hblank hsblank).consequence
    (fun _ h => h) ?_ le_rfl
  rintro v rfl
  exact ⟨rfl,fun i y j => output_symbol hr a ns A D S source p middle s signMiddle t dest q i y j⟩

end
end IntegerMultBounds.Machine.FlatAffineScaling
