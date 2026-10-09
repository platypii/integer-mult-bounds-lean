import IntegerMultBounds.Machine.CompactComplexStopCompare

/-! Original global dimension and remaining exponent feed a fixed stop machine:
construct the threshold once, then read the actual runtime comparison flag.
All scalar words are retained. -/
namespace IntegerMultBounds.Machine.CompactComplexStopRun
noncomputable section
variable {q : ℕ}
open SharedPlacementAlphabet (setTape)

def exponent (es : List Bool) : Tapes 1 q :=
  ⟨fun _ => 1, fun _ => BinaryDescriptorStack.descriptor es⟩

def input (ds es : List Bool) : Tapes 10 q :=
  (FixedBasePowerUntil.input ds).append (exponent es)

def intermediate (B D : ℕ) (ds es : List Bool) : Tapes 10 q :=
  (CompactComplexStopThreshold.output B (Nat.clog B D) ds).append (exponent es)

def output (B D : ℕ) (ds es : List Bool) : Tapes 10 q :=
  setTape (intermediate B D ds es) (8 : Fin 10)
    (CompactComplexStopCompare.result es (FixedBasePowerUntil.counter (Nat.clog B D))) 0

def placement : Fin (3+7) ≃ Fin 10 :=
  ((Equiv.swap (0 : Fin 10) 9).trans (Equiv.swap 1 7)).trans (Equiv.swap 2 8)

def compare := Placement.placed (CompactComplexStopCompare.program (q := q)) placement

def program (B : ℕ) := seq (extend (CompactComplexStopThreshold.program (q := q) B) 1) compare

private theorem active (B D : ℕ) (ds es : List Bool) :
    Placement.active placement (intermediate (q := q) B D ds es) =
      BinaryDescriptorCompare.input es (FixedBasePowerUntil.counter (Nat.clog B D)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem replace (B D : ℕ) (ds es : List Bool) :
    Placement.replace placement (intermediate (q := q) B D ds es)
      (CompactComplexStopCompare.output es (FixedBasePowerUntil.counter (Nat.clog B D))) =
      output B D ds es := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (B D : ℕ) (hB : 2≤B) (hD : 0<D) (ds es : List Bool)
    (hd : Counter.value ds=D) (cd : GrowingCounterData.Canonical ds)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (program (q := q) B) (fun v => v=input ds es)
      (fun v => v=output B D ds es)
      ((FixedBasePowerUntil.constant B*B+2*B+7)*D+
        2*(es.length+(FixedBasePowerUntil.counter (Nat.clog B D)).length)+14) := by
  have ht := hoare_extend_eq (CompactComplexStopThreshold.constructs (q := q) B D hB hD ds hd cd)
    (exponent (q := q) es)
  have hc := Placement.hoare_at
    (CompactComplexStopCompare.runs_linear (q := q) es (FixedBasePowerUntil.counter (Nat.clog B D)) ce)
    placement (intermediate B D ds es) (active B D ds es)
  have hc' : HoareTime (compare (q := q)) (fun v => v=intermediate B D ds es)
      (fun v => v=output B D ds es)
      (2*(es.length+(FixedBasePowerUntil.counter (Nat.clog B D)).length)+13) := by
    apply hc.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨small,rfl,rfl⟩
    exact replace B D ds es
  exact (ht.seq hc').consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Original scalar words suffice for the complete physical comparison. -/
theorem runs_scalar (B D : ℕ) (hB : 2≤B) (hD : 0<D) (ds es : List Bool)
    (hd : Counter.value ds=D) (cd : GrowingCounterData.Canonical ds)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (program (q := q) B) (fun v => v=input ds es)
      (fun v => v=output B D ds es)
      ((FixedBasePowerUntil.constant B*B+2*B+27)*(D+Counter.value es+1)) := by
  have hr : Nat.clog B D ≤ D := Nat.clog_le_of_le_pow
    (show D ≤ B^D from (FixedBasePowerDescriptor.depth_le_power B D hB).trans' (by omega))
  have he := GrowingCounterData.canonical_width es ce
  have hel := Nat.log2_le_self (Counter.value es)
  have hc := GrowingCounterData.canonical_width (FixedBasePowerUntil.counter (Nat.clog B D))
    (FixedBasePowerUntil.counter_canonical (Nat.clog B D))
  rw [FixedBasePowerUntil.counter_value] at hc
  have hcl := Nat.log2_le_self (Nat.clog B D)
  exact (runs B D hB hD ds es hd cd ce).consequence (fun _ h => h) (fun _ h => h)
    (by
      let A := FixedBasePowerUntil.constant B*B+2*B+7
      change A*D+2*(es.length+(FixedBasePowerUntil.counter (Nat.clog B D)).length)+14 ≤
        (A+20)*(D+Counter.value es+1)
      have hx := Nat.mul_le_mul_left A (show D ≤ D+Counter.value es+1 by omega)
      calc
        _ ≤ A*D+2*(D+Counter.value es)+18 := by omega
        _ ≤ (A+20)*(D+Counter.value es+1) := by nlinarith only [hx,hD])

/-- One fixed actual-base machine for all original dimension/exponent words. -/
theorem runs_actual (D : ℕ) (hD : 0<D) (ds es : List Bool)
    (hd : Counter.value ds=D) (cd : GrowingCounterData.Canonical ds)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (program (q := q) CompactComplexStopThreshold.base) (fun v => v=input ds es)
      (fun v => v=output CompactComplexStopThreshold.base D ds es)
      ((FixedBasePowerUntil.constant CompactComplexStopThreshold.base*CompactComplexStopThreshold.base+
        2*CompactComplexStopThreshold.base+27)*(D+Counter.value es+1)) :=
  runs_scalar CompactComplexStopThreshold.base D CompactComplexStopThreshold.base_ge_two hD ds es hd cd ce

theorem flag_actual (D e : ℕ) (ds es : List Bool) (he : Counter.value es=e) :
    (output (q := q) CompactComplexStopThreshold.base D ds es).tape 8 0 =
      bitSymbol (Networks.ComplexRecursiveCallSchema.stopped D e) := by
  change CompactComplexStopCompare.result es
    (FixedBasePowerUntil.counter (CompactComplexStopThreshold.threshold D)) 0 = _
  exact CompactComplexStopCompare.flag_actual D e es he

end
end IntegerMultBounds.Machine.CompactComplexStopRun
